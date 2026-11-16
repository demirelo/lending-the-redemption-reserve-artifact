#!/usr/bin/env python3
"""Exact finite checks for the credit-capacity extension.

Run from any directory with Python 3; no external packages or network are used.
All safety calculations use Fraction.  A square root is used only to display
the decimal approximation of the explicitly bracketed nonlinear release.
This is a finite checker, not a formal proof or a production lending engine.
"""

from dataclasses import dataclass
from fractions import Fraction as F
from itertools import combinations_with_replacement, product
from math import isqrt, lcm, sqrt
from random import Random


@dataclass(frozen=True)
class Piece:
    end: F
    intercept: F
    slope: F


class Curve:
    """Right-continuous nondecreasing affine prices on rational intervals."""

    def __init__(self, name, pieces):
        self.name = name
        self.pieces = tuple(Piece(*(F(x) for x in item)) for item in pieces)
        if not self.pieces:
            raise ValueError("A curve needs at least one piece")
        start = F(0)
        previous_left_price = None
        for piece in self.pieces:
            if piece.end <= start or piece.slope < 0:
                raise ValueError("Invalid interval or negative slope")
            right_price = piece.intercept + piece.slope * start
            if right_price <= 0:
                raise ValueError("Non-positive price")
            if previous_left_price is not None and right_price < previous_left_price:
                raise ValueError("Downward price jump")
            previous_left_price = piece.intercept + piece.slope * piece.end
            start = piece.end
        self.capacity = self.pieces[-1].end

    def reserve(self, quantity):
        quantity = F(quantity)
        if not 0 <= quantity <= self.capacity:
            raise ValueError("Supply outside curve domain")
        start = F(0)
        total = F(0)
        for piece in self.pieces:
            end = min(quantity, piece.end)
            if end > start:
                total += piece.intercept * (end - start)
                total += piece.slope * (end * end - start * start) / 2
            if quantity <= piece.end:
                break
            start = piece.end
        return total


@dataclass(frozen=True)
class Loan:
    lock: F
    debt: F

    def __post_init__(self):
        object.__setattr__(self, "lock", F(self.lock))
        object.__setattr__(self, "debt", F(self.debt))
        if self.lock <= 0 or self.debt <= 0:
            raise ValueError("Initial locks and debts must be positive")

    @property
    def ratio(self):
        return self.debt / self.lock


@dataclass(frozen=True)
class Buffer:
    required: F
    depth: F
    residual_locks: tuple
    candidates: int


def proportional_buffer(curve, loans):
    """Sort ratios and scan the merged loan/price intervals exactly."""
    if not loans:
        return Buffer(F(0), F(0), (), 1)
    order = sorted(range(len(loans)), key=lambda i: loans[i].ratio, reverse=True)
    total_lock = sum((loan.lock for loan in loans), F(0))
    if total_lock > curve.capacity:
        raise ValueError("Locks exceed curve capacity")
    ends = []
    acc = F(0)
    for i in order:
        acc += loans[i].lock
        ends.append(acc)

    left = F(0)
    h_left = F(0)
    r_left = F(0)
    best = F(0)
    best_depth = F(0)
    candidate_count = 0
    loan_piece = 0
    price_piece = 0
    while left < total_lock:
        a = loans[order[loan_piece]].ratio
        piece = curve.pieces[price_piece]
        right = min(ends[loan_piece], piece.end, total_lock)
        assert right > left
        candidates = {left, right}
        if piece.slope > 0:
            stationary = (a - piece.intercept) / piece.slope
            if left <= stationary <= right:
                candidates.add(stationary)
        for q in sorted(candidates):
            h = h_left + a * (q - left)
            r = r_left + piece.intercept * (q - left)
            r += piece.slope * (q * q - left * left) / 2
            value = h - r
            candidate_count += 1
            if value > best:
                best, best_depth = value, q
        h_left += a * (right - left)
        r_left += piece.intercept * (right - left)
        r_left += piece.slope * (right * right - left * left) / 2
        left = right
        if left == ends[loan_piece]:
            loan_piece += 1
        if left == piece.end:
            price_piece += 1

    remaining = best_depth
    residual = [F(0)] * len(loans)
    for i in order:
        residual[i] = min(loans[i].lock, remaining)
        remaining -= residual[i]
    assert remaining == 0
    # The returned allocation is checked by direct reserve evaluation, not
    # by the local interval expressions used to choose the maximum.
    direct_debt = sum((loans[i].ratio * residual[i] for i in range(len(loans))), F(0))
    assert direct_debt - curve.reserve(best_depth) == best
    return Buffer(best, best_depth, tuple(residual), candidate_count)


def residual_grid_oracle(curve, loans, denominator=4):
    """Enumerate every residual vector on a rational grid, without sorting.

    A common integer scale avoids Fraction arithmetic inside the product loop.
    The fixture generator ensures that all continuous maxima occur on this
    grid.  That property is NOT claimed for arbitrary curves or inputs.
    """
    capacities = []
    for loan in loans:
        units = loan.lock * denominator
        if units.denominator != 1:
            raise ValueError("Grid does not contain initial lock")
        capacities.append(int(units))
    total_units = sum(capacities)
    reserves = [curve.reserve(F(q, denominator)) for q in range(total_units + 1)]
    debt_per_unit = [loan.ratio / denominator for loan in loans]
    scale = 1
    for value in reserves + debt_per_unit:
        scale = lcm(scale, value.denominator)
    r_scaled = [int(value * scale) for value in reserves]
    a_scaled = [int(value * scale) for value in debt_per_unit]
    best_scaled = 0
    best_state = (0,) * len(loans)
    count = 0
    for state in product(*(range(cap + 1) for cap in capacities)):
        debt = sum(a * x for a, x in zip(a_scaled, state))
        value = debt - r_scaled[sum(state)]
        count += 1
        if value > best_scaled:
            best_scaled, best_state = value, state
    return F(best_scaled, scale), tuple(F(x, denominator) for x in best_state), count


def cash_after_free_exit(curve, supply, loans, initial_cash, residual_pairs):
    """Repay to the supplied pairs, then redeem every free token at gross."""
    supply, initial_cash = F(supply), F(initial_cash)
    if len(loans) != len(residual_pairs):
        raise ValueError("Residual vector has wrong length")
    remaining_lock = F(0)
    repayments = F(0)
    for loan, (q, b) in zip(loans, residual_pairs):
        q, b = F(q), F(b)
        if not (0 <= q <= loan.lock and 0 <= b <= loan.debt):
            raise ValueError("Residual pair outside initial amounts")
        remaining_lock += q
        repayments += loan.debt - b
    gross_redemption = curve.reserve(supply) - curve.reserve(remaining_lock)
    return initial_cash + repayments - gross_redemption


def whole_position_buffer(curve, loans):
    best = F(0)
    witness = 0
    for mask in range(1 << len(loans)):
        lock = sum((loan.lock for i, loan in enumerate(loans) if mask >> i & 1), F(0))
        debt = sum((loan.debt for i, loan in enumerate(loans) if mask >> i & 1), F(0))
        deficit = debt - curve.reserve(lock)
        if deficit > best:
            best, witness = deficit, mask
    return best, witness


def whole_position_dp(curve, loans):
    if any(loan.lock.denominator != 1 for loan in loans):
        raise ValueError("DP requires integer collateral")
    total = int(sum((loan.lock for loan in loans), F(0)))
    best_debt = [None] * (total + 1)
    best_debt[0] = F(0)
    for loan in loans:
        weight = int(loan.lock)
        for quantity in range(total, weight - 1, -1):
            previous = best_debt[quantity - weight]
            if previous is None:
                continue
            value = previous + loan.debt
            if best_debt[quantity] is None or value > best_debt[quantity]:
                best_debt[quantity] = value
    return max(
        debt - curve.reserve(F(quantity))
        for quantity, debt in enumerate(best_debt)
        if debt is not None
    )


def partition_bitset(weights):
    """Independent integer subset-sum decision, without debt or reserve data."""
    total = sum(weights)
    if total % 2:
        return False
    reachable = 1
    for weight in weights:
        reachable |= reachable << weight
    return bool((reachable >> (total // 2)) & 1)


def rational_sqrt(value):
    value = F(value)
    numerator = isqrt(value.numerator)
    denominator = isqrt(value.denominator)
    if numerator * numerator != value.numerator or denominator * denominator != value.denominator:
        raise ValueError("Not a rational square")
    return F(numerator, denominator)


def fixtures():
    return (
        Curve("flat", [(16, 1, 0)]),
        Curve("linear", [(16, 1, 1)]),
        Curve("stepped", [(1, 1, 0), (3, 2, 0), (16, 3, 0)]),
        Curve("continuous_kinks", [(1, 1, 1), (3, F(3, 2), F(1, 2)), (16, 0, 1)]),
        Curve("affine_with_jump", [(2, 1, F(1, 2)), (16, F(5, 2), F(1, 4))]),
    )


def examples():
    curve = Curve("linear_example", [(16, 1, 1)])
    empty = proportional_buffer(curve, [])
    assert (empty.required, empty.depth, empty.residual_locks) == (F(0), F(0), ())
    one = [Loan(1, F(3, 2))]
    concentrated = [Loan(F(1, 2), 1), Loan(F(1, 2), F(1, 2))]
    uniform = proportional_buffer(curve, one)
    unequal = proportional_buffer(curve, concentrated)
    assert (uniform.required, uniform.depth) == (F(1, 8), F(1, 2))
    assert (unequal.required, unequal.depth) == (F(3, 8), F(1, 2))
    shortfall = cash_after_free_exit(curve, 1, one, 0, [(F(1, 2), F(3, 4))])
    assert shortfall == -F(1, 8)
    safe_cash = cash_after_free_exit(curve, 1, one, F(1, 8), [(F(1, 2), F(3, 4))])
    assert safe_cash == 0

    # The remaining nonlinear lock solves R(q)=3/4.  Certify a rational
    # interval for it; sqrt is used solely for the printed decimal.
    lower = F(581138830084, 10**12)
    upper = lower + F(1, 10**12)
    assert curve.reserve(lower) < F(3, 4) < curve.reserve(upper)
    released_decimal = 2 - sqrt(2.5)
    pool_gain = curve.reserve(2) - 2 * curve.reserve(1)
    assert pool_gain == 1

    print("CF01 exact examples")
    print(f"  uniform buffer={uniform.required}; stress depth={uniform.depth}")
    print(f"  concentrated buffer={unequal.required}; stress depth={unequal.depth}")
    print(f"  proportional half-release cash without buffer={shortfall}")
    print(f"  same release cash with committed buffer={safe_cash}")
    print(f"  nonlinear remaining lock is in [{lower}, {upper}]")
    print(f"  nonlinear released tokens (display only)={released_decimal:.12f}")
    print(f"  capacity gain from merging two one-token locks={pool_gain}")


def grid_checks():
    rng = Random(902711)
    curves = fixtures()
    cases = 0
    states = 0
    candidates = 0
    zero_buffer_cases = 0
    for curve in curves:
        for _ in range(48):
            n = rng.randint(1, 4)
            loans = [Loan(lock, F(rng.randint(1, 20), 4) * lock)
                     for lock in (rng.randint(1, 2) for _ in range(n))]
            result = proportional_buffer(curve, loans)
            oracle, _, count = residual_grid_oracle(curve, loans)
            assert result.required == oracle, (curve.name, loans, result, oracle)
            # These fixtures deliberately include every analytic candidate on
            # the quarter-token grid; an arbitrary coarse grid is not enough.
            assert (result.depth * 4).denominator == 1
            total_lock = sum((loan.lock for loan in loans), F(0))
            total_debt = sum((loan.debt for loan in loans), F(0))
            supply = total_lock + 1
            initial_cash = curve.reserve(supply) - total_debt + result.required
            residual_pairs = [(q, loan.ratio * q) for q, loan in zip(result.residual_locks, loans)]
            assert initial_cash >= 0
            cash = cash_after_free_exit(curve, supply, loans, initial_cash, residual_pairs)
            assert cash == 0
            equal = [Loan(loan.lock, total_debt * loan.lock / total_lock) for loan in loans]
            equal_requirement = proportional_buffer(curve, equal).required
            assert equal_requirement <= result.required
            floor = curve.pieces[0].intercept
            assert (result.required == 0) == all(loan.ratio <= floor for loan in loans)
            zero_buffer_cases += result.required == 0
            cases += 1
            states += count
            candidates += result.candidates
    print("CF02 sorted envelope versus exhaustive rational residual states")
    print(f"  curves={len(curves)}; books={cases}; residual states={states}")
    print(f"  exact interval candidates={candidates}; zero-buffer books={zero_buffer_cases}")
    print("  mismatches=0; equal-ratio weak-minimum checks passed")


def capacity_checks():
    cases = 0
    curve = Curve("capacity_example", [(32, 1, 1)])
    for total_lock in (F(1), F(2), F(3), F(4)):
        for reserve in (F(0), F(1, 32), F(1, 8), F(1, 2), F(2), F(8)):
            if reserve == 0:
                ratio = F(1)
            elif reserve <= total_lock * total_lock / 2:
                ratio = 1 + rational_sqrt(2 * reserve)
            else:
                ratio = 1 + total_lock / 2 + reserve / total_lock
            debt = total_lock * ratio
            result = proportional_buffer(curve, [Loan(total_lock, debt)])
            assert result.required == reserve
            increased = proportional_buffer(curve, [Loan(total_lock, debt + F(1, 100))])
            assert increased.required > reserve
            cases += 1
    print("CF03 aggregate capacity")
    print(f"  closed-form boundary cases={cases}; all feasible")
    print("  increasing aggregate debt by 1/100 violates the buffer in every case")


def nonlinear_checks():
    rng = Random(161803)
    cases = 0
    close_count = 0
    curve = Curve("nonlinear_example", [(32, 1, 1)])
    for cap in (F(2, 3), F(9, 10), F(1)):
        for _ in range(48):
            locks = [F(rng.randint(1, 3)) for _ in range(rng.randint(1, 4))]
            loans = [Loan(lock, cap * curve.reserve(lock)) for lock in locks]
            residual_pairs = []
            for lock in locks:
                remaining = F(rng.randint(0, int(lock * 4)), 4)
                residual_pairs.append((remaining, cap * curve.reserve(remaining)))
            supply = sum(locks, F(0)) + 1
            debt = sum((loan.debt for loan in loans), F(0))
            initial_cash = curve.reserve(supply) - debt
            cash = cash_after_free_exit(curve, supply, loans, initial_cash, residual_pairs)
            remaining_lock = sum((q for q, _ in residual_pairs), F(0))
            remaining_debt = sum((b for _, b in residual_pairs), F(0))
            assert cash == curve.reserve(remaining_lock) - remaining_debt >= 0
            for loan, (q, b) in zip(loans, residual_pairs):
                repayment = loan.debt - b
                release = loan.lock - q
                assert release <= loan.lock * repayment / loan.debt
            # Close remaining loans in a shuffled order.  Fees at rate 1-cap
            # are paid to an outside recipient, so the issuer funds the full
            # gross curve return less the internally netted repayment.
            close_order = list(residual_pairs)
            rng.shuffle(close_order)
            close_supply = remaining_lock
            close_cash = cash
            for q, b in close_order:
                if q == 0:
                    assert b == 0
                    continue
                gross = curve.reserve(close_supply) - curve.reserve(close_supply - q)
                assert cap * gross - b >= 0
                close_cash += b - gross
                close_supply -= q
                assert close_cash >= 0
                close_count += 1
            assert close_supply == 0 and close_cash == 0
            cases += 1
    print("CF04 nonlinear collateral release")
    print(f"  exact residual-path cases={cases}; cash shortfalls=0")
    print(f"  release bounds passed; atomic netted closes={close_count}; shortfalls=0")


def partition_checks():
    cases = 0
    yes_cases = 0
    checked_subsets = 0
    for n in range(1, 6):
        for weights in combinations_with_replacement(range(1, 6), n):
            total = sum(weights)
            if total % 2:
                continue
            b = total // 2
            curve = Curve("partition", [(total + 1, 1, 1)])
            loans = [Loan(weight, (1 + b) * weight) for weight in weights]
            reserve = F(b * b, 2) - F(1, 4)
            required, mask = whole_position_buffer(curve, loans)
            dynamic_program = whole_position_dp(curve, loans)
            partition = partition_bitset(weights)
            assert required == dynamic_program
            assert (required > reserve) == partition
            assert sum((loan.debt for loan in loans), F(0)) == curve.reserve(total)
            # Initial all-locked cash is the committed reserve.  Retain the
            # maximizing subset, repay its complement, and calculate payouts.
            residual_pairs = [(loan.lock, loan.debt) if mask >> i & 1 else (F(0), F(0))
                              for i, loan in enumerate(loans)]
            cash = cash_after_free_exit(curve, total, loans, reserve, residual_pairs)
            assert cash == reserve - required
            if partition:
                assert cash == -F(1, 4)
            else:
                assert cash >= F(1, 4)
            # Reachability: lock all positions at floor debt first, then top up.
            running_debt = F(total)
            available = curve.reserve(total) - running_debt + reserve
            for weight in weights:
                topup = b * weight
                assert topup <= available
                available -= topup
                running_debt += topup
                assert running_debt <= curve.reserve(total)
                assert available >= reserve
            assert available == reserve
            cases += 1
            yes_cases += partition
            checked_subsets += 1 << n
    print("CF05 whole-position subset coverage and PARTITION reduction")
    print(f"  integer books={cases}; subsets enumerated={checked_subsets}")
    print(f"  PARTITION yes cases={yes_cases}; no cases={cases - yes_cases}")
    print("  subset enumeration / integer DP / independent subset-sum mismatches=0")
    print("  all constructed books reachable through immediately covered states")


def mutation_checks():
    curve = Curve("linear_mutation", [(16, 1, 1)])
    one = [Loan(1, F(3, 2))]
    failures = []

    # Wrong guard 1: current aggregate coverage ignores future partial release.
    assert one[0].debt <= curve.reserve(one[0].lock)
    cash = cash_after_free_exit(curve, 1, one, 0, [(F(1, 2), F(3, 4))])
    assert cash == -F(1, 8)
    failures.append(("current aggregate coverage only", -cash))

    # Wrong guard 2: use average leverage instead of the actual ratio envelope.
    concentrated = [Loan(F(1, 2), 1), Loan(F(1, 2), F(1, 2))]
    proxy = proportional_buffer(curve, one).required
    cash = cash_after_free_exit(curve, 1, concentrated, proxy, [(F(1, 2), 1), (0, 0)])
    assert cash == -F(1, 4)
    failures.append(("average-ratio buffer proxy", -cash))

    # Wrong guard 3: permit the committed reserve to be skimmed as surplus.
    buffer = proportional_buffer(curve, one).required
    initial_cash = buffer
    skim = buffer
    assert skim <= initial_cash  # The skim itself is payable.
    cash = cash_after_free_exit(curve, 1, one, initial_cash - skim, [(F(1, 2), F(3, 4))])
    assert cash == -F(1, 8)
    failures.append(("skim the committed reserve", -cash))

    # Wrong guard 4: preserve only floor and total funding after premium credit.
    changed = Curve("changed_step", [(1, 1, 0), (16, 3, 0)])
    supply = F(2)
    initial_cash = curve.reserve(supply) - one[0].debt
    assert changed.pieces[0].intercept == curve.pieces[0].intercept
    assert changed.reserve(supply) == curve.reserve(supply)
    cash = cash_after_free_exit(changed, supply, one, initial_cash, [(1, F(3, 2))])
    assert cash == -F(1, 2)
    failures.append(("old reshape guards with new debt anchor", -cash))

    print("CF06 directed unsafe mutations")
    for name, shortfall in failures:
        print(f"  detected: {name}; exact cash shortfall={shortfall}")
    print(f"  mutations detected={len(failures)} / {len(failures)}")


def main():
    print("Credit capacity and collateral release: exact finite checks")
    print("Arithmetic: Fraction; deterministic seeds; no external packages")
    examples()
    grid_checks()
    capacity_checks()
    nonlinear_checks()
    partition_checks()
    mutation_checks()
    print("PASS: all stated finite checks completed")
    print("Status: analytic results are not Lean-verified; no production-contract claim")


if __name__ == "__main__":
    main()
