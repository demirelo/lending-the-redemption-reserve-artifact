"""Executable reference model of floor-anchored token credit on a stepped curve.

Exact integer arithmetic only. Prices are WAD-scaled integers (reserve units
per token unit, times WAD). Token and reserve amounts are integers.

The model implements the transition system of the paper (Section 3) with the
integer rounding rules of Proposition "Integer refinement". Switches re-introduce
the defects discussed in the paper ("mutants"), so that the test-suite can show
that each defect is detected.

State
    steps   list of [price, capacity], all capacities positive; steps[0] is the
            floor step, so Pf = p(0). Redeemed floor capacity is retired unless
            the floor step is the last step of the curve.
    S       total token supply
    A       reserve actually held
    gamma   current LTV policy (basis points), 0 < gamma <= gamma_cap
    bal     free (unlocked) token balance per account
    loans   per account: [locked tokens, debt]; a record exists only while
            both are positive
"""

WAD = 10**18
BPS = 10_000


class Revert(Exception):
    """A guard failed. Callers restore the previous state."""


def ceil_div(a, b):
    return -((-a) // b)


def is_int(*xs):
    return all(isinstance(x, int) and not isinstance(x, bool) for x in xs)


def acct(u):
    """Account identifiers are strings or integers; anything else is rejected."""
    if isinstance(u, bool) or not isinstance(u, (str, int)):
        raise Revert("bad account")
    return u


class DABC:
    def __init__(self, steps, gamma_cap_bps=9_000, gamma_bps=9_000,
                 fee_buy_bps=100, fee_sell_bps=100, fee_orig_bps=200,
                 lock_rounding="up", floor_guard=True, debt_cap="floor",
                 lift_cap=False):
        steps = [list(s) for s in steps]
        if not steps or not all(is_int(p, c) and p > 0 and c > 0 for p, c in steps):
            raise ValueError("steps must be non-empty with positive integer price and capacity")
        if any(steps[i][0] > steps[i + 1][0] for i in range(len(steps) - 1)):
            raise ValueError("prices must be non-decreasing")
        if not (is_int(gamma_cap_bps, gamma_bps) and 0 < gamma_bps <= gamma_cap_bps <= BPS):
            raise ValueError("need 0 < gamma <= gamma_cap <= 100%")
        if not (is_int(fee_buy_bps, fee_sell_bps, fee_orig_bps) and fee_buy_bps >= 0
                and 0 <= fee_sell_bps < BPS and 0 <= fee_orig_bps < BPS):
            raise ValueError("fees out of range")
        self.steps = steps
        self.S = 0
        self.A = 0
        self.bal = {}
        self.loans = {}
        self.gamma_cap_bps = gamma_cap_bps
        self.gamma_bps = gamma_bps
        self.fb, self.fs, self.fo = fee_buy_bps, fee_sell_bps, fee_orig_bps
        # mutant switches (the specification is the default of each)
        if lock_rounding not in ("up", "down") or debt_cap not in ("floor", "spot") \
                or not isinstance(floor_guard, bool) or not isinstance(lift_cap, bool):
            raise ValueError("unknown switch value")
        self.lock_rounding = lock_rounding      # "up" | "down" (public v1 harness)
        self.floor_guard = floor_guard          # True | False (v1 Definition 3.5)
        self.debt_cap = debt_cap                # "floor" | "spot"
        # optional extraction guard: no minted unit is repriced by more than kappa
        self.lift_cap = lift_cap

    # ------------------------------------------------------------------ views
    @property
    def Pf(self):
        return self.steps[0][0]

    @property
    def L(self):
        return sum(l for l, _ in self.loans.values())

    @property
    def D(self):
        return sum(d for _, d in self.loans.values())

    def capacity(self):
        return sum(c for _, c in self.steps)

    def rnum(self, x, steps=None):
        """WAD * R(x): exact numerator of the reserve function."""
        steps = self.steps if steps is None else steps
        tot, rem = 0, x
        for p, c in steps:
            if rem <= 0:
                break
            take = min(c, rem)
            tot += take * p
            rem -= take
        if rem > 0:
            raise Revert("supply above curve capacity")
        return tot

    def price_at(self, u, steps=None):
        """Price of the unit at position u (0-based); None beyond capacity."""
        steps = self.steps if steps is None else steps
        cum = 0
        for p, c in steps:
            cum += c
            if cum > u:
                return p
        return None

    def mint_price(self):
        return self.price_at(self.S)

    def surplus(self):
        """Reserve beyond what backs the curve: A + D - ceil(R(S))."""
        return self.A + self.D - ceil_div(self.rnum(self.S), WAD)

    def _normalise(self):
        # Retire redeemed floor capacity, but never the last step of the curve,
        # so that the capacity stays positive and Pf = p(0) is always defined.
        if len(self.steps) > 1 and self.S < self.steps[0][1]:
            self.steps[0][1] = self.S
            if self.S == 0:
                self.steps.pop(0)

    # ------------------------------------------------------------ transitions
    def buy(self, u, x):
        acct(u)
        if not (is_int(x) and x > 0) or self.S + x > self.capacity():
            raise Revert("buy size")
        cost = ceil_div(self.rnum(self.S + x) - self.rnum(self.S), WAD)   # round up
        fee = ceil_div(cost * self.fb, BPS)
        self.S += x
        self.A += cost + fee                                   # fee retained
        self.bal[u] = self.bal.get(u, 0) + x
        return cost + fee

    def sell(self, u, x):
        acct(u)
        if not (is_int(x) and 0 < x <= self.bal.get(u, 0)):
            raise Revert("sell size")
        num = self.rnum(self.S) - self.rnum(self.S - x)
        gross = num // WAD                                       # curve return, rounded down
        out = (num * (BPS - self.fs)) // (WAD * BPS)             # net proceeds, rounded once
        if out > self.A:
            raise Revert("INSUFFICIENT RESERVE")       # must be unreachable
        self.S -= x
        self.A -= out
        self.bal[u] -= x
        self._normalise()
        return out, gross

    def _ltv_ok(self, l, d):
        if self.debt_cap == "floor":
            cap_price = self.Pf
        else:                                          # mutant: value at spot
            cap_price = self.mint_price() or self.steps[-1][0]
        if self.lock_rounding == "up":
            # exact integer form of  d <= gamma * P * l
            return d * BPS * WAD <= self.gamma_bps * cap_price * l
        # mutant (public v1 harness): l >= floor(d * WAD * BPS / (gamma * P))
        return l >= (d * WAD * BPS) // (self.gamma_bps * cap_price)

    def required_lock(self, d):
        """Smallest lock for a total debt d under the active rounding rule."""
        price = self.Pf if self.debt_cap == "floor" else (self.mint_price() or self.steps[-1][0])
        num, den = d * WAD * BPS, self.gamma_bps * price
        return ceil_div(num, den) if self.lock_rounding == "up" else num // den

    def borrow(self, u, lock_add, b):
        """Origination, top-up (lock_add = 0), or added lock with new debt."""
        acct(u)
        l, d = self.loans.get(u, (0, 0))
        if not (is_int(lock_add, b) and b > 0 and 0 <= lock_add <= self.bal.get(u, 0)):
            raise Revert("borrow args")
        l2, d2 = l + lock_add, d + b
        if not self._ltv_ok(l2, d2):
            raise Revert("LTV")
        if b > self.A:
            raise Revert("INSUFFICIENT RESERVE")       # must be unreachable
        fee = ceil_div(b * self.fo, BPS)
        self.bal[u] = self.bal.get(u, 0) - lock_add
        self.loans[u] = [l2, d2]
        self.A -= b - fee                              # fee retained
        return b - fee

    def repay(self, u, r):
        acct(u)
        if u not in self.loans:
            raise Revert("no loan")
        l, d = self.loans[u]
        if not (is_int(r) and 0 < r <= d):
            raise Revert("repay size")
        self.A += r
        if r == d:                                     # full repayment releases everything
            self.bal[u] = self.bal.get(u, 0) + l
            del self.loans[u]
            return l
        unlock = (l * r) // d                          # round down
        self.bal[u] = self.bal.get(u, 0) + unlock
        self.loans[u] = [l - unlock, d - r]
        return unlock

    def close(self, u):
        """Collateral-netted close: repay in full from the proceeds of selling the lock."""
        acct(u)
        if u not in self.loans:
            raise Revert("no loan")
        l, d = self.loans[u]
        num = self.rnum(self.S) - self.rnum(self.S - l)
        out = (num * (BPS - self.fs)) // (WAD * BPS)             # net proceeds, rounded once
        if out < d:
            raise Revert("close not covered by proceeds")
        if out - d > self.A:
            raise Revert("INSUFFICIENT RESERVE")       # must be unreachable
        del self.loans[u]
        self.S -= l
        self.A -= out - d
        self._normalise()
        return out - d

    def accrue(self, u, delta):
        """Capped accrual: debt may grow only up to gamma_cap * Pf * lock."""
        acct(u)
        if u not in self.loans or not (is_int(delta) and delta > 0):
            raise Revert("accrue args")
        l, d = self.loans[u]
        if (d + delta) * BPS * WAD > self.gamma_cap_bps * self.Pf * l:
            raise Revert("accrual cap")
        self.loans[u] = [l, d + delta]

    def skim(self, w):
        if not (is_int(w) and 0 < w <= self.surplus()):
            raise Revert("skim amount")
        if w > self.A:
            raise Revert("INSUFFICIENT RESERVE")       # must be unreachable
        self.A -= w

    def set_gamma(self, g):
        if not (is_int(g) and 0 < g <= self.gamma_cap_bps):
            raise Revert("gamma")
        self.gamma_bps = g

    def donate(self, c):
        if not (is_int(c) and c > 0):
            raise Revert("donation")
        self.A += c

    def kappa_limit(self, price):
        """floor(price * (1+f_b)/(1-f_s))."""
        return (price * (BPS + self.fb)) // (BPS - self.fs)

    def raise_floor(self, c):
        """Exact water-filling of the minted range with budget c (level rounded down).

        Unminted capacity priced at or below the new floor is retired.
        """
        if not (is_int(c) and 0 < c <= self.surplus()) or self.S == 0:
            raise Revert("raise budget")
        Pf, S0 = self.steps[0][0], min(self.steps[0][1], self.S)
        budget = c * WAD                               # exact numerator, never rounded
        limit = self.kappa_limit(Pf) if self.lift_cap else None
        j, steps = 1, self.steps
        while True:
            target = steps[j][0] if j < len(steps) else None
            if limit is not None:
                target = limit if target is None else min(target, limit)
            if target is None or budget < (target - Pf) * S0:
                Pf += budget // S0                     # final level, rounded down
                break
            budget -= (target - Pf) * S0               # exact cost of this lift
            Pf = target
            if j >= len(steps) or target < steps[j][0]:
                break                                  # stopped at the lift cap
            S0 = min(S0 + steps[j][1], self.S)         # absorb step j; cap at S
            j += 1
        if Pf == self.steps[0][0]:
            raise Revert("raise has no effect")        # budget too small, or the cap is reached
        self._install([[Pf, S0]] + [list(s) for s in steps[j:]], inject=0)

    def reconfigure(self, new_steps, inject=0):
        try:
            new = [list(s) for s in new_steps]
        except TypeError:
            raise Revert("bad schedule")
        self._install(new, inject)

    def _install(self, new, inject):
        if not new or not is_int(inject) or inject < 0:
            raise Revert("bad reshape")
        if not all(len(s) == 2 and is_int(*s) and s[0] > 0 and s[1] > 0 for s in new):
            raise Revert("bad step")
        if any(new[i][0] > new[i + 1][0] for i in range(len(new) - 1)):
            raise Revert("not monotone")
        if sum(c for _, c in new) < self.S:
            raise Revert("capacity below supply")
        if self.floor_guard and new[0][0] < self.Pf:
            raise Revert("FLOOR DECREASE")                         # (G1)
        if self.rnum(self.S, new) > (self.A + inject + self.D) * WAD:
            raise Revert("UNDERFUNDED")                            # (G2)
        if self.lift_cap:
            # no minted unit may be repriced upward by more than kappa
            u = 0
            while u < self.S:
                old_p, new_p = self.price_at(u), self.price_at(u, new)
                if new_p > self.kappa_limit(old_p):
                    raise Revert("LIFT CAP")
                # jump to the next breakpoint of either schedule
                nxt, cum = self.S, 0
                for sched in (self.steps, new):
                    cum = 0
                    for _, c in sched:
                        cum += c
                        if cum > u:
                            nxt = min(nxt, cum)
                            break
                u = nxt
        self.A += inject
        self.steps = new                               # floor capacity is retired only on redemptions

    # ------------------------------------------------------------- invariants
    def check(self):
        """Return the list of violated properties (empty list = state is safe)."""
        bad = []
        L, D = self.L, self.D
        ok_dom = (is_int(self.S, self.A) and self.S >= 0 and self.A >= 0
                  and 0 < self.gamma_bps <= self.gamma_cap_bps <= BPS
                  and all(is_int(v) and v >= 0 for v in self.bal.values())
                  and all(is_int(l, d) and l >= 0 and d > 0 for l, d in self.loans.values())
                  and all(p > 0 and c > 0 for p, c in self.steps)
                  and all(self.steps[i][0] <= self.steps[i + 1][0]
                          for i in range(len(self.steps) - 1))
                  and self.capacity() >= self.S and self.capacity() > 0)
        if not ok_dom:
            bad.append("state domain")
        if sum(self.bal.values()) + L != self.S:
            bad.append("J1 custody")
        if any(d * BPS * WAD > self.gamma_cap_bps * self.Pf * l for l, d in self.loans.values()):
            bad.append("J2 loan cover")
        if (self.A + D) * WAD < self.rnum(self.S):
            bad.append("J3 reserve adequacy")
        # coverage with slack:  A >= [R(S) - R(L)] + (1 - gamma_cap) R(L)
        if BPS * self.A * WAD < BPS * self.rnum(self.S) - self.gamma_cap_bps * self.rnum(L):
            bad.append("coverage")
        return bad
