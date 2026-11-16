"""Randomized stateful tests of the reference model.

Usage:  python3 -I scripts/test_model.py [episodes] [steps]

1. SPEC runs: random operation sequences on the specified mechanism. After
   every executed operation all invariants must hold; no sale, loan, close or
   skim may be refused for lack of reserve; no floor raise within the surplus
   may be refused for lack of funding; and every floor raise must reach the
   level computed by an independent exact water-filling calculation.
2. MUTANT runs (negative tests): each re-introduces one defect. The suite must
   observe a violation for every mutant, otherwise it exits non-zero.
3. Property tests: sandwich profit bound, mint-reshape-redeem with and without
   the lift cap.
"""
import copy
import random
import sys
from fractions import Fraction as F

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from dabc_model import DABC, Revert, WAD, BPS  # noqa: E402


def random_curve(rng):
    """Floor step plus 1-3 sloped segments, with prices that are not round."""
    pf = rng.choice([WAD, 2 * WAD, WAD // 3 + 1, 7 * WAD // 5, 10**6, 3 * 10**17 + 7])
    steps = [[pf, rng.randint(1, 5000)]]
    p = pf
    for _ in range(rng.randint(1, 3)):
        dp = rng.choice([0, 1, pf // 97 + 1, pf // 10 + 3, pf // 2])
        q = rng.randint(1, 3000)
        for _ in range(rng.randint(1, 6)):
            p += dp + rng.choice([0, 0, 1])
            steps.append([p, q])
    return steps


def random_reconfig(rng, m):
    """A candidate schedule: reshapes steps, may try to move the floor."""
    new = [list(s) for s in m.steps]
    kind = rng.randint(0, 3)
    if kind == 0 and len(new) > 2:            # shift value between two steps
        i = rng.randint(1, len(new) - 2)
        delta = rng.randint(1, max(1, new[i][0] // 20))
        new[i][0] -= delta
        new[i + 1][0] += delta
    elif kind == 1:                           # try to lower the floor
        new[0][0] -= rng.randint(1, max(1, new[0][0] // 5))
        if len(new) > 1:
            new[-1][0] += rng.randint(0, new[-1][0] // 5)
    elif kind == 2:                           # reprice the tail upward
        for s in new[1:]:
            s[0] += rng.randint(0, s[0] // 10)
        new[1:] = sorted(new[1:])
    else:                                     # flatten everything to one price
        avg = m.rnum(m.S) // max(m.S, 1)
        new = [[max(avg, 1), max(m.capacity(), 1)]]
    return new


def exact_fill_level(steps, S, c):
    """Independent water-filling: floor of the level y with K(y) = c, in WAD units.

    K(y) = sum over minted units of (y - p)^+ . Uses rationals, no model code.
    """
    units, rem = [], S                        # (price, minted amount), ascending
    for p, cap in steps:
        if rem <= 0:
            break
        take = min(cap, rem)
        if take:
            units.append((p, take))
        rem -= take
    budget, level, below = F(c * WAD), F(units[0][0]), 0
    i = 0
    while True:
        while i < len(units) and units[i][0] <= level:
            below += units[i][1]
            i += 1
        nxt = units[i][0] if i < len(units) else None
        if nxt is None or budget < (nxt - level) * below:
            return int(level + budget / below)   # floor, values are positive
        budget -= (nxt - level) * below
        level = F(nxt)


def cap_price(m):
    """Price at which the active borrowing rule values a locked token."""
    return m.Pf if m.debt_cap == "floor" else (m.mint_price() or m.steps[-1][0])


def episode(rng, steps, **mutant):
    """Run one random sequence; return (set of violated properties, executed ops)."""
    cap = rng.choice([5000, 8000, 9000, 9900, 10000])
    m = DABC(random_curve(rng), gamma_cap_bps=cap, gamma_bps=rng.randint(1, cap),
             fee_buy_bps=rng.choice([0, 30, 100, 300]),
             fee_sell_bps=rng.choice([0, 30, 100, 750]),
             fee_orig_bps=rng.choice([0, 100, 300]), **mutant)
    users, ops, floor_hwm, kinds = list(range(5)), 0, m.Pf, set()
    menu = (["buy"] * 4 + ["sell"] * 3 + ["borrow"] * 4 + ["topup"] * 2 + ["repay"] * 2
            + ["close", "accrue", "skim"] + ["raise"] * 2 + ["reconf", "gamma", "donate"])
    for _ in range(steps):
        u = rng.choice(users)
        snap = copy.deepcopy(m.__dict__)
        op = rng.choice(menu)
        pre_surplus, pre_pf = m.surplus(), m.Pf
        try:
            if op == "buy":
                room = m.capacity() - m.S
                m.buy(u, rng.randint(1, max(1, room // rng.choice([1, 3, 20]))))
            elif op == "sell":
                b = m.bal.get(u, 0)
                x = rng.choice([b, rng.randint(1, max(1, b))])
                out, gross = m.sell(u, x)
                # integer floor guarantee: gross >= floor(Pf * x)
                if gross < (pre_pf * x) // WAD:
                    kinds.add("sell below floor")
            elif op == "borrow":
                b = m.bal.get(u, 0)
                l, d = m.loans.get(u, (0, 0))
                if rng.random() < 0.5:        # ask for an amount; lock what is required
                    lock = rng.randint(1, max(1, b))
                    amt = rng.randint(1, max(1, m.gamma_bps * cap_price(m) * lock // (BPS * WAD) + 2))
                    m.borrow(u, max(0, m.required_lock(d + amt) - l), amt)
                else:                          # offer a lock; borrow up to the limit
                    lock = rng.randint(1, max(1, b))
                    mx = m.gamma_bps * cap_price(m) * (l + lock) // (BPS * WAD) - d
                    m.borrow(u, lock, rng.randint(1, max(1, mx + 1)))
            elif op == "topup":
                l, d = m.loans.get(u, (0, 0))
                mx = m.gamma_bps * cap_price(m) * l // (BPS * WAD) - d
                m.borrow(u, 0, rng.randint(1, max(1, mx + 1)))
            elif op == "repay":
                d = m.loans.get(u, (0, 0))[1]
                l0 = m.loans.get(u, (0, 0))[0]
                r = rng.choice([d, rng.randint(1, max(1, d))])
                got = m.repay(u, r)
                if r == d and got != l0:
                    kinds.add("full repayment did not release the lock")
            elif op == "close":
                try:
                    m.close(u)
                except Revert as e:
                    # under gamma_cap + f_s <= 1 a close can never be refused for lack of proceeds
                    if "not covered" in str(e) and m.gamma_cap_bps + m.fs <= BPS \
                            and m.lock_rounding == "up" and m.floor_guard and m.debt_cap == "floor":
                        kinds.add("close refused under the parameter rule")
                    raise
            elif op == "accrue":
                l, d = m.loans.get(u, (0, 0))
                room = m.gamma_cap_bps * m.Pf * l // (BPS * WAD) - d
                m.accrue(u, rng.randint(1, max(1, room + 1)))
            elif op == "skim":
                s = m.surplus()
                m.skim(rng.choice([s, rng.randint(1, max(1, s))]))
            elif op == "raise":
                s = m.surplus()
                c = rng.choice([s, rng.randint(1, max(1, s))])
                expect = exact_fill_level(m.steps, m.S, c) if 0 < c <= s and m.S > 0 else None
                if m.lift_cap and expect is not None:       # constrained level
                    expect = min(expect, m.kappa_limit(m.Pf))
                m.raise_floor(c)
                used = pre_surplus - m.surplus()
                if not 0 <= used <= c:
                    kinds.add("raise used more than budget")
                if m.Pf != expect:
                    kinds.add("raise level differs from exact water-filling")
            elif op == "reconf":
                m.reconfigure(random_reconfig(rng, m), inject=rng.choice([0, 0, rng.randint(0, 50)]))
            elif op == "gamma":
                m.set_gamma(rng.randint(1, m.gamma_cap_bps))
            else:
                m.donate(rng.randint(1, 1000))
            ops += 1
        except Revert as e:
            m.__dict__.update(snap)
            if "INSUFFICIENT RESERVE" in str(e):
                kinds.add("liquidity refusal (" + op + ")")
            if op == "raise" and "UNDERFUNDED" in str(e):
                kinds.add("raise underfunded")
            continue
        kinds.update(m.check())
        if m.Pf < floor_hwm:
            kinds.add("floor decreased")
        floor_hwm = max(floor_hwm, m.Pf)
    return kinds, ops


def run(name, episodes, steps, seed, **mutant):
    rng = random.Random(seed)
    fails, total_ops, tally = 0, 0, {}
    for _ in range(episodes):
        kinds, ops = episode(rng, steps, **mutant)
        total_ops += ops
        fails += bool(kinds)
        for k in kinds:
            tally[k] = tally.get(k, 0) + 1
    print(f"{name:26s} episodes={episodes:6d} executed_ops={total_ops:9d} "
          f"failing_episodes={fails:6d}  {dict(sorted(tally.items())) if tally else ''}")
    return fails


def reshape_property(episodes, seed, cap):
    """Mint a, reshape upward with the whole surplus, redeem a. Profit must be <= 0 with the cap.

    The reshape is either a floor raise or a reconfiguration to a flat schedule
    at the highest funded price, so both entry points are exercised.
    """
    rng = random.Random(seed)
    trials = wins = worst = rejected = 0
    for _ in range(episodes):
        fb, fs = rng.choice([(0, 0), (30, 30), (100, 100), (300, 300), (100, 750)])
        m = DABC(random_curve(rng), fee_buy_bps=fb, fee_sell_bps=fs, lift_cap=cap)
        try:
            m.buy("h", rng.randint(1, m.capacity() - 1))
            if rng.random() < 0.6:               # push the market back toward the floor
                m.sell("h", rng.randint(1, m.bal["h"]))
            m.donate(rng.randint(1, 1 + m.rnum(m.S) // WAD))
            paid = m.buy("att", rng.randint(1, max(1, (m.capacity() - m.S) // rng.choice([1, 2, 10]))))
        except Revert:
            continue
        trials += 1
        try:
            if rng.random() < 0.5:
                m.raise_floor(m.surplus())
            else:
                m.reconfigure([[(m.A + m.D) * WAD // m.S, m.capacity()]])
        except Revert:
            rejected += 1                        # the reshape itself is refused
            continue
        got, _ = m.sell("att", m.bal["att"])
        if m.check():
            return None
        if got > paid:
            wins += 1
            worst = max(worst, got - paid)
    return trials, rejected, wins, worst


def sandwich_bound(episodes, seed):
    """profit <= a * [(1-fs) * p_top - (1+fb) * p_low], with no tolerance."""
    rng = random.Random(seed)
    trials = viol = 0
    for _ in range(episodes):
        fb, fs = rng.choice([(0, 0), (30, 30), (100, 100), (300, 300)])
        m = DABC(random_curve(rng), fee_buy_bps=fb, fee_sell_bps=fs)
        try:
            m.buy("h", rng.randint(1, m.capacity() // 2))
            p_low = m.mint_price()
            a = rng.randint(1, max(1, (m.capacity() - m.S) // 3))
            paid = m.buy("att", a)
            m.buy("vic", rng.randint(1, max(1, (m.capacity() - m.S) // 2)))
            p_top = m.price_at(m.S - 1)          # highest minted price
            got, _ = m.sell("att", a)
        except Revert:
            continue
        trials += 1
        if (got - paid) * BPS * WAD > a * ((BPS - fs) * p_top - (BPS + fb) * p_low):
            viol += 1
    return trials, viol


def directed():
    """Boundary cases: rejected inputs leave the state unchanged; no zero-capacity state."""
    bad = []
    m = DABC([[WAD, 10]], fee_buy_bps=0, fee_sell_bps=0)
    m.buy("u", 1); m.sell("u", 1)
    if m.check() or m.capacity() <= 0:
        bad.append("complete redemption on a one-step curve")
    m = DABC([[WAD, 10], [2 * WAD, 10]], fee_buy_bps=0, fee_sell_bps=0)
    m.buy("u", 15); m.sell("u", 15)
    if m.check() or m.capacity() <= 0 or m.Pf != 2 * WAD:
        bad.append("complete redemption on a two-step curve")
    m.reconfigure([[3 * WAD, 7]])
    if m.check() or m.capacity() != 7:
        bad.append("reconfiguration at zero supply")
    m = DABC([[WAD, 10], [2 * WAD, 10]])
    m.buy("u", 12); m.borrow("u", 5, 3)
    calls = [lambda: m.buy([], 1), lambda: m.buy("u", -1), lambda: m.buy("u", 1.5),
             lambda: m.sell("u", 10**9), lambda: m.sell(None, 1), lambda: m.borrow("u", -1, 1),
             lambda: m.borrow("u", 1, 10**9), lambda: m.repay("u", 0), lambda: m.repay("x", 1),
             lambda: m.close("x"), lambda: m.accrue("u", 10**9), lambda: m.skim(10**9),
             lambda: m.set_gamma(10**6), lambda: m.donate(-11), lambda: m.raise_floor(10**9),
             lambda: m.reconfigure([]), lambda: m.reconfigure([[WAD, 0]]),
             lambda: m.reconfigure([[WAD // 2, 100]]), lambda: m.reconfigure(None)]
    for i, call in enumerate(calls):
        before = copy.deepcopy(m.__dict__)
        try:
            call()
            bad.append(f"invalid call {i} was accepted")
        except Revert:
            pass
        except Exception as e:                      # any other exception is a defect
            bad.append(f"invalid call {i} raised {type(e).__name__}")
        if m.__dict__ != before:
            bad.append(f"invalid call {i} changed the state")
    for kw in (dict(debt_cap="flor"), dict(lock_rounding="dwn"), dict(fee_buy_bps=-10000),
               dict(gamma_cap_bps=10001), dict(fee_sell_bps=10000)):
        try:
            DABC([[WAD, 10]], **kw)
            bad.append(f"invalid configuration accepted: {kw}")
        except ValueError:
            pass
    # a reshape or an inflow at zero supply must not retire the untouched floor step
    m = DABC([[WAD, 10], [2 * WAD, 10]])
    m.donate(5)
    m.reconfigure([[WAD, 10], [2 * WAD, 10]], inject=3)
    if m.steps != [[WAD, 10], [2 * WAD, 10]] or m.Pf != WAD or m.A != 8 or m.check():
        bad.append("reshape at zero supply changed the schedule")
    # a raise whose budget is too small to move the level is refused and changes nothing
    m = DABC([[WAD, 3 * 10**18], [2 * WAD, 10]], fee_buy_bps=0, fee_sell_bps=0)
    m.buy("a", 2 * 10**18); m.donate(1)                 # budget 1 over 2e18 tokens: level cannot move
    before = copy.deepcopy(m.__dict__)
    try:
        m.raise_floor(1)
        bad.append("ineffective raise was accepted")
    except Revert:
        pass
    if m.__dict__ != before:
        bad.append("ineffective raise changed the state")
    # after a raise on a one-step curve, a redemption reopens capacity at the floor
    m = DABC([[WAD, 10]], fee_buy_bps=0, fee_sell_bps=0)
    m.buy("a", 2); m.donate(2); m.raise_floor(2)
    if m.Pf != 2 * WAD or m.capacity() != 2:
        bad.append("raise on a one-step curve")
    m.sell("a", 1)
    if m.capacity() != 2 or m.buy("b", 1) != 2 or m.check():
        bad.append("mint at the floor after a redemption from the last step")
    # a full redemption exposes the next step as the new floor; the next mint is at that floor
    m = DABC([[WAD, 10], [2 * WAD, 10], [3 * WAD, 10]], fee_buy_bps=0, fee_sell_bps=0)
    m.buy("a", 2); m.donate(1); m.raise_floor(1)
    if m.steps != [[3 * WAD // 2, 2], [2 * WAD, 10], [3 * WAD, 10]]:
        bad.append("raise on a three-step curve")
    m.sell("a", 2)
    if m.steps != [[2 * WAD, 10], [3 * WAD, 10]] or m.buy("b", 1) != 2 or m.Pf != 2 * WAD or m.check():
        bad.append("mint at the new floor after a full redemption")
    # integer close under the parameter rule: Pf = 1.5, gamma = 90%, f_s = 3%
    m = DABC([[3 * WAD // 2, 10]], gamma_cap_bps=9000, gamma_bps=9000,
             fee_buy_bps=0, fee_sell_bps=300, fee_orig_bps=0)
    m.buy("u", 1); m.borrow("u", 1, 1)
    try:
        if m.close("u") < 0 or m.check():
            bad.append("integer close")
    except Revert:
        bad.append("integer close refused under the parameter rule")
    return bad


if __name__ == "__main__":
    E = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
    N = int(sys.argv[2]) if len(sys.argv) > 2 else 200
    ok = True
    d = directed()
    print("directed boundary tests    failures=%d %s" % (len(d), d if d else ""))
    ok &= not d
    ok &= run("SPEC", E, N, seed=1) == 0
    ok &= run("SPEC + lift cap", E, N, seed=2, lift_cap=True) == 0
    for label, kw in [("MUTANT lock rounds down", dict(lock_rounding="down")),
                      ("MUTANT no floor guard", dict(floor_guard=False)),
                      ("MUTANT debt cap at spot", dict(debt_cap="spot"))]:
        ok &= run(label, max(500, E // 10), N, seed=3, **kw) > 0
    for cap in (False, True):
        t, rej, w, worst = reshape_property(E * 5, 11, cap)
        print(f"mint-reshape-redeem lift_cap={cap!s:5s} trials={t} reshape_refused={rej} "
              f"profitable={w} max_profit={worst}")
        ok &= (w == 0) if cap else (w > 0)
    t, v = sandwich_bound(E * 5, 12)
    print(f"sandwich profit bound      trials={t} violations={v}")
    ok &= v == 0 and t > 0
    print("RESULT:", "PASS (spec holds; every mutant is caught)" if ok else "FAIL")
    sys.exit(0 if ok else 1)
