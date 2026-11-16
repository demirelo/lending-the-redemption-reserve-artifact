"""Recompute every number quoted in the paper.  Usage: python3 -I scripts/numbers.py

Each block prints a tag [Nxx] that the LaTeX source cites in a comment next
to the number, so that every figure in the text can be traced to this file.
"""
import copy
import math
import sys
from fractions import Fraction as F

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from dabc_model import DABC, Revert, WAD, BPS  # noqa: E402

W = WAD


def hdr(t):
    print("\n== " + t)


# ---------------------------------------------------------------- N01 leverage
hdr("[N01] leverage loop, C0=1000, gamma=0.90, phi=0.03, buy at the floor, no trade fee")
g, phi, C0 = F(9, 10), F(3, 100), 1000
eta = g * (1 - phi)
T = C0 / (1 - eta)
Dbt = g * T
fees = phi * Dbt
print("eta =", float(eta), " purchases = tokens*Pf =", round(float(T), 2))
print("gross debt =", round(float(Dbt), 2), " origination fees =", round(float(fees), 2),
      " net proceeds reinvested =", round(float(Dbt - fees), 2))
print("equity at floor = tokens*Pf - debt =", round(float(T - Dbt), 2),
      " = C0 - fees =", round(float(C0 - fees), 2))
print("exposure multiple 1/(1-eta) =", round(float(1 / (1 - eta)), 3),
      " floor-value/equity = 1/(1-gamma) =", float(1 / (1 - g)))
print("v1 off-by-one: 1 + sum_{i>=0} eta^i =", round(float(1 + 1 / (1 - eta)), 3))
# explicit loop as a cross-check of the closed form
cap, tok, debt, fee_tot = F(C0), F(0), F(0), F(0)
for _ in range(2000):
    tok += cap
    b = g * cap
    debt += b
    fee_tot += phi * b
    cap = b * (1 - phi)
print("loop check (2000 rounds): tokens", round(float(tok), 2), "debt", round(float(debt), 2),
      "fees", round(float(fee_tot), 2))
print("with trade fee f_b=1% and premium pi=1.25: eta =",
      round(float(g * (1 - phi) / (F(5, 4) * F(101, 100))), 4),
      " multiple =", round(float(1 / (1 - g * (1 - phi) / (F(5, 4) * F(101, 100)))), 3))
for gg, pp in [(0.90, 0.03), (0.90, 0.04), (0.85, 0.03), (0.80, 0.03), (0.95, 0.03)]:
    e = gg * (1 - pp)
    print(f"  gamma={gg} phi={pp}: eta={e:.4f} multiple={1/(1-e):.2f} "
          f"floor-value/equity={1/(1-gg):.2f} fees/C0={pp*gg/(1-e):.3f}")

# ---------------------------------------------------------- N02 borrow horizon
hdr("[N02] break-even holding horizon T* = ln(1/(1-phi))/r")
for phi_, r_ in [(0.03, 0.05), (0.02, 0.05), (0.03, 0.10), (0.01, 0.04)]:
    Ts = math.log(1 / (1 - phi_)) / r_
    print(f"  phi={phi_} r={r_}: T* = {Ts:.3f} years = {12*Ts:.1f} months")

# ------------------------------------------------------- N03 exit routing
hdr("[N03] exit routing at the floor: borrow-and-abandon vs redeem (per unit of floor value)")
g_, phi_ = 0.90, 0.03
print("  borrow-and-abandon cash =", round(g_ * (1 - phi_), 4))
for fs in [0.01, 0.03, 0.075, 0.10, 0.127, 0.15, 0.225]:
    print(f"  sell fee {fs:.3f}: redeem cash = {1-fs:.3f}  ->",
          "REDEEM" if 1 - fs > g_ * (1 - phi_) else "BORROW-AND-ABANDON")
print("  threshold sell fee = 1 - gamma(1-phi) =", round(1 - g_ * (1 - phi_), 4))

# ------------------------------------------------------- N04 sandwich
hdr("[N04] primary-curve sandwich, steps 100,101,102,103 (1000 tokens each), fees 1%/1%")
ex = [[100 * W, 1000], [101 * W, 1000], [102 * W, 1000], [103 * W, 1000]]
m = DABC(ex, fee_buy_bps=100, fee_sell_bps=100)
paid = m.buy("att", 1000)
m.buy("victim", 3000)
got, _ = m.sell("att", 1000)
print("  attacker pays", paid, "receives", got, "profit", got - paid, "(per token", (got - paid) / 1000, ")")
print("  v1 local condition dp < 2 f p holds on every step:", all(1 < 2 * 0.01 * p for p in (100, 101, 102)))
print("  kappa = (1+fb)/(1-fs) =", round(1.01 / 0.99, 5), " victim price ratio = 1.03")
m = DABC(ex, fee_buy_bps=100, fee_sell_bps=100)
paid = m.buy("att", 1000); m.buy("victim", 1000); got, _ = m.sell("att", 1000)
print("  victim moves 100->101 only (ratio 1.01 < kappa): attacker profit", got - paid)

print("  [N04b] the victim's own price ratio is not necessary: price 1 on 10 tokens, then 100")
two = [[W, 10], [100 * W, 1000]]
alone = DABC(two, fee_buy_bps=100, fee_sell_bps=100).buy("victim", 1)
m = DABC(two, fee_buy_bps=100, fee_sell_bps=100)
paid = m.buy("att", 10); vic = m.buy("victim", 1); got, _ = m.sell("att", 10)
print("    integer settlement: victim alone pays", alone, "; after the front-run the victim pays", vic,
      "; attacker pays", paid, "receives", got, "profit", got - paid)
print("    real-valued: attacker pays", 10 * 1.01, "receives", round(0.99 * 109, 2),
      "profit", round(0.99 * 109 - 10.1, 2), "; victim's curve cost 1 -> 100")

geo = []
price = F(W)
for i in range(60):                      # 1% geometric steps of 1000 tokens, rounded down
    geo.append([int(price), 1000])
    price *= F(101, 100)
print("  [N04c] geometric curve, step ratio 1.01, 1000 tokens per step; supply at a step boundary;")
print("         attacker size fixed at 1000 tokens (one step)")
for fbps in (30, 100, 300):
    kap = F(BPS + fbps, BPS - fbps)
    need = next(n for n in range(1, 99) if F(101, 100) ** n > kap)
    print(f"    fee={fbps}bps kappa={float(kap):.5f}: smallest n with 1.01^n > kappa is n={need}")
    with open(__file__.rsplit("/", 2)[0] + f"/figures/sandwich_{fbps}.dat", "w") as fh:
        fh.write("victim profit\n")
        first = None
        for v in range(1000, 12001, 1000):
            mm = DABC(geo, fee_buy_bps=fbps, fee_sell_bps=fbps)
            mm.buy("seed", 1000)
            c = mm.buy("att", 1000); mm.buy("vic", v); o, _ = mm.sell("att", 1000)
            fh.write(f"{v} {o - c}\n")
            if o - c > 0 and first is None:
                first = v
        print(f"      first victim size (whole steps) with positive attacker profit: {first}")

# ------------------------------------------------------- N05 mint before a floor raise
hdr("[N05] minting just before a floor raise (market at the floor), integer settlement, fees 3%")
for cap in (False, True):
    base = [[W, 1000]] + [[W + (i + 1) * W // 10, 100] for i in range(10)]
    m = DABC(base, fee_buy_bps=300, fee_sell_bps=300, lift_cap=cap)
    m.buy("holders", 1000)              # all supply sits at the floor price 1.0
    m.donate(300)                       # accumulated budget
    ref = copy.deepcopy(m)
    ref.raise_floor(300)
    paid = m.buy("att", 100)            # cost 110 plus fee, rounded up
    m.raise_floor(300)                  # same budget of 300
    got, _ = m.sell("att", 100)
    print(f"  lift cap={cap!s:5s}: floor without attacker {ref.Pf/W:.4f}, with attacker {m.Pf/W:.4f}; "
          f"attacker paid {paid} got {got} profit {got-paid}")
print("  real-valued: pays", 110 * 1.03, "receives", round((1 + (300 - 100 - 110) / 1100 + 0.2) * 100 * 0.97, 3))

# ------------------------------------------------------- N06 reconfiguration gap
hdr("[N06] reconfiguration without the floor guard (v1 Def. 3.5): prices (10,30) -> (8,32)")
m = DABC([[10 * W, 1], [30 * W, 1]], gamma_cap_bps=9000, gamma_bps=9000, fee_buy_bps=0,
         fee_sell_bps=0, fee_orig_bps=0, floor_guard=False)
m.buy("a", 1); m.buy("b", 1)
m.borrow("a", 1, 9)
print("  before: A =", m.A, "D =", m.D, "R(S) =", m.rnum(2) // W, "violations:", m.check())
m.reconfigure([[8 * W, 1], [32 * W, 1]])
print("  after : floor =", m.Pf // W, " debt 9 vs floor value of lock", m.Pf // W,
      "; free token claims", (m.rnum(2) - m.rnum(1)) // W, "vs cash", m.A, " violations:", m.check())
try:
    m.sell("b", 1)
except Revert as e:
    print("  sell by the unlocked holder ->", e)
m2 = DABC([[10 * W, 1], [30 * W, 1]], fee_buy_bps=0, fee_sell_bps=0, fee_orig_bps=0)
m2.buy("a", 1); m2.buy("b", 1); m2.borrow("a", 1, 9)
try:
    m2.reconfigure([[8 * W, 1], [32 * W, 1]])
except Revert as e:
    print("  with the guard the same call ->", e)

# ------------------------------------------------------- N07 rounding
hdr("[N07] lock rounding: floor (public v1 harness) vs ceil (specification)")
for (d, P, gam) in [(3, 2 * W, 9000), (1_000_001, W, 9000), (1, 100 * W, 9000), (101, W, 8000)]:
    dn = d * W * BPS // (gam * P)
    up = -((-d * W * BPS) // (gam * P))
    print(f"  debt={d} price={P/W:g} LTV={gam/100:g}%: lock floor={dn} "
          f"(borrowing power {dn*gam*P//(W*BPS)}, floor value {dn*P//W}) | lock ceil={up} "
          f"(borrowing power {up*gam*P//(W*BPS)})")

# ------------------------------------------------------- N08 tightness
hdr("[N08] tightness: per-token debt cap above the floor breaks coverage")
m = DABC([[W, 100], [2 * W, 100]], gamma_cap_bps=9000, gamma_bps=9000, fee_buy_bps=0,
         fee_sell_bps=0, fee_orig_bps=0, debt_cap="spot")
m.buy("a", 100); m.buy("b", 100)
m.borrow("a", 100, 180)       # 0.9 * spot(2.0) * 100 = 180 > floor value 100
print("  spot-anchored loan: debt 180 on 100 tokens of floor value 100; violations:", m.check())
print("  A =", m.A, " claims of free supply =", (m.rnum(200) - m.rnum(100)) // W)
try:
    m.sell("b", 100)
except Revert as e:
    print("  the unlocked holder redeems ->", e)

# ------------------------------------------------------- N09 misc arithmetic
hdr("[N09] miscellaneous")
print("  v1 Scenario 3: 0.045*100000/200 =", 0.045 * 100000 / 200, "blocks =",
      0.045 * 100000 / 200 * 12 / 60, "minutes at 12 s")
print("  capped interest: gamma=0.80, cap factor 1.10 -> worst ratio", 0.80 * 1.10)
print("  net floor with sell-fee cap 3%:", 1 - 0.03, " design rule gamma + f_s < 1: 0.90+0.03 =", 0.93)
k = lambda fb, fs: (1 + fb) / (1 - fs)
print("  kappa(1%,1%) =", round(k(.01, .01), 4), " kappa(3%,3%) =", round(k(.03, .03), 4),
      " kappa(0.3%,0.3%) =", round(k(.003, .003), 4))
print("  collateral-netted close feasible iff gamma <= 1 - f_s: gamma=0.90, f_s=0.03 -> residual per unit floor value",
      round(1 - 0.03 - 0.90, 4))

# ------------------------------------------------------- figures: curve + raise
hdr("[N10] figure data written to figures/*.dat")
base = [[W, 4000]] + [[W + (i + 1) * W // 5, 1000] for i in range(8)]
m = DABC(base, fee_buy_bps=0, fee_sell_bps=0)
m.buy("x", 7500)
root = __file__.rsplit("/", 2)[0] + "/figures/"


def dump(name, mm):
    with open(root + name, "w") as fh:
        fh.write("s p\n")
        cum = 0
        for p, c in mm.steps:
            if c == 0:
                continue
            fh.write(f"{cum} {p/W:.6f}\n{cum+c} {p/W:.6f}\n")
            cum += c
    return cum


dump("curve_before.dat", m)
m.donate(1500)
m.raise_floor(1500)
dump("curve_after.dat", m)
print("  floor after injecting 1500 into supply 7500:", m.Pf / W, " floor capacity:", m.steps[0][1],
      " surplus left:", m.surplus())
with open(root + "regions.dat", "w") as fh:
    fh.write("fs gER gRC\n")
    for i in range(0, 31):
        fs = i / 100
        fh.write(f"{fs:.2f} {min(1,(1-fs)/(1-0.03)):.4f} {1-fs:.4f}\n")
with open(root + "leverage.dat", "w") as fh:
    fh.write("gamma m0 m3\n")
    for i in range(50, 96):
        gq = i / 100
        fh.write(f"{gq:.2f} {1/(1-gq):.4f} {1/(1-gq*0.97):.4f}\n")
print("  ok")

# ------------------------------------------------------- N11 equilibrium in the floor economy
hdr("[N11] floor economy: lock share, growth rate, revenue-maximising fee (exponential horizons)")
import random as _rnd


def T0(phi, rho):
    return math.log(1 / (1 - phi)) / rho


def lock_share(phi, rho, tau):
    z = T0(phi, rho) / tau
    return (1 + z) * math.exp(-z)


def growth(alpha, fb, fs, phi, gam, rho, tau):
    z = T0(phi, rho) / tau
    surv = math.exp(-z)                    # 1 - F(T0)
    mass = tau * math.exp(-z)              # E[(T - T0)^+]
    return alpha * ((fb + fs) + phi * gam * surv) / (tau - alpha * phi * gam * mass)


for phi_, rho_, tau_ in [(0.01, 0.05, 1.0), (0.03, 0.05, 1.0), (0.01, 0.05, 0.5), (0.03, 0.05, 2.0)]:
    print(f"  phi={phi_} rho={rho_} tau={tau_}: T0={12*T0(phi_, rho_):.1f} months, "
          f"lock share U={lock_share(phi_, rho_, tau_):.3f}")
# Monte Carlo check of the lock share: stationary population, exponential horizons
_rnd.seed(7)
phi_, rho_, tau_ = 0.03, 0.05, 1.0
t0 = T0(phi_, rho_)
hs = [_rnd.expovariate(1 / tau_) for _ in range(400_000)]
mc = sum(h for h in hs if h > t0) / sum(hs)
print(f"  Monte Carlo lock share (phi=0.03, rho=0.05, tau=1): {mc:.3f} vs formula {lock_share(phi_, rho_, tau_):.3f}")
mcm = sum(max(h - t0, 0) for h in hs) / len(hs)
print(f"  Monte Carlo E[(T-T0)^+]: {mcm:.3f} vs tau*exp(-T0/tau) = {tau_*math.exp(-t0/tau_):.3f}")
for a_ in (0.5, 1.0):
    print(f"  growth g* with alpha={a_}, fb=fs=1%, phi=3%, gamma=0.9, rho=5%, tau=1: "
          f"{growth(a_, 0.01, 0.01, 0.03, 0.9, 0.05, 1.0):.4f} per year")
print(f"  growth g* with alpha=1, fb=fs=0, phi=1%, gamma=1, rho=5%, tau=1: "
      f"{growth(1.0, 0, 0, 0.01, 1.0, 0.05, 1.0):.4f} per year")
for rho_, tau_ in [(0.05, 1.0), (0.05, 2.0), (0.10, 1.0)]:
    k = 1 / (rho_ * tau_)
    star = 1 / (1 + k)
    grid = max((p / 100000 * (1 - p / 100000) ** k, p / 100000) for p in range(1, 100000))[1]
    z = T0(star, rho_) / tau_
    print(f"  revenue-maximising fee: rho={rho_} tau={tau_}: phi*={star:.4f} (grid search {grid:.4f}); "
          f"lock share at phi* = {(1+z)*math.exp(-z):.3f}; T0/tau = {z:.3f}")
print("  limit of the lock share at phi* as rho*tau -> 0: 2/e =", round(2 / math.e, 3))

# ------------------------------------------------------- N12 entry value in the floor economy
hdr("[N12] entry value of a buyer in the floor economy (cash-only preferences)")


def entry_value(T, g, rho, phi, gam, fb, fs):
    """Present value at entry, per token and per unit of the entry floor, of buying, following the
    optimal borrowing plan (borrow at arrival, top up until T - T0, repay at exit) and redeeming at T."""
    t0 = T0(phi, rho)
    v = -(1 + fb) + (1 - fs) * math.exp((g - rho) * T)
    if T > t0:
        A = T - t0
        v += gam * ((1 - phi) - math.exp(-rho * T))
        v += gam * g * ((1 - phi) * (math.exp((g - rho) * A) - 1) / (g - rho)
                        - math.exp(-rho * T) * (math.exp(g * A) - 1) / g)
    return v


def integrate_exp(f, tau, hi=60.0, n=200_000):
    h = hi / n
    return sum(f((i + 0.5) * h) * math.exp(-(i + 0.5) * h / tau) / tau * h for i in range(n))


rho_, tau_, phi_, gam_, fb_, fs_, al_ = 0.05, 1.0, 0.03, 0.9, 0.01, 0.01, 1.0
g_ = growth(al_, fb_, fs_, phi_, gam_, rho_, tau_)
t0_ = T0(phi_, rho_)
print(f"  parameters: rho={rho_} tau={tau_} phi={phi_} gamma={gam_} fb=fs={fb_} alpha={al_}; T0={t0_:.6f} g*={g_:.7f}")
v1 = entry_value(1.0, g_, rho_, phi_, gam_, fb_, fs_)
buy_redeem = -(1 + fb_) + (1 - fs_) * math.exp(g_ - rho_)
loan0 = gam_ * ((1 - phi_) - math.exp(-rho_))
print(f"  V(1) = {v1:.8f}: purchase and redemption {buy_redeem:.8f}, first loan {loan0:.8f}, "
      f"top-ups {v1 - buy_redeem - loan0:.8f}")
for T_ in (0.3, 1, 2, 3, 5, 10):
    print(f"    V({T_}) = {entry_value(T_, g_, rho_, phi_, gam_, fb_, fs_):+.5f}")
lo, hi = 1.0, 3.0
for _ in range(60):
    mid = (lo + hi) / 2
    lo, hi = (mid, hi) if entry_value(mid, g_, rho_, phi_, gam_, fb_, fs_) < 0 else (lo, mid)
print(f"  horizon at which V changes sign: {hi:.3f} years; share of arriving tokens with V < 0: "
      f"{1 - math.exp(-hi / tau_):.3f}")
mean_v = integrate_exp(lambda T: entry_value(T, g_, rho_, phi_, gam_, fb_, fs_), tau_)
print(f"  mean entry value E[V(T)] by numerical integration: {mean_v:.6f}")


# the identity of the theorem:  mean V = -(g A_n + s)/nu - (rho - g) X / nu   (nu = 1, s = 0 for alpha = 1)
def stationary(f, tau, hi=60.0, m=4000, k=400):
    """Integral of f(T, a) over the stationary population (density e^(-T/tau)/tau in T, ages 0..T).
    The horizon axis is split at T0 and the age axis at T - T0, where f has kinks or jumps."""
    def inner(T):
        cut = max(T - t0_, 0.0)
        tot = 0.0
        for lo, hi_ in ((0.0, cut), (cut, T)):
            if hi_ > lo:
                da = (hi_ - lo) / k
                tot += sum(f(T, lo + (j + 0.5) * da) for j in range(k)) * da
        return tot
    tot = 0.0
    for lo, hi_, n in ((0.0, t0_, m // 10), (t0_, hi, m)):
        h = (hi_ - lo) / n
        for i in range(n):
            T = lo + (i + 0.5) * h
            tot += math.exp(-T / tau) / tau * h * inner(T)
    return tot


def debt_n(T, a):
    if T <= t0_:
        return 0.0
    return gam_ if a <= T - t0_ else gam_ * math.exp(-g_ * (a - (T - t0_)))


def continuation(T, a):
    """Present value of the remaining cash flows of a holder of age a, per token, current floor = 1."""
    rem = T - a
    v = (1 - fs_) * math.exp((g_ - rho_) * rem)
    if T > t0_:
        if a <= T - t0_:
            A = T - t0_ - a
            v += gam_ * g_ * (1 - phi_) * (math.exp((g_ - rho_) * A) - 1) / (g_ - rho_)
            v -= gam_ * math.exp(g_ * A) * math.exp(-rho_ * rem)
        else:
            v -= debt_n(T, a) * math.exp(-rho_ * rem)
    return v


Dn = stationary(debt_n, tau_)
An = tau_ - Dn
X = stationary(continuation, tau_)
print(f"  stationary debt per unit of arrivals D_n = {Dn:.5f}, cash A_n = S - D_n = {An:.5f}, "
      f"continuation value of current holders X = {X:.5f}")
print(f"  identity: -(g A_n) - (rho - g) X = {-(g_ * An) - (rho_ - g_) * X:.6f}  (mean V above: {mean_v:.6f})")
ben = -mean_v / (tau_ / (1 + rho_ * tau_))
print(f"  flow benefit per token-year that makes the mean entry value zero: {ben:.5f} of the floor price "
      f"(E[(1-e^(-rho T))/rho] = {tau_ / (1 + rho_ * tau_):.4f})")

# ------------------------------------------------------- N13 the issuer's side of a loan
hdr("[N13] issuer's present value of a loan when the reserve could earn the rate r_I")
for rI in (0.0, 0.02, 0.05):
    T_ = 1.0
    print(f"  r_I={rI}: loan of horizon 1, fee 3%: issuer PV per unit of debt = {math.exp(-rI * T_) - (1 - 0.03):+.7f}")
k_ = 1 / (rho_ * tau_)
for ph in (0.01, 0.03, 0.0476, 0.2, 0.5):
    z = T0(ph, rho_) / tau_
    net = math.exp(-z) * ((1 - ph) / (1 + rho_ * tau_) - (1 - ph))       # r_I = rho, exponential horizons
    print(f"  r_I=rho: net lending value per arriving token and unit of gamma at fee {ph}: {net:+.6f} "
          f"(gross fee flow {ph * math.exp(-z):.6f})")


def lending_value(ph, rI, rho, tau):
    """Issuer's present value of lending per arriving token and unit of gamma (alpha = 0, exponential horizons)."""
    z = T0(ph, rho) / tau
    return math.exp(-z) * (math.exp(-rI * T0(ph, rho)) / (1 + rI * tau) - (1 - ph))


for rI in (0.0, 0.02, 0.03, 0.04):
    closed = 1 - (1 + rho_ * tau_) ** (-rho_ / (rho_ - rI))
    best = max((lending_value(i / 100000, rI, rho_, tau_), i / 100000) for i in range(1, 99999))
    print(f"  r_I={rI}: fee that maximises the issuer's present value: closed form {closed:.5f}, grid search {best[1]:.5f}, "
          f"value {best[0]:.6f}; locked share at that fee {(1 + T0(closed, rho_) / tau_) * math.exp(-T0(closed, rho_) / tau_):.4f}")


# ------------------------------------------------------- N14 committed buffer: debt capacity against redemption value
hdr("[N14] linear price p(q) = P + k q: maximum debt with a committed buffer W against the redemption value R(L)")
P_, k_c, L_ = 1.0, 1.0, 1.0
RL = L_ * (P_ + k_c * L_ / 2)
print(f"  P={P_} k={k_c} L={L_}: R(L) = {RL}; debt capacity exceeds R(L) when W > k L^2 / 8 = {k_c * L_ ** 2 / 8}")
for W_ in (0.05, 0.1, 0.125, 0.2, 0.5, 0.8):
    if W_ <= k_c * L_ ** 2 / 2:
        Dm = L_ * (P_ + math.sqrt(2 * k_c * W_))
    else:
        Dm = L_ * (P_ + k_c * L_ / 2) + W_
    # brute-force check of D_max = L inf_q (R(q) + W) / q
    brute = min(L_ * ((P_ * q + k_c * q * q / 2) + W_) / q for q in (i / 100000 for i in range(1, 100001)))
    assert abs(brute - Dm) < 1e-6, (W_, brute, Dm)
    print(f"  W={W_}: D_max = {Dm:.4f} ({'above' if Dm > RL + 1e-12 else 'not above'} R(L))")


# ------------------------------------------------------- N15 pro-rata envelope against the exact whole-position buffer
hdr("[N15] committed buffer: pro-rata envelope minus exact whole-position requirement, against max_i (d_i - Pf l_i)^+")
from fractions import Fraction as Fr
from itertools import combinations
import random as _rnd15

_r15 = _rnd15.Random(2026)


def _R_lin(q, P, k):
    return P * q + k * q * q / 2


def _w_prorata(loans, P, k):
    """max over q of H(q) - R(q) for R(q) = P q + k q^2 / 2 (exact rationals)."""
    order = sorted(loans, key=lambda x: Fr(x[1], 1) / x[0], reverse=True)
    best, Q, B = Fr(0), Fr(0), Fr(0)
    for l, d in order:
        a = Fr(d) / l
        cands = [Q, Q + l]
        if k > 0:
            star = (a - P) / k
            if Q < star < Q + l:
                cands.append(star)
        for q in cands:
            best = max(best, B + a * (q - Q) - _R_lin(q, P, k))
        Q, B = Q + l, B + d
    return best


def _w_whole(loans, P, k):
    best = Fr(0)
    for r in range(1, len(loans) + 1):
        for sub in combinations(loans, r):
            best = max(best, sum(d for _, d in sub) - _R_lin(sum(l for l, _ in sub), P, k))
    return best


viol = viol4 = worst = 0
N15 = 3000
for _ in range(N15):
    P, k = Fr(_r15.randint(1, 4)), Fr(_r15.randint(0, 6), _r15.randint(1, 4))
    loans = []
    for _ in range(_r15.randint(1, 6)):
        l = Fr(_r15.randint(1, 5))
        loans.append((l, l * P * Fr(_r15.randint(5, 25), 10)))        # debt between 0.5 and 2.5 times the floor value
    gap = _w_prorata(loans, P, k) - _w_whole(loans, P, k)
    bound = max(max(d - P * l, Fr(0)) for l, d in loans)
    viol += not (0 <= gap <= bound)
    viol4 += not (4 * gap <= bound)
    worst = max(worst, float(gap / bound) if bound > 0 else 0.0)
assert viol == 0 and viol4 == 0
print(f"  {N15} random books (1 to 6 loans, linear price, exact rationals): violations of 0 <= gap <= bound: {viol}; "
      f"largest gap / bound: {worst:.4f}")
print(f"  violations of the linear-price bound gap <= bound / 4: {viol4}")
_eps = Fr(1, 100)                                        # step curve: price 1 below 1 - eps, 1 + 1/eps above
_Rstep = lambda q: q if q <= 1 - _eps else (1 - _eps) + (1 + 1 / _eps) * (q - (1 - _eps))
_wp = max(2 * Fr(i, 10000) - _Rstep(Fr(i, 10000)) for i in range(0, 10001))
print(f"  step example, eps = 0.01, one loan (1, 2): R(1) = {_Rstep(Fr(1))}, W_whole = {max(Fr(0), 2 - _Rstep(Fr(1)))}, "
      f"W_prop = {float(_wp)}, floor excess = 1")

# ------------------------------------------------------- N16 what a coalition can take out of a committed buffer
hdr("[N16] R(q) = q + q^2/2, L = S = 1, W = 0.08: borrow at capacity, repay part, redeem the released part, abandon the rest")
Rq = lambda q: q + q * q / 2
W16 = Fr(8, 100)
D16 = 1 + Fr(4, 10)                                    # D_max = L (P + sqrt(2 k W)) = 1.4
assert (D16 - 1) ** 2 == 2 * W16
best = max(((D16 * Fr(i, 1000) - Rq(Fr(i, 1000))), Fr(i, 1000)) for i in range(0, 1001))
print(f"  D_max = {float(D16)}; W_min = max_q (1.4 q - R(q)) = {float(best[0])} at q = {float(best[1])}; R(1) = {float(Rq(Fr(1)))}")
q16 = best[1]
flows = [-Rq(Fr(1)), D16, -(D16 - D16 * q16), Rq(Fr(1)) - Rq(q16)]
print(f"  cash flows (buy, borrow, repay, redeem released): {[float(x) for x in flows]}; net = {float(sum(flows))}; "
      f"issuer cash afterwards = {float(W16 + Rq(Fr(1)) - D16 + (D16 - D16 * q16) - (Rq(Fr(1)) - Rq(q16)))}")
fb = fo = fs = Fr(1, 100)
net_fee = D16 * q16 - Rq(q16) - fb * Rq(Fr(1)) - fo * D16 - fs * (Rq(Fr(1)) - Rq(q16))
print(f"  with buy, origination and sell fees of 1%: net = {float(net_fee)}")
q2 = Fr(2, 10)
res = max(D16 * Fr(i, 10000) - Rq(Fr(i, 10000)) for i in range(0, 2001))
print(f"  after repaying 1.12 (residual lock {float(q2)}, debt {float(D16 * q2)}): required buffer = {float(res)}, "
      f"so {float(W16 - res)} of the buffer can be withdrawn while the loan is open")


# ------------------------------------------------------- N17 the three contracts compared
hdr("[N17] p(q) = 1 + q, total lock L = 1: credit under the floor cap, a committed reserve, and a curve-valued lock")
R17 = lambda q: q + q * q / 2
W17 = 0.08
D17 = 1 + math.sqrt(2 * W17)
print(f"  floor cap: aggregate credit {1.0}; committed reserve W = {W17}: D_max = {D17:.4f} (+{100 * (D17 - 1):.0f}%)")
for l in (0.1, 0.5, 1.0):
    print(f"  curve-valued lock of size {l}: credit R(l) = {R17(l):.4f}, gain over the floor value {100 * (R17(l) / l - 1):.0f}%")
print(f"  ten equal locks of 0.1: aggregate {10 * R17(0.1):.4f}; one lock of 1: {R17(1.0):.4f}")
u17 = 1 - (-1 + math.sqrt(1 + 2 * 0.75))          # R(q) = 0.75  =>  q = -1 + sqrt(2.5)
print(f"  unit lock at the limit 1.5, repay half the debt (0.75): released {u17:.4f} tokens (proportional rule: 0.5)")
