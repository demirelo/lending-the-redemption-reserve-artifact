"""Empirical analysis of Baseline credit on Ethereum (public event logs).

Usage: python3 -I empirics/analyze.py      # prints results, writes sections/empnums.tex
Input: empirics/data/logs_eth.jsonl, meta.json (fetch.py) and supply.json (supply.py)

Units of account in this file: an *account* is a (pool, address) pair; an
*event* is one log; a *loan episode* is a maximal period in which an account
has positive debt. Windows are in blocks: 300 blocks (about one hour) and
50,400 blocks (about seven days) at twelve seconds per block.
"""
import bisect
import collections
import json
import os
import statistics
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from decode import load  # noqa: E402

evs, meta = load()
supply = json.load(open(os.path.join(HERE, "data", "supply.json")))
endpoint = json.load(open(os.path.join(HERE, "data", "endpoint.json")))   # contract state at the last block
assert endpoint["block"] == meta["to_block"]
E18 = 10**18
HOUR, WEEK = 300, 50_400
END = meta["to_block"]
CREDIT = ("Borrow", "Repay", "Leverage", "Deleverage")
anch = sorted((int(b), t) for b, t in meta["anchors"].items())


def ts(block):
    """Block timestamp by linear interpolation between fetched anchor blocks."""
    i = max(1, min(len(anch) - 1, bisect.bisect_left([b for b, _ in anch], block)))
    (b0, t0), (b1, t1) = anch[i - 1], anch[i]
    return t0 + (t1 - t0) * (block - b0) / (b1 - b0)


def days(b0, b1):
    return (ts(b1) - ts(b0)) / 86400


def after(x, e):
    return (x["block"], x["idx"]) > (e["block"], e["idx"])


tokens = [e["bToken"] for e in evs if e["event"] == "Initialized"]
by_acct = collections.defaultdict(list)           # (pool, address) -> events in log order
for e in evs:
    if "user" in e:
        by_acct[(e["bToken"], e["user"])].append(e)

rows = []
tot = collections.Counter()
repay_cls = collections.Counter()
episodes = []          # (pool, address, opened_block, opening_event, closed_block or None)
snap_accts, state_end = set(), {}

for tok in tokens:
    sym = supply[tok]["symbol"]
    init_block = next(e["block"] for e in evs if e["event"] == "Initialized" and e["bToken"] == tok)
    acct, snap, snap_block = {}, {}, None
    stake = collections.Counter()
    open_ep, cnt = {}, collections.Counter()
    floors, prices = [], []
    for e in evs:
        if e["bToken"] != tok:
            continue
        cnt[e["event"]] += 1
        if e["event"] == "CreditClaim":
            snap_block = e["block"]
            for u, c, d in zip(e["users"], e["collaterals"], e["debts"]):
                acct[u] = (c, d)
                snap[u] = (c, d)
                snap_accts.add((tok, u))
        elif e["event"] in CREDIT:
            u = e["user"]
            before = acct.get(u, (0, 0))
            acct[u] = (e["collateral"], e["debt"])
            if u not in snap:
                if before[1] == 0 and e["debt"] > 0:
                    open_ep[u] = (e["block"], e["event"])
                elif before[1] > 0 and e["debt"] == 0 and u in open_ep:
                    b0, kind = open_ep.pop(u)
                    episodes.append((tok, u, b0, kind, e["block"]))
        elif e["event"] == "Deposit":
            stake[e["user"]] += e["amount"]
        elif e["event"] in ("Withdraw", "Liquidate"):
            stake[e["user"]] -= e["amount"]
        elif e["event"] == "Swap":
            floors.append(e["blvPrice"])
            prices.append(e["activePrice"])
    for u, (b0, kind) in open_ep.items():
        episodes.append((tok, u, b0, kind, None))
    for u, st in acct.items():
        state_end[(tok, u)] = st
    coll = sum(c for c, d in acct.values())
    debt = sum(d for c, d in acct.values())
    staked = sum(stake.values())
    assert all(v >= 0 for v in stake.values()), f"{sym}: negative reconstructed stake"
    # collateral is staked automatically, so the reconstructed stake must cover it
    assert staked >= coll, f"{sym}: stake {staked} below collateral {coll}"
    total_supply, in_contract = int(supply[tok]["end"][0]), int(supply[tok]["end"][1])
    wallets = total_supply - in_contract                 # tokens held outside the contract
    assert in_contract >= staked, f"{sym}: contract balance below reconstructed stake"
    outside_pool = wallets + staked                      # supply not in the pool's own inventory
    # reconcile the reconstruction with the contract's own totals at the last block
    ep = {k: int(v) for k, v in endpoint["pools"][tok].items()}
    assert coll == ep["totalCollateral"], f"{sym}: collateral {coll} != {ep['totalCollateral']}"
    assert debt == ep["totalDebt"], f"{sym}: debt {debt} != {ep['totalDebt']}"
    assert staked == ep["totalStaked"], f"{sym}: stake {staked} != {ep['totalStaked']}"
    # The contract's circulating supply equals our measure plus any tokens that the contract counts
    # in its total supply but that are not in the ERC-20 total supply on this chain (ONYX only).
    off_chain = ep["totalSupply"] - total_supply
    assert abs(outside_pool + off_chain - ep["getCirculatingSupply"]) <= 10, f"{sym}: circulating supply mismatch"
    share_contract = coll / ep["getCirculatingSupply"]
    floor_end = ep["blvPrice"]
    last_swap_block = max(e["block"] for e in evs if e["event"] == "Swap" and e["bToken"] == tok)
    n_open = sum(1 for c, d in acct.values() if d > 0)
    s_open = sum(1 for u in snap if acct[u][1] > 0)
    s_same = sum(1 for u in snap if acct[u] == snap[u])
    # account-associated activity after the snapshot: any credit, swap, withdraw or claim event,
    # or a stake deposit that is not part of the migration itself
    active = [u for u in snap if any(
        x["block"] > snap_block and (x["event"] != "Deposit" or x["block"] > snap_block + 10)
        for x in by_acct[(tok, u)])]
    a_closed = sum(1 for u in active if acct[u][1] == 0)
    rows.append(dict(
        sym=sym, accounts=len(acct), open=n_open, share=share_contract, share_erc20=coll / outside_pool,
        off_chain=off_chain,
        lens_total=ep["totalSupply"], erc_total=total_supply, circ=ep["getCirculatingSupply"],
        ltv=debt * E18 / (floor_end * coll) if coll else float("nan"),
        floor_end_same=(floor_end == floors[-1]), floor_end_ratio=floor_end / floors[-1],
        last_swap_days=days(last_swap_block, END),
        prem0=prices[0] / floors[0], prem1=prices[-1] / floors[-1],
        floor_values=len(set(floors)), floor_ratio=max(floors) / min(floors),
        floor_changes=sum(1 for a, b in zip(floors, floors[1:]) if a != b),
        snap=len(snap), snap_open=s_open, inc=cnt["Borrow"] + cnt["Leverage"],
        repay=cnt["Repay"], delev=cnt["Deleverage"], coll=coll, debt=debt, days=days(init_block, END)))
    for k in ("Borrow", "Repay", "Leverage", "Deleverage", "Swap", "Liquidate", "Claim"):
        tot[k] += cnt[k]
    tot["snap"] += len(snap); tot["snap_open"] += s_open; tot["snap_same"] += s_same
    tot["active"] += len(active); tot["active_closed"] += a_closed

# ---- what follows a plain repayment (categories are mutually exclusive)
repay_accts = set()
for e in evs:
    if e["event"] != "Repay":
        continue
    mine = by_acct[(e["bToken"], e["user"])]
    repay_accts.add((e["bToken"], e["user"]))

    def sale(lo, hi, later):
        return any(x["event"] == "Swap" and x["bTokenDelta"] < 0 and
                   e["block"] + lo <= x["block"] <= e["block"] + hi and after(x, e) == later for x in mine)

    sold_w = sale(0, WEEK, True)
    reborrow = any(x["event"] in ("Borrow", "Leverage") and after(x, e) and x["block"] <= e["block"] + WEEK
                   for x in mine)
    repay_cls["sold_hour"] += sale(0, HOUR, True)
    repay_cls["sold_week"] += sold_w
    repay_cls["sold_before_hour"] += sale(-HOUR, 0, False)
    repay_cls["reborrow_any"] += reborrow
    repay_cls["cat_sold" if sold_w else ("cat_reborrow" if reborrow else "cat_neither")] += 1
    repay_cls["full" if e["debt"] == 0 else "partial"] += 1
# ---- further estimands for plain repayments: censoring, concentration, amounts
assert all(e["block"] + WEEK <= END for e in evs if e["event"] == "Repay"), "a repayment has an incomplete window"
rep_events = [e for e in evs if e["event"] == "Repay"]


def followed_by_sale(e):
    return any(x["event"] == "Swap" and x["bTokenDelta"] < 0 and after(x, e) and x["block"] <= e["block"] + WEEK
               for x in by_acct[(e["bToken"], e["user"])])


per_acct = collections.Counter((e["bToken"], e["user"]) for e in rep_events)
top2 = [k for k, _ in per_acct.most_common(2)]
top2_events = sum(per_acct[k] for k in top2)
rest = [e for e in rep_events if (e["bToken"], e["user"]) not in top2]
rest_sold = sum(1 for e in rest if followed_by_sale(e))
amt_total = sum(e["debtRepaid"] for e in rep_events)
amt_sold = sum(e["debtRepaid"] for e in rep_events if followed_by_sale(e))
# ---- amounts of new debt: plain loans against leverage (all pools have the same reserve asset)
assert len({endpoint["pools"][t]["reserve"] for t in tokens}) == 1
amt_borrow = sum(e["borrowed"] + e["fee"] for e in evs if e["event"] == "Borrow")
amt_lever = sum(e["debtAdded"] for e in evs if e["event"] == "Leverage")
full_delev = sum(1 for e in evs if e["event"] == "Deleverage" and e["debt"] == 0)
full_repay = sum(1 for e in evs if e["event"] == "Repay" and e["debt"] == 0)
reduce_n = tot["Repay"] + tot["Deleverage"]
linked = tot["Deleverage"] + repay_cls["cat_sold"] + repay_cls["cat_reborrow"]

acct_sold_after = sum(
    1 for k in repay_accts
    if any(x["event"] == "Swap" and x["bTokenDelta"] < 0 and
           any(r["event"] == "Repay" and after(x, r) and x["block"] <= r["block"] + WEEK for r in by_acct[k])
           for x in by_acct[k]))
# comparison group: accounts in debt at the end that never reduced their debt
never_reduced = [k for k, st in state_end.items()
                 if st[1] > 0 and not any(x["event"] in ("Repay", "Deleverage") for x in by_acct[k])]
nr_sold = sum(1 for k in never_reduced if any(x["event"] == "Swap" and x["bTokenDelta"] < 0 for x in by_acct[k]))

new_accts = {(t, u) for t, u, *_ in episodes}
ep_closed = [days(b0, b1) for _, _, b0, _, b1 in episodes if b1 is not None]
ep_open = [days(b0, END) for _, _, b0, _, b1 in episodes if b1 is None]
ep_kind = collections.Counter(kind for *_, kind, _ in [(t, u, b0, kind, b1) for t, u, b0, kind, b1 in episodes])
first_kind = collections.Counter()
for k in new_accts:
    first_kind[next(x["event"] for x in by_acct[k] if x["event"] in CREDIT)] += 1
# the first loan episode of each new account
first_ep = {}
for t, u, b0, kind, b1 in sorted(episodes, key=lambda x: x[2]):
    first_ep.setdefault((t, u), (b0, b1))
first_closed = [days(b0, b1) for b0, b1 in first_ep.values() if b1 is not None]
accts_short = len({(t, u) for t, u, b0, kind, b1 in episodes if b1 is not None and days(b0, b1) <= 30})
fees = sorted(e["fee"] / (e["borrowed"] + e["fee"]) for e in evs if e["event"] == "Borrow" and e["borrowed"] > 0)


def med(xs):
    return statistics.median(xs)


def kaplan_meier(spells, horizon):
    """Share of loan episodes still open after `horizon` days (product-limit estimate).
    spells: (duration in days, closed?) ; open episodes are censored at the end of the sample."""
    surv = 1.0
    for t in sorted({d for d, closed in spells if closed and d <= horizon}):
        at_risk = sum(1 for d, _ in spells if d >= t)
        events = sum(1 for d, closed in spells if closed and d == t)
        surv *= 1 - events / at_risk
    return surv


spells = [(days(b0, b1), True) for _, _, b0, _, b1 in episodes if b1 is not None] + \
         [(days(b0, END), False) for _, _, b0, _, b1 in episodes if b1 is None]


# ---------------------------------------------------------------- printed report
span = days(meta["from_block"], END)
print(f"dataset: blocks {meta['from_block']}-{END}, {meta['n_logs']} logs, {span:.0f} days")
print("event types not used (administrative, fee distribution, one unidentified):", meta["ignored_events"])
print(f"{'pool':8s} {'accts':>5s} {'open':>5s} {'locked':>7s} {'debt/floor':>10s} {'prem0':>6s} {'prem1':>6s} "
      f"{'floor chg':>9s} {'ratio':>6s} | {'snap':>4s} {'open':>4s} | {'incr':>4s} {'repay':>5s} {'delev':>5s}")
for r in rows:
    print(f"{r['sym']:8s} {r['accounts']:5d} {r['open']:5d} {r['share']:7.3f} {r['ltv']:10.4f} {r['prem0']:6.3f} "
          f"{r['prem1']:6.3f} {r['floor_changes']:9d} {r['floor_ratio']:6.3f} | {r['snap']:4d} {r['snap_open']:4d} | "
          f"{r['inc']:4d} {r['repay']:5d} {r['delev']:5d}")
print("events:", {k: tot[k] for k in ("Borrow", "Leverage", "Repay", "Deleverage", "Swap", "Liquidate", "Claim")})
print(f"origination fee / gross amount in Borrow events: min {fees[0]:.5f} median {med(fees):.5f} max {fees[-1]:.5f}")
print(f"debt-reducing events {reduce_n}: Deleverage {tot['Deleverage']} ({tot['Deleverage']/reduce_n:.1%}), Repay {tot['Repay']}")
print(f"full closures: by Deleverage {full_delev}, by Repay {full_repay}")
print("plain repayments:", dict(repay_cls))
print(f"plain repayments followed by a sale within {WEEK} blocks: {repay_cls['sold_week']}/{tot['Repay']} "
      f"= {repay_cls['sold_week']/tot['Repay']:.1%}; all {tot['Repay']} have a complete window")
print(f"the two most active repaying accounts make {top2_events} of {tot['Repay']} repayments "
      f"({top2_events/tot['Repay']:.1%}), pools {[supply[k[0]]['symbol'] for k in top2]}; without them: "
      f"{rest_sold}/{len(rest)} = {rest_sold/len(rest):.1%}")
print(f"amount of plain repayments followed by a sale: {amt_sold/amt_total:.1%} of {amt_total/E18:.2f}")
print(f"gross new debt: plain loans {amt_borrow/E18:.8f}, leverage {amt_lever/E18:.8f}; leverage share "
      f"{amt_lever/(amt_borrow+amt_lever):.4%}")
print("new loan episodes still open (Kaplan-Meier): " +
      ", ".join(f"{h} d {kaplan_meier(spells, h):.1%}" for h in (7, 30, 90, 180)))
for r in rows:
    print(f"  {r['sym']}: locked share with the contract's circulating supply {r['share']:.4f}, with ERC-20 supply "
          f"{r['share_erc20']:.4f} (tokens counted by the contract beyond the ERC-20 supply: {r['off_chain']/E18:.0f})")
    print(f"  {r['sym']}: floor at the last block / floor at the last swap = {r['floor_end_ratio']:.6f}; "
          f"last swap {r['last_swap_days']:.1f} days before the end")
print(f"debt reductions that are a Deleverage, or a Repay followed within {WEEK} blocks by a sale or a new loan: "
      f"{linked}/{reduce_n} = {linked/reduce_n:.1%}")
print(f"accounts with a plain Repay: {len(repay_accts)}; sold within {WEEK} blocks after one: {acct_sold_after}")
print(f"accounts in debt at the end with no debt reduction: {len(never_reduced)}; any sale in the whole window: {nr_sold} "
      f"({nr_sold/len(never_reduced):.1%})")
print(f"carried-over accounts {tot['snap']}: in debt at the end {tot['snap_open']} ({tot['snap_open']/tot['snap']:.1%}); "
      f"credit position unchanged {tot['snap_same']} ({tot['snap_same']/tot['snap']:.1%}); with later account activity "
      f"{tot['active']}, of these closed {tot['active_closed']} ({tot['active_closed']/tot['active']:.1%})")
print(f"new accounts {len(new_accts)} (first credit event {dict(first_kind)}); loan episodes {len(episodes)} "
      f"(opened by {dict(ep_kind)}); closed {len(ep_closed)} (median age {med(ep_closed):.1f} d, within 30 d "
      f"{sum(1 for a in ep_closed if a <= 30)}); open {len(ep_open)} (median age {med(ep_open):.0f} d)")
print(f"first episode of each new account: closed {len(first_closed)}, within 30 d "
      f"{sum(1 for a in first_closed if a <= 30)}; accounts with at least one episode closed within 30 d: {accts_short}")

# ---------------------------------------------------------------- heterogeneity, uncertainty, upgrades
import json as _json
import random as _random

sym_of = {t: supply[t]["symbol"] for t in tokens}
# (a) plain repayments by pool
pool_rep = {}
for e in rep_events:
    r = pool_rep.setdefault(sym_of[e["bToken"]], {"n": 0, "sold": 0, "accts": set()})
    r["n"] += 1
    r["sold"] += followed_by_sale(e)
    r["accts"].add(e["user"])
# (b) by half of the sample window
mid_block = (meta["from_block"] + END) // 2
half = {h: [e for e in rep_events if (e["block"] > mid_block) == h] for h in (False, True)}
# (c) interval for the share followed by a sale, resampling accounts (clusters), not events
by_cluster = collections.defaultdict(list)
for e in rep_events:
    by_cluster[(e["bToken"], e["user"])].append(followed_by_sale(e))
clusters = list(by_cluster.values())
_rng = _random.Random(2026)
boot = []
for _ in range(10_000):
    draw = [clusters[_rng.randrange(len(clusters))] for _ in clusters]
    boot.append(sum(map(sum, draw)) / sum(map(len, draw)))
boot.sort()
ci_lo, ci_hi = boot[249], boot[9749]
# (d) number of episodes still under observation at each horizon of the survival estimate
at_risk = {h: sum(1 for d, _ in spells if d >= h) for h in (30, 90, 180)}
late_closes = sum(1 for d, closed in spells if closed and d > 180)
# (e) component upgrades: which component, when, and whether the event layouts changed
UPG = "0x198aeafd78956c82987d6b6e05441c98958e51bf483fa75b0a65babd3483dfcb"
upgrades, layout = [], collections.defaultdict(set)
with open(os.path.join(HERE, "data", "logs_eth.jsonl")) as fh:
    for line in fh:
        lg = _json.loads(line)
        layout[lg["topics"][0]].add((len(lg["topics"]), len(lg["data"])))
        if lg["topics"][0] == UPG:
            blk = lg["blockNumber"]
            blk = int(blk, 16) if isinstance(blk, str) else blk
            name = bytes.fromhex(lg["data"][2:66]).rstrip(b"\0").decode()
            upgrades.append((blk, name))
up_by = collections.Counter(n for _, n in upgrades)
varying = [t for t, v in layout.items() if len(v) > 1]
last_credit_up = max(b for b, n in upgrades if n == "BCredit")
last_any_up = max(b for b, _ in upgrades)
regime = {h: [e for e in rep_events if (e["block"] > last_credit_up) == h] for h in (False, True)}
credit_after = sum(1 for e in evs if e["event"] in CREDIT and e["block"] > last_any_up)
credit_all = sum(1 for e in evs if e["event"] in CREDIT)
# (f) base rate: the share of week-long windows, at any date in the sample, in which the same account sells
F0 = meta["from_block"]


def sale_window_share(key):
    """Exact share of start blocks b in [F0, END - WEEK] with a sale by the account in (b, b + WEEK]."""
    ivs = sorted((max(F0, x["block"] - WEEK), min(END - WEEK, x["block"] - 1)) for x in by_acct[key]
                 if x["event"] == "Swap" and x["bTokenDelta"] < 0)
    covered, hi = 0, F0 - 1
    for lo_, hi_ in ivs:
        if hi_ < lo_:
            continue
        lo_ = max(lo_, hi + 1)
        if hi_ >= lo_:
            covered += hi_ - lo_ + 1
            hi = hi_
    return covered / (END - WEEK - F0 + 1)


base_rate = sum(per_acct[k] * sale_window_share(k) for k in per_acct) / len(rep_events)
# (g) full against partial repayments; without the ONYX pool
full_r = [e for e in rep_events if e["debt"] == 0]
part_r = [e for e in rep_events if e["debt"] != 0]
no_onyx = [e for e in rep_events if sym_of[e["bToken"]] != "ONYX"]
# (h) resampling addresses (an address can hold accounts in several pools)
by_addr = collections.defaultdict(list)
for e in rep_events:
    by_addr[e["user"]].append(followed_by_sale(e))
addr_clusters = list(by_addr.values())
_rng2 = _random.Random(2027)
boot2 = []
for _ in range(10_000):
    draw = [addr_clusters[_rng2.randrange(len(addr_clusters))] for _ in addr_clusters]
    boot2.append(sum(map(sum, draw)) / sum(map(len, draw)))
boot2.sort()
ci2_lo, ci2_hi = boot2[249], boot2[9749]
# (i) survival of the first episode of each new account
first_spells = [(days(b0, b1), True) if b1 is not None else (days(b0, END), False) for b0, b1 in first_ep.values()]
print("\n== heterogeneity, uncertainty, upgrades")
for k, r in pool_rep.items():
    print(f"  plain repayments in {k}: {r['n']} by {len(r['accts'])} accounts, {r['sold']} followed by a sale")
for h in (False, True):
    print(f"  {'second' if h else 'first'} half of the window: {len(half[h])} repayments, "
          f"{sum(map(followed_by_sale, half[h]))} followed by a sale")
print(f"  share followed by a sale, 95% interval from 10,000 resamples of {len(clusters)} accounts: "
      f"{ci_lo:.4f} to {ci_hi:.4f}")
print(f"  episodes at risk at 30/90/180 days: {at_risk}; closures after day 180: {late_closes}")
print(f"  base rate: share of week-long windows with a sale by the same account, weighted by repayments: {base_rate:.4f}")
print(f"  full repayments followed by a sale: {sum(map(followed_by_sale, full_r))} of {len(full_r)}; "
      f"partial: {sum(map(followed_by_sale, part_r))} of {len(part_r)}; "
      f"without ONYX: {sum(map(followed_by_sale, no_onyx))} of {len(no_onyx)}")
print(f"  95% interval from 10,000 resamples of {len(addr_clusters)} addresses: {ci2_lo:.4f} to {ci2_hi:.4f}")
print(f"  first episodes only, share still open at 30/90/180 days: "
      f"{kaplan_meier(first_spells, 30):.4f} {kaplan_meier(first_spells, 90):.4f} {kaplan_meier(first_spells, 180):.4f}")
print(f"  upgrades by component: {dict(up_by)}; blocks {sorted({b for b, _ in upgrades})}")
print(f"  event types whose log layout varies in the sample: {len(varying)} (CreditClaim, the carry-over event at launch, whose data are arrays)")
for h in (False, True):
    print(f"  {'after' if h else 'up to'} the last upgrade of the credit component (block {last_credit_up}): "
          f"{len(regime[h])} repayments, {sum(map(followed_by_sale, regime[h]))} followed by a sale")
print(f"  credit events after the last upgrade of any component: {credit_after} of {credit_all}")

# ---------------------------------------------------------------- LaTeX output
B = next(r for r in rows if r["sym"] == "B")
EL = next(r for r in rows if r["sym"] == "ELEFENT")


def num(x, nd=0):
    return f"{x:,.{nd}f}".replace(",", "{,}")


def pct(x, nd=0):
    return f"{100 * x:.{nd}f}"


shares = sorted(r["share"] for r in rows)
M = {
    "ELogs": num(meta["n_logs"]), "EDays": num(span), "EEndBlock": num(END),
    "EStartBlock": num(meta["from_block"]), "EPools": str(len(rows)),
    "EUpgrades": num(meta["ignored_events"].get("ComponentUpgraded", 0)),
    "EBorrow": num(tot["Borrow"]), "ELeverage": num(tot["Leverage"]), "ERepay": num(tot["Repay"]),
    "EDeleverage": num(tot["Deleverage"]), "ESwap": num(tot["Swap"]),
    "EReduce": num(reduce_n), "EDelevPct": pct(tot["Deleverage"] / reduce_n),
    "EFullDelev": num(full_delev), "EFullRepay": num(full_repay),
    "ESoldHour": num(repay_cls["sold_hour"]), "ESoldWeek": num(repay_cls["sold_week"]),
    "ESoldBeforeHour": num(repay_cls["sold_before_hour"]),
    "ECatSold": num(repay_cls["cat_sold"]), "ECatReborrow": num(repay_cls["cat_reborrow"]),
    "ECatNeither": num(repay_cls["cat_neither"]), "EReborrowAny": num(repay_cls["reborrow_any"]),
    "ERepaySoldPct": pct(repay_cls["sold_week"] / tot["Repay"]),
    "ETopTwoEvents": num(top2_events), "ETopTwoPct": pct(top2_events / tot["Repay"]),
    "ERestSold": num(rest_sold), "ERestN": num(len(rest)), "ERestPct": pct(rest_sold / len(rest)),
    "EAmtSoldPct": pct(amt_sold / amt_total),
    "ELeverAmtPct": pct(amt_lever / (amt_borrow + amt_lever)),
    "EAmtBorrow": num(amt_borrow / E18, 1), "EAmtLever": num(amt_lever / E18, 1),
    "EKMThirty": pct(kaplan_meier(spells, 30)), "EKMNinety": pct(kaplan_meier(spells, 90)),
    "EKMHalfYear": pct(kaplan_meier(spells, 180)),
    "EKMRiskThirty": num(at_risk[30]), "EKMRiskNinety": num(at_risk[90]), "EKMRiskHalfYear": num(at_risk[180]),
    "EKMLateCloses": num(late_closes),
    "EBaseRate": pct(base_rate, 1), "EFullRepSold": num(sum(map(followed_by_sale, full_r))), "EFullRepN": num(len(full_r)),
    "EPartRepSold": num(sum(map(followed_by_sale, part_r))), "EPartRepN": num(len(part_r)),
    "ENoOnyxSold": num(sum(map(followed_by_sale, no_onyx))), "ENoOnyxN": num(len(no_onyx)),
    "EAddrClusters": num(len(addr_clusters)), "EAddrCILo": pct(ci2_lo), "EAddrCIHi": pct(ci2_hi),
    "EKMFirstThirty": pct(kaplan_meier(first_spells, 30)), "EKMFirstNinety": pct(kaplan_meier(first_spells, 90)),
    "EKMFirstHalfYear": pct(kaplan_meier(first_spells, 180)),
    "ERepayCILo": pct(ci_lo), "ERepayCIHi": pct(ci_hi), "ERepayClusters": num(len(clusters)),
    "EHalfOneN": num(len(half[False])), "EHalfOneSold": num(sum(map(followed_by_sale, half[False]))),
    "EHalfTwoN": num(len(half[True])), "EHalfTwoSold": num(sum(map(followed_by_sale, half[True]))),
    "EUpCredit": num(up_by["BCredit"]), "EUpSwap": num(up_by["BSwap"]), "EUpLens": num(up_by["BLens"]),
    "EUpController": num(up_by["BController"]), "EUpFactory": num(up_by["BFactory"]),
    "EUpDates": num(len({b for b, _ in upgrades})), "EUpLastCredit": num(last_credit_up),
    "ERegOneN": num(len(regime[False])), "ERegOneSold": num(sum(map(followed_by_sale, regime[False]))),
    "ERegTwoN": num(len(regime[True])), "ERegTwoSold": num(sum(map(followed_by_sale, regime[True]))),
    "ECreditAfterUp": num(credit_after), "ECreditAll": num(credit_all),
    "EOnyxLensTotal": num(next(r for r in rows if r["sym"] == "ONYX")["lens_total"] / E18),
    "EOnyxErcTotal": num(next(r for r in rows if r["sym"] == "ONYX")["erc_total"] / E18),
    "EOnyxCirc": num(next(r for r in rows if r["sym"] == "ONYX")["circ"] / E18),
    "EOnyxShareErc": pct(next(r for r in rows if r["sym"] == "ONYX")["share_erc20"]),
    "EOnyxOff": num(next(r for r in rows if r["sym"] == "ONYX")["off_chain"] / E18),
    "EFloorEndSame": str(sum(1 for r in rows if r["floor_end_same"])),
    "EElFloorEndPct": f"{100 * (EL['floor_ratio'] and EL['floor_end_ratio'] - 1):.1f}",
    "EMaxSwapGap": num(max(r["last_swap_days"] for r in rows)),
    "ELinked": num(linked), "ELinkedPct": pct(linked / reduce_n),
    "ERepayAccts": num(len(repay_accts)), "EAcctSoldAfter": num(acct_sold_after),
    "ENeverReduced": num(len(never_reduced)), "ENeverReducedSold": num(nr_sold),
    "ENeverReducedSoldPct": pct(nr_sold / len(never_reduced), 1),
    "ESnap": num(tot["snap"]), "ESnapOpen": num(tot["snap_open"]),
    "ESnapOpenPct": pct(tot["snap_open"] / tot["snap"]),
    "ESnapSame": num(tot["snap_same"]), "ESnapSamePct": pct(tot["snap_same"] / tot["snap"]),
    "EActive": num(tot["active"]), "EActiveClosed": num(tot["active_closed"]),
    "EActiveClosedPct": pct(tot["active_closed"] / tot["active"]),
    "ENewAccts": num(len(new_accts)), "EEpisodes": num(len(episodes)),
    "EEpLeverage": num(ep_kind["Leverage"]), "EEpBorrow": num(ep_kind["Borrow"]),
    "EEpClosed": num(len(ep_closed)), "EEpOpen": num(len(ep_open)),
    "EEpClosedThirty": num(sum(1 for a in ep_closed if a <= 30)),
    "EFirstClosed": num(len(first_closed)), "EFirstClosedThirty": num(sum(1 for a in first_closed if a <= 30)),
    "EAcctsShort": num(accts_short),
    "EEpMedianClose": f"{med(ep_closed):.1f}", "EEpMedianOpenAge": f"{med(ep_open):.0f}",
    "EFeeMedian": f"{100 * med(fees):.2f}",
    "EBShare": pct(B["share"]), "EBLtv": pct(B["ltv"], 1), "EBOpen": num(B["open"]),
    "EBPremFirst": f"{B['prem0']:.2f}", "EBPremLast": f"{B['prem1']:.2f}",
    "EShareMin": pct(shares[0]), "EShareMax": pct(shares[-1]),
    "EFlatPools": str(sum(1 for r in rows if r["floor_changes"] == 0)),
    "EElChanges": num(EL["floor_changes"]), "EElRatio": f"{EL['floor_ratio']:.1f}",
    "EElLtv": pct(EL["ltv"]), "EElAccounts": num(EL["accounts"]), "EElOpen": num(EL["open"]),
    "EHourBlocks": num(HOUR), "EWeekBlocks": num(WEEK),
}
lines = ["% generated by empirics/analyze.py -- do not edit"]
lines += ["\\newcommand{\\%s}{%s}" % kv for kv in M.items()]
tab = [f"{r['sym']} & {num(r['accounts'])} & {num(r['open'])} & {pct(r['share'])}\\% & {pct(r['ltv'], 1)}\\% & "
       f"{r['prem0']:.2f} & {r['prem1']:.2f} & {num(r['floor_changes'])} & {num(r['snap'])} & {num(r['snap_open'])} & "
       f"{num(r['inc'])} & {num(r['repay'])} & {num(r['delev'])}\\\\" for r in rows]
lines.append("\\newcommand{\\EPoolRows}{%\n" + "\n".join(tab) + "}")
order = [r["sym"] for r in rows if r["sym"] in pool_rep]
rtab = [f"{k} & {pool_rep[k]['n']} & {len(pool_rep[k]['accts'])} & {pool_rep[k]['sold']}\\\\" for k in order]
lines.append("\\newcommand{\\ERepayPoolRows}{%\n" + "\n".join(rtab) + "}")
out = os.path.join(HERE, "..", "sections", "empnums.tex")
open(out, "w").write("\n".join(lines) + "\n")
print("wrote sections/empnums.tex")
