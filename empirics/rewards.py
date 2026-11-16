"""Reconstruct fee allocations and reward claims from the supplied Baseline logs.

Usage: python3 -I empirics/rewards.py
Prints a report and writes sections/rewardnums.tex. No network or packages.

The ABI JSON files define the decoded fields; mercury_event_topics.txt supplies
their recorded topic hashes. Amounts remain integer reserve units until display.
This is an allocation ledger, not account earnings, investment returns or yield.
"""

import collections
import json
from decimal import Decimal
from pathlib import Path


HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
UNIT = 10**18                 # the common reserve asset is WETH
NAMES = {"Distributed", "Borrow", "Leverage", "Swap", "Claim"}
AMOUNTS = ("totalAmount", "protocolFee", "creatorFee", "stakingFee")


def abi_type(field):
    """Type spelling in the supplied topic manifest, including static tuples."""
    if field["type"] == "tuple":
        return "(" + ",".join(abi_type(x) for x in field["components"]) + ")"
    return field["type"]


def manifest_signature(event):
    return event["name"] + "(" + ", ".join(
        abi_type(x) + " " + x["name"] for x in event["inputs"]) + ")"


def load_definitions():
    definitions = {}
    for filename in ("mercury_bCredit.json", "mercury_bSwap.json", "mercury_bStaking.json"):
        for item in json.loads((HERE / "abi" / filename).read_text()):
            if item.get("type") == "event" and item["name"] in NAMES:
                assert not item["anonymous"]
                old = definitions.setdefault(item["name"], item)
                assert old == item, "conflicting ABI definitions"
    assert set(definitions) == NAMES
    topics = {}
    for line in (HERE / "abi" / "mercury_event_topics.txt").read_text().splitlines():
        if not line.startswith("0x"):
            continue
        topic, signature = line.split(" ", 1)
        name = signature.split("(", 1)[0]
        if name in NAMES:
            assert signature == manifest_signature(definitions[name])
            old = topics.setdefault(topic, definitions[name])
            assert old == definitions[name]
    assert {x["name"] for x in topics.values()} == NAMES
    return topics


def static_value(field, data, pos):
    """Decode precisely the static ABI types used by the five selected events."""
    kind = field["type"]
    if kind == "tuple":
        value = {}
        for component in field["components"]:
            value[component["name"]], pos = static_value(component, data, pos)
        return value, pos
    assert pos < len(data), "short ABI payload"
    word = int(data[pos], 16)
    if kind == "address":
        assert word < 2**160, "noncanonical address"
        return f"0x{word:040x}", pos + 1
    if kind.startswith("uint"):
        assert word < 2 ** int(kind[4:]), "noncanonical unsigned integer"
        return word, pos + 1
    if kind == "int256":
        return word - 2**256 if word >= 2**255 else word, pos + 1
    raise ValueError("unsupported ABI type: " + kind)


def decode(log, definition):
    assert len(log["topics"]) == 1, "unexpected indexed fields"
    payload = log["data"][2:]
    assert len(payload) % 64 == 0, "misaligned ABI payload"
    data = [payload[i:i + 64] for i in range(0, len(payload), 64)]
    event = {"event": definition["name"], "tx": log["transactionHash"],
             "idx": int(log["logIndex"], 16), "block": int(log["blockNumber"], 16)}
    pos = 0
    for field in definition["inputs"]:
        assert not field["indexed"]
        event[field["name"]], pos = static_value(field, data, pos)
    assert pos == len(data), "unexpected trailing ABI fields"
    return event


def expected_distribution(event):
    """Accounting amount to match; a match does not identify a fee beneficiary."""
    if event["event"] == "Borrow":
        return event["fee"]
    if event["event"] == "Leverage":
        return event["debtAdded"] - event["reservesIn"]
    if event["event"] == "Swap":
        return event["totalFee"] - event["liquidityFee"]
    raise ValueError("not a candidate fee source")


def totals(events):
    return {key: sum(event[key] for event in events) for key in AMOUNTS}


def amount(value, places=6):
    return f"{Decimal(value) / UNIT:.{places}f}"


def count(value):
    return f"{value:,}".replace(",", "{,}")


def main():
    definitions = load_definitions()
    raw = [json.loads(line) for line in (HERE / "data" / "logs_eth.jsonl").read_text().splitlines()]
    meta = json.loads((HERE / "data" / "meta.json").read_text())
    endpoint = json.loads((HERE / "data" / "endpoint.json").read_text())
    supply = json.loads((HERE / "data" / "supply.json").read_text())
    assert len(raw) == meta["n_logs"]
    assert endpoint["block"] == meta["to_block"]
    keys = [(int(x["blockNumber"], 16), int(x["logIndex"], 16)) for x in raw]
    assert keys == sorted(keys) and len(keys) == len(set(keys))
    assert all(meta["from_block"] <= b <= meta["to_block"] for b, _ in keys)
    assert all(x["address"].lower() == meta["singleton"].lower() for x in raw)
    events = [decode(x, definitions[x["topics"][0]]) for x in raw if x["topics"][0] in definitions]
    distributions = [x for x in events if x["event"] == "Distributed"]
    claims = [x for x in events if x["event"] == "Claim"]
    # These counts identify the paper's pinned sample, not a generic future sample.
    assert len(distributions) == 2233 and len(claims) == 173
    assert all(x["totalAmount"] == x["protocolFee"] + x["creatorFee"] + x["stakingFee"]
               for x in distributions), "allocation components do not reconcile"
    reserve_ids = {int(endpoint["pools"][t]["reserve"]) for t in supply}
    assert len(reserve_ids) == 1
    assert all(x["bToken"] in supply and int(x["reserve"], 16) in reserve_ids for x in distributions)

    # A source must be the next Borrow/Leverage/Swap in the SAME transaction and
    # pool, and its accounting amount must agree exactly. Each source can be
    # matched once only. Records without such a match remain unassigned.
    candidates = collections.defaultdict(list)
    for event in events:
        if event["event"] in {"Borrow", "Leverage", "Swap"}:
            assert expected_distribution(event) >= 0
            candidates[(event["tx"], event["bToken"])].append(event)
    proposed = collections.defaultdict(list)
    for distribution in distributions:
        later = [x for x in candidates[(distribution["tx"], distribution["bToken"])]
                 if x["idx"] > distribution["idx"]]
        if later and expected_distribution(later[0]) == distribution["totalAmount"]:
            source = later[0]
            proposed[(source["tx"], source["idx"])].append((distribution, source))
    matched = {}
    for pairs in proposed.values():
        if len(pairs) == 1:
            distribution, source = pairs[0]
            matched[(distribution["tx"], distribution["idx"])] = source["event"]
    by_origin = collections.defaultdict(list)
    for distribution in distributions:
        origin = matched.get((distribution["tx"], distribution["idx"]), "Unassigned")
        by_origin[origin].append(distribution)
    grand = totals(distributions)
    assert all(sum(totals(xs)[key] for xs in by_origin.values()) == grand[key] for key in AMOUNTS)
    # Independent reconciliation against the fee-bearing event fields. This
    # checks that the matching neither drops nor duplicates a recorded source.
    for origin in ("Borrow", "Leverage", "Swap"):
        fee_events = [x for x in events if x["event"] == origin]
        assert len(by_origin[origin]) == len(fee_events), "a fee source is unmatched"
        assert totals(by_origin[origin])["totalAmount"] == sum(map(expected_distribution, fee_events))

    print("command: python3 -I empirics/rewards.py")
    print(f"sample: blocks {meta['from_block']}-{meta['to_block']}; {len(raw)} raw logs")
    print(f"ABI-decoded: {len(distributions)} distributions; {len(claims)} reward claims")
    print("checks: each allocation identity, one reserve asset, unique ordered logs, "
          "one-to-one source matching, independent source-fee sums: PASS")
    print("amounts below are WETH; raw-unit totals are integers")
    print("pool     records       total    protocol     creator     staking     claimed")
    rows = []
    pool_sums = {key: 0 for key in AMOUNTS}
    for token, token_info in supply.items():
        xs = [x for x in distributions if x["bToken"] == token]
        row = totals(xs)
        paid = sum(x["amount"] for x in claims if x["bToken"] == token)
        for key in AMOUNTS:
            pool_sums[key] += row[key]
        print(f"{token_info['symbol']:8s} {len(xs):7d} " +
              " ".join(f"{amount(row[key]):>11s}" for key in AMOUNTS) + f" {amount(paid):>11s}")
        rows.append(token_info["symbol"] + " & " + " & ".join(
            amount(row[key], 4) for key in AMOUNTS) + " & " + amount(paid, 4) + r"\\")
    assert pool_sums == grand
    claimed = sum(x["amount"] for x in claims)
    print("TOTAL            " + " ".join(f"{amount(grand[key]):>11s}" for key in AMOUNTS) +
          f" {amount(claimed):>11s}")
    print("allocation totals in raw units:", json.dumps(grand, sort_keys=True))
    print("claim total in raw units:", claimed)
    print("source        records       allocated         staking")
    for origin in ("Borrow", "Leverage", "Swap", "Unassigned"):
        row = totals(by_origin[origin])
        print(f"{origin:13s} {len(by_origin[origin]):7d} " +
              f"{amount(row['totalAmount'], 18):>24s} {amount(row['stakingFee'], 18):>24s}")
    print("interpretation: allocations are recorded fee destinations; claims are separate events.")
    print("No subtraction of claims from allocations is an estimate of unclaimed earnings. "
          "Opening accruals, user histories and reward-accounting semantics are not reconstructed.")
    print("Unassigned distributions retain their measured allocations but receive no inferred source.")

    credit = by_origin["Borrow"] + by_origin["Leverage"]
    macros = {
        "RNDistributions": count(len(distributions)), "RNClaims": count(len(claims)),
        "RTotal": amount(grand["totalAmount"], 4),
        "RProtocol": amount(grand["protocolFee"], 4),
        "RCreator": amount(grand["creatorFee"], 4),
        "RStaking": amount(grand["stakingFee"], 4), "RClaimed": amount(claimed, 4),
        "RCreditN": count(len(credit)), "RCreditTotal": amount(totals(credit)["totalAmount"], 4),
        "RCreditStaking": amount(totals(credit)["stakingFee"], 4),
        "RSwapN": count(len(by_origin["Swap"])),
        "RSwapTotal": amount(totals(by_origin["Swap"])["totalAmount"], 4),
        "RUnassignedN": count(len(by_origin["Unassigned"])),
        "RUnassignedTotal": amount(totals(by_origin["Unassigned"])["totalAmount"], 10),
    }
    rows.append(r"\midrule" + "\nTotal & " + " & ".join(amount(grand[key], 4) for key in AMOUNTS)
                + " & " + amount(claimed, 4) + r"\\")
    lines = ["% generated by empirics/rewards.py -- do not edit"]
    lines += ["\\newcommand{\\" + key + "}{" + value + "}" for key, value in macros.items()]
    lines.append(r"\newcommand{\RPoolRows}{%" + "\n" + "\n".join(rows) + "}")
    (ROOT / "sections" / "rewardnums.tex").write_text("\n".join(lines) + "\n")
    print("wrote sections/rewardnums.tex")


if __name__ == "__main__":
    main()
