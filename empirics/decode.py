"""Decode Baseline Mercury event logs (public SDK event definitions, see empirics/abi)."""
import json
import os

HERE = os.path.dirname(os.path.abspath(__file__))
T = {
    "0x36f3eae349acbc4d07973448b29421cdb622c336e7ea546ca6c4e38db77c890f": "Borrow",
    "0xda0dc32c1e3ca53ee9f27754d750edeacdf7573f052ea74ef01fd49d53ff20da": "Repay",
    "0x7dac1603a55d3840464c24d4931c43e563ca19429b7ae765e819941f7bb87837": "Leverage",
    "0x74bcb77fb25b1f5c24bff03370cb1f154a97999cd5bda7a903903d2cc08d8b70": "Deleverage",
    "0x5ae03fd0a09fe0fbbf66ab0e6e545fb76c14a16e40e763d0ab59a1ef511328ee": "CreditClaim",
    "0xa98f07efc4d0a837f30fe354a44231615ea1ef631a52a1c83fa7c19b5128dd0f": "Swap",
    "0x5fc70f0171c90baf6cad0d4f6218b5213a5bba33199aec219a77980c50e4d81b": "Deposit",
    "0xef2d1a64c29adde93d1a73995196cf50480e699e19ac7a07be2898bdff189ce8": "Withdraw",
    "0x6b40d9ac9d9dcc4ba6477664fdae5809a701208c8db1cbb7bc759993691146a9": "Initialized",
    "0xc64b6267fa6fd0d6338cf97dc012b1d1ce8a0504a2f40d5099afd8dd1810f2b8": "Liquidate",
    "0x70eb43c4a8ae8c40502dcf22436c509c28d6ff421cf07c491be56984bd987068": "Claim",
}
# Event types that carry no account-level information used in the analysis.
IGNORED = {
    "0x45e202d2d36c7846d6d53971ffe792d5dace4037c9af46b384a71d72e8761884": "Distributed",
    "0x916d60cf5360c058722c013df4e95816ae5ddf71f4c218eb89d1afb76e047bb8": "FeesClaimed",
    "0x28dfb2e3cc3e295eff8199284d79be6ddc49171b1382fda8dd2ee934ed923483": "PoolCreated",
    "0x5c088440a5ebbf647b6d40edac901a3319ab1219de322aadcd5e7046e0a2eab8": "BTokenCreated",
    "0x92d95d1d10106a45a636985bb95ad6f1ab3f36b8e046fa1d4263e1b99f4485f9": "ApprovedCreditDeployerSet",
    "0xd16790ba2e13960877459a2a4bc08c1567ddb3173d27536ebae2ec10845a6a80": "CreatorFeePctSet",
    "0x7f11fe0c7098e1a76afcc68f35abaa07ef156fa7d6dd2d39664812fe37348d16": "CreatorTransferred",
    "0x68ee1155c717cb6687be9b69fb1836837e8faf8242e173193101016ae51580a2": "DeployerProfileSet",
    "0x9f00477a7224dd6a6a421b4d1b36201ecc8f7396e3d2125129db5f6898bc37ba": "DeployerSet",
    "0x15d80a013f22151bc7246e3bc132e12828cde19de98870475e3fa70840152721": "FeeRecipientSet",
    "0xce517016a528bad743e1b1b056ff7a110c11984b45f33649757bf9db16523cd6": "LiquidityFeePctSet",
    "0x364512939b35c3636a04fc2ea0d7dff51e8efc42e9833230796ab002661e2e18": "ReserveApproved",
    # administrative events of the upgradeable system (signatures from a public signature database)
    "0xe22b4f506b7da9a528a95d7063a6cde8d2b6268773b1f7f65c00057531704a3d": "AdminTransferred",
    "0xcfa6fb7a59d2f180dc7624ee733c7498c87bef80055a9964fb0fa01cd9d66d6b": "PendingAdminSet",
    "0x711f5951fc7eae49a80da326fd7838ea68d291d9bbb945b0a79587f1b501fff3": "ComponentAdded",
    "0x198aeafd78956c82987d6b6e05441c98958e51bf483fa75b0a65babd3483dfcb": "ComponentUpgraded",
    "0xf4a2c6ec5a0e21aa20718af4e7fda67e851123508139ad1d2b93e974ce0d04b3": "ExecutorAdded",
    # DeployerProfileSet(address,(bool,bool,bool,uint64,uint64,bool)): a later ABI version of the
    # deployer-profile event (six profile fields; SDK 1.3.0 lists five). One log.
    "0xdbc827ce45c8b878f107fc94e5364df9eb86b769101c033a92774d5cdbf5aad2": "DeployerProfileSet(v2)",
    # One log at block 24,920,874 whose signature we could not identify; its data is a single
    # address. It is excluded from the analysis.
    "0x64a7542d85d9fadc270a1478ad4484f92bceb67e61bcc9e3d0c9af5915d0d8db": "unidentified",
}
FIELDS = {
    "Borrow": ["bToken:a", "user:a", "borrowed:u", "fee:u", "collateral:u", "debt:u"],
    "Repay": ["bToken:a", "user:a", "collateralRedeemed:u", "debtRepaid:u", "collateral:u", "debt:u"],
    "Leverage": ["bToken:a", "user:a", "collateralAdded:u", "debtAdded:u", "collateralIn:u",
                 "reservesIn:u", "collateral:u", "debt:u"],
    "Deleverage": ["bToken:a", "user:a", "collateralRedeemed:u", "debtRepaid:u", "collateralSold:u",
                   "refund:u", "collateral:u", "debt:u"],
    "Swap": ["bToken:a", "user:a", "activePrice:u", "blvPrice:u", "bTokenDelta:i", "reserveDelta:i",
             "totalFee:u", "liquidityFee:u"],
    "Deposit": ["bToken:a", "user:a", "amount:u"],
    "Withdraw": ["bToken:a", "user:a", "amount:u"],
    "Liquidate": ["bToken:a", "user:a", "amount:u"],   # stake removed when collateral is sold
    "Claim": ["bToken:a", "user:a", "amount:u"],       # reward claim
    "Initialized": ["bToken:a", "activePrice:u", "blvPrice:u", "swapFeePct:u"],
}


def words(data):
    h = data[2:]
    return [h[i:i + 64] for i in range(0, len(h), 64)]


def conv(w, kind):
    v = int(w, 16)
    if kind == "a":
        return "0x" + w[24:]
    if kind == "i" and v >= 1 << 255:
        v -= 1 << 256
    return v


def decode(log):
    name = T.get(log["topics"][0])
    if name is None:
        return None
    ev = {"event": name, "block": int(log["blockNumber"], 16), "idx": int(log["logIndex"], 16),
          "tx": log["transactionHash"]}
    w = words(log["data"])
    if name == "CreditClaim":
        ev["bToken"] = conv(w[0], "a")
        arrs = []
        for k in (1, 2, 3):                      # three dynamic arrays
            off = int(w[k], 16) // 32
            n = int(w[off], 16)
            arrs.append(w[off + 1: off + 1 + n])
        ev["users"] = [conv(x, "a") for x in arrs[0]]
        ev["collaterals"] = [int(x, 16) for x in arrs[1]]
        ev["debts"] = [int(x, 16) for x in arrs[2]]
        assert len(ev["users"]) == len(ev["collaterals"]) == len(ev["debts"])
        return ev
    for i, f in enumerate(FIELDS[name]):
        key, kind = f.split(":")
        ev[key] = conv(w[i], kind)
    return ev


def load():
    evs, unknown = [], {}
    with open(os.path.join(HERE, "data", "logs_eth.jsonl")) as fh:
        for line in fh:
            log = json.loads(line)
            e = decode(log)
            if e:
                evs.append(e)
            elif log["topics"][0] not in IGNORED:
                unknown[log["topics"][0]] = unknown.get(log["topics"][0], 0) + 1
    # every log must be either decoded or explicitly ignored
    assert not unknown, f"undecoded event types: {unknown}"
    meta_extra = {}
    with open(os.path.join(HERE, "data", "logs_eth.jsonl")) as fh:
        for line in fh:
            t = json.loads(line)["topics"][0]
            if t in IGNORED:
                meta_extra[IGNORED[t]] = meta_extra.get(IGNORED[t], 0) + 1
    meta = json.load(open(os.path.join(HERE, "data", "meta.json")))
    meta["ignored_events"] = meta_extra
    return evs, meta
