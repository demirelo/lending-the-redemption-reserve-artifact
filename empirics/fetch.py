"""Fetch all event logs of the Baseline Mercury singleton on Ethereum mainnet.

Public data only, no API key. Usage:
    python3 -I empirics/fetch.py            # fetch up to the current head (minus 64 blocks) and pin it
    python3 -I empirics/fetch.py 26414000   # fetch up to a given block (to reproduce the paper's dataset)

Writes empirics/data/logs_eth.jsonl (one raw log per line, sorted) and
empirics/data/meta.json (block range, anchor timestamps, token supplies).
"""
import json
import os
import sys
import time
import urllib.request

RPC = "https://gateway.tenderly.co/public/mainnet"
SINGLETON = "0xc81Fd894C0acE037d133aF4886550aC8133568E8"
DEPLOY_BLOCK = 24_915_618
CHUNK = 250_000
HERE = os.path.dirname(os.path.abspath(__file__))


def rpc(method, params, tries=6):
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": method, "params": params}).encode()
    for k in range(tries):
        try:
            req = urllib.request.Request(RPC, data=body, headers={"content-type": "application/json",
                                                                  "user-agent": "research-script"})
            with urllib.request.urlopen(req, timeout=60) as r:
                out = json.loads(r.read())
            if "result" in out:
                return out["result"]
            err = out.get("error")
        except Exception as e:  # network error or throttling
            err = repr(e)
        time.sleep(2 + 3 * k)
    raise RuntimeError(f"{method} failed: {err}")


def block_time(n):
    return int(rpc("eth_getBlockByNumber", [hex(n), False])["timestamp"], 16)


def call(to, data, block):
    return rpc("eth_call", [{"to": to, "data": data}, hex(block)])


def main():
    end = int(sys.argv[1]) if len(sys.argv) > 1 else int(rpc("eth_blockNumber", []), 16) - 64
    logs = []
    lo = DEPLOY_BLOCK
    while lo <= end:
        hi = min(lo + CHUNK - 1, end)
        part = rpc("eth_getLogs", [{"address": SINGLETON, "fromBlock": hex(lo), "toBlock": hex(hi)}])
        logs += part
        print(f"blocks {lo}-{hi}: {len(part)} logs", flush=True)
        lo = hi + 1
        time.sleep(1.0)
    logs.sort(key=lambda l: (int(l["blockNumber"], 16), int(l["logIndex"], 16)))
    os.makedirs(os.path.join(HERE, "data"), exist_ok=True)
    with open(os.path.join(HERE, "data", "logs_eth.jsonl"), "w") as fh:
        for l in logs:
            fh.write(json.dumps({k: l[k] for k in ("address", "blockNumber", "blockHash", "transactionHash",
                                                   "transactionIndex", "logIndex", "topics", "data")}) + "\n")
    # anchor timestamps for converting blocks to time (12-second slots; linear interpolation)
    anchors = {}
    for b in sorted(set([DEPLOY_BLOCK, end] + list(range(DEPLOY_BLOCK, end, 200_000)))):
        anchors[b] = block_time(b)
        time.sleep(0.3)
    meta = {"rpc": RPC, "singleton": SINGLETON, "from_block": DEPLOY_BLOCK, "to_block": end,
            "n_logs": len(logs), "anchors": anchors}
    json.dump(meta, open(os.path.join(HERE, "data", "meta.json"), "w"), indent=1)
    print("total logs", len(logs), "end block", end)


if __name__ == "__main__":
    main()
