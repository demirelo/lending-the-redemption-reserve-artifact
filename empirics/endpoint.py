"""Read the state of every pool from the contract at the last block of the sample.

Usage: python3 -I empirics/endpoint.py   (after fetch.py; writes empirics/data/endpoint.json)

The selectors are those of the read-only functions in the project's public
software kit (version 1.3.0): blvPrice, activePrice, totalDebt, totalCollateral,
totalStaked, getCirculatingSupply, totalSupply, swapFee, reserve, each with one address
argument, and originationFee(). All values are stored as raw integer strings.
"""
import json
import os
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
from fetch import rpc, SINGLETON  # noqa: E402
from decode import load  # noqa: E402

SEL = {"blvPrice": "0x158b852a", "activePrice": "0x400fd013", "totalDebt": "0x1ff517ff",
       "totalCollateral": "0x7e059b22", "totalStaked": "0x9bfd8d61",
       "getCirculatingSupply": "0x1585a1e3", "totalSupply": "0xe4dc2aa4", "swapFee": "0xa6ae80e2",
       "reserve": "0xe75179a4"}

evs, meta = load()
end = meta["to_block"]
out = {"block": end, "originationFee": str(int(rpc("eth_call", [{"to": SINGLETON, "data": "0xb8bb5c42"}, hex(end)]), 16)),
       "pools": {}}
for tok in [e["bToken"] for e in evs if e["event"] == "Initialized"]:
    row = {}
    for name, sel in SEL.items():
        res = rpc("eth_call", [{"to": SINGLETON, "data": sel + tok[2:].rjust(64, "0")}, hex(end)])
        row[name] = str(int(res, 16))
        time.sleep(0.25)
    out["pools"][tok] = row
    print(tok, row)
json.dump(out, open(os.path.join(HERE, "data", "endpoint.json"), "w"), indent=1)
