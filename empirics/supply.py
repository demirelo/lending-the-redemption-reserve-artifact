"""Read token supplies and the contract's token balances onchain at the first and last block.

Usage: python3 -I empirics/supply.py   (after fetch.py; writes empirics/data/supply.json)
"""
import sys, json, time
import os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fetch import rpc, SINGLETON
from decode import load
evs,meta=load()
end=meta['to_block']
toks=[e['bToken'] for e in evs if e['event']=='Initialized']
out={}
for t in toks:
    row={}
    for name,blk in (('start',[e['block'] for e in evs if e['event']=='Initialized' and e['bToken']==t][0]+5),('end',end)):
        ts=int(rpc('eth_call',[{'to':t,'data':'0x18160ddd'},hex(blk)]),16)
        bal=int(rpc('eth_call',[{'to':t,'data':'0x70a08231'+SINGLETON[2:].lower().rjust(64,'0')},hex(blk)]),16)
        row[name]=(str(ts),str(bal)); time.sleep(0.4)   # raw integers (18 decimals), as strings
    sym=bytes.fromhex(rpc('eth_call',[{'to':t,'data':'0x95d89b41'},hex(end)])[2:]).replace(b'\x00',b'').decode(errors='ignore').strip()
    row['symbol']=''.join(ch for ch in sym if ch.isalnum())
    row['decimals']=int(rpc('eth_call',[{'to':t,'data':'0x313ce567'},hex(end)]),16)
    out[t]=row; print(t,row)
json.dump(out,open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'data','supply.json'),'w'),indent=1)
