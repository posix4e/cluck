"""What a round costs outside the guest's own work: for each slot of a shadow log, the host's time for
asking the guest (request there, block built, answer back) beside the guest's own account of its work
from its console. Usage: intake.py RUN.jsonl"""
import json, re, sys, statistics as st
rows = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
own = []
for line in open(sys.argv[1] + ".serial", errors="replace"):
    m = re.match(r"evm: status 00, (\d+) ms", line)
    if m: own.append(int(m.group(1)))
host = sorted((r.get("seconds") or {}).get("guest", 0) for r in rows if r.get("seconds"))
size = sorted(r.get("request_bytes", 0) for r in rows)
total = sorted((r.get("seconds") or {}).get("total", 0) for r in rows if r.get("seconds"))
own.sort()
print(f"{len(rows)} slots; a request is {size[len(size)//2] / 1e6:.2f} MB at the median")
print(f"asking the guest, as the host times it: median {st.median(host):.2f} s, 90th {host[int(len(host)*.9)]:.2f}")
print(f"the guest's own account of its work:    median {st.median(own)/1000:.2f} s, 90th {own[int(len(own)*.9)]/1000:.2f}  ({len(own)} rounds)")
print(f"a whole round (inputs, proofs, guest):  median {st.median(total):.2f} s")
for lo, hi in ((0, 2e6), (2e6, 3e6), (3e6, 6e6), (6e6, 1e9)):
    g = [(r.get("seconds") or {}).get("guest", 0) for r in rows if lo <= r.get("request_bytes", 0) < hi and r.get("seconds")]
    if g: print(f"  requests of {lo/1e6:.0f} to {hi/1e6:.0f} MB: {len(g)} slots, asking the guest took {st.median(g):.2f} s at the median")
rounds = [len(r.get("rounds") or []) for r in rows]
print(f"rounds a slot: median {st.median(rounds)}; last block ready before its slot: median {st.median([r.get('ready_before_slot', 0) for r in rows]):.2f} s")
