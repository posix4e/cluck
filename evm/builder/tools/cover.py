"""Joins a watcher's record (seen.py) with a shadow log: of what the block the chain took held that had been
pending in public at least CUT seconds before its slot, how much (by what it paid over the base fee) was
in our last block of that slot. Usage: cover.py SEEN.jsonl SHADOW.jsonl [CUT ...]"""
import json, sys, statistics as st
seen = {r["slot"]: r for r in (json.loads(l) for l in open(sys.argv[1]) if l.strip())}
ours = {r["slot"]: r for r in (json.loads(l) for l in open(sys.argv[2]) if l.strip()) if r.get("rounds") and "txs" in r}
cuts = [float(c) for c in sys.argv[3:]] or [3, 2, 1, 0.5, 0]
both = sorted(set(seen) & set(ours))
print(len(both), "slots in both; our last block ready before the slot: median", st.median(ours[s]["ready_before_slot"] for s in both))
for cut in cuts:
    shares, had, could = [], 0.0, 0.0
    for s in both:
        public = [(h, tip) for h, tip, before in seen[s].get("public", []) if before >= cut]
        total = sum(tip for _, tip in public)
        mine = set(ours[s]["txs"])
        got = sum(tip for h, tip in public if h in mine)
        if total > 0:
            shares.append(got / total); had += got; could += total
    print("public at least %.1f s before: of its fees ours held median %.0f%%, summed %.0f%% (%.4f of %.4f ETH)" % (cut, 100 * st.median(shares), 100 * had / could, had, could))
missed = {}
