"""Joins a watcher's record (seen.py) with a shadow log: of what the block the chain took held that had been
pending in public at least CUT seconds before its slot, how much (by what it paid over the base fee) was
in our last block of that slot; and what was not, by how long before the slot it became public.
Usage: cover.py SEEN.jsonl SHADOW.jsonl [CUT ...]"""
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
# What was public and is not in ours, by how long before the slot it became public. Our last round takes
# its transactions when it begins, so what became public after that was lost to time whatever else is so.
began = sorted(ours[s]["rounds"][-1]["ready_before_slot"] + ours[s]["rounds"][-1].get("seconds", 0) for s in both)
print("our last round began before the slot: median %.2f s, a tenth under %.2f s" % (st.median(began), began[len(began) // 10]))
edges = [0, 0.5, 1, 1.5, 2, 3, 6, 12, float("inf")]
public, missed = [0.0] * 8, [0.0] * 8
for s in both:
    mine = set(ours[s]["txs"])
    for h, tip, before in seen[s].get("public", []):
        if before < 0: continue
        i = max(i for i in range(8) if before >= edges[i])
        public[i] += tip
        if h not in mine: missed[i] += tip
print("public by the slot's start: %.4f ETH of fees, %.4f of it not in ours" % (sum(public), sum(missed)))
for i in range(8):
    if public[i] > 0:
        print("   public %4.1f s to %s before: %.4f ETH, not in ours %.4f (%.0f%% of it; %.0f%% of all that is not in ours)"
              % (edges[i], "%.1f s" % edges[i + 1] if i < 7 else "longer", public[i], missed[i], 100 * missed[i] / public[i], 100 * missed[i] / max(sum(missed), 1e-18)))
