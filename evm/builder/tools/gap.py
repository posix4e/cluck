"""For each slot of a shadow log: what our last block of the slot was worth, and what the block the
proposer took paid, as relays' public lists have it. Reads only."""
import json, sys, time, urllib.request, statistics as st
RELAYS = ["https://boost-relay.flashbots.net", "https://relay-builders-us.ultrasound.money", "https://aestus.live",
          "https://us-global.titanrelay.xyz", "https://bloxroute.max-profit.blxrbdn.com", "https://agnostic-relay.net"]
def delivered(slot):
    for relay in RELAYS:
        try:
            q = urllib.request.Request(f"{relay}/relay/v1/data/bidtraces/proposer_payload_delivered?slot={slot}", headers={"User-Agent": "research"})
            rows = json.load(urllib.request.urlopen(q, timeout=15))
            if rows:
                return int(rows[0]["value"]) / 1e18, int(rows[0].get("num_tx", 0)), relay.split("//")[1]
        except Exception:
            pass
        time.sleep(0.05)
    return None
rows = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
out = []
for r in rows:
    rs = r.get("rounds")
    if not rs or "slot" not in r: continue
    won = delivered(r["slot"])
    ours, first = r.get("value_eth") or 0, rs[0].get("value_eth") or 0
    out.append((r["slot"], first, ours, r.get("went_in"), r.get("ready_before_slot"), won))
    print(r["slot"], "first %.5f" % first, "last %.5f (%s txs, %ss before)" % (ours, r.get("went_in"), r.get("ready_before_slot")),
          "| taken: " + ("%.5f ETH, %d txs, %s" % won if won else "no relay lists it"), "| ours/taken %.1f%%" % (100 * ours / won[0]) if won and won[0] else "")
known = [o for o in out if o[5] and o[5][0] > 0]
if known:
    ratios = sorted(o[2] / o[5][0] for o in known)
    print(f"\n{len(out)} slots, {len(known)} with a relay's figure.")
    print("taken blocks: median %.5f ETH; ours, last round: median %.5f; first round: median %.5f" % (st.median(o[5][0] for o in known), st.median(o[2] for o in known), st.median(o[1] for o in known)))
    print("ours as a share of the taken block: median %.1f%%, best %.1f%%, slots where ours was worth more: %d" % (100 * st.median(ratios), 100 * ratios[-1], sum(x >= 1 for x in ratios)))
    print("sum taken %.4f ETH, sum ours %.4f ETH (%.1f%%)" % (sum(o[5][0] for o in known), sum(o[2] for o in known), 100 * sum(o[2] for o in known) / sum(o[5][0] for o in known)))
