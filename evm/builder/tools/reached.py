"""For N slots spread over a shadow log: when the last of our bids that a relay lists reached that relay,
against the beginning of the slot, beside when this program had the guest's answer for the slot's last
round (which comes after the relays have answered), and when the bid the proposer took reached its
relay. Reads the log and relays' public lists only.

    python3 -I builder/tools/reached.py LOG N        (from evm/)
"""
import json, sys, time, urllib.request, statistics as st
RELAYS = ["https://boost-relay.flashbots.net", "https://relay-builders-us.ultrasound.money", "https://aestus.live",
          "https://us-global.titanrelay.xyz", "https://bloxroute.max-profit.blxrbdn.com", "https://agnostic-relay.net"]
GENESIS = 1606824023
def get(url):
    try:
        q = urllib.request.Request(url, headers={"User-Agent": "research"})
        return json.load(urllib.request.urlopen(q, timeout=15))
    except Exception:
        return None
rows = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
rows = [r for r in rows if r.get("slot") and r.get("rounds") and r.get("builder")]
n = int(sys.argv[2])
taken_at, ours_at, behind = [], [], []
for r in rows[::max(1, len(rows) // n)][:n]:
    slot, start, line = r["slot"], (GENESIS + 12 * r["slot"]) * 1000, [r["slot"]]
    for relay in RELAYS:
        d = get(f"{relay}/relay/v1/data/bidtraces/proposer_payload_delivered?slot={slot}")
        time.sleep(0.05)
        if d:
            b = get(f"{relay}/relay/v1/data/bidtraces/builder_blocks_received?slot={slot}&block_hash={d[0]['block_hash']}")
            ts = [int(x["timestamp_ms"]) for x in (b or []) if x.get("timestamp_ms")]
            if ts:
                taken_at.append((min(ts) - start) / 1000)
                line.append("the bid taken reached %s at %+.2f s" % (relay.split("//")[1], taken_at[-1]))
            break
    for relay in RELAYS[:2]:
        b = get(f"{relay}/relay/v1/data/bidtraces/builder_blocks_received?slot={slot}&builder_pubkey={r['builder']}")
        ts = sorted(int(x["timestamp_ms"]) for x in (b or []) if x.get("timestamp_ms"))
        time.sleep(0.05)
        if ts:
            ours_at.append((ts[-1] - start) / 1000)
            line.append("| %d of ours listed at %s, the last at %+.2f s" % (len(ts), relay.split("//")[1], ours_at[-1]))
            if "ready_before_slot" in r:
                behind.append(-r["ready_before_slot"] - ours_at[-1])
                line.append("(its answer was here at %+.2f s)" % -r["ready_before_slot"])
            break
    print(*line, flush=True)
q = lambda w, p: sorted(w)[min(len(w) - 1, int(len(w) * p))]
if taken_at:
    print("\nbids taken, %d with a time: a tenth by %+.2f s, median %+.2f s" % (len(taken_at), q(taken_at, .1), st.median(taken_at)))
if ours_at:
    print("our last listed, %d slots: median %+.2f s, a tenth by %+.2f s, nine tenths by %+.2f s"
          % (len(ours_at), st.median(ours_at), q(ours_at, .1), q(ours_at, .9)))
if behind:
    print("the answer was here %.2f s after the relay had the bid, at the median" % st.median(behind))
