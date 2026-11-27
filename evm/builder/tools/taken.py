"""When the bid a proposer took first reached a relay, against the beginning of its slot, for N slots
from FIRST on: the relay that lists the block as delivered gives its hash, and every relay that lists
when it received a bid with that hash gives a time; the earliest counts. Reads relays' public lists only.

    python3 -I builder/tools/taken.py FIRST N        (from evm/)
"""
import json, sys, time, urllib.request, statistics as st
RELAYS = ["https://boost-relay.flashbots.net", "https://relay-builders-us.ultrasound.money", "https://aestus.live",
          "https://us-global.titanrelay.xyz", "https://bloxroute.max-profit.blxrbdn.com", "https://agnostic-relay.net"]
GENESIS = 1606824023
def get(url):
    try:
        q = urllib.request.Request(url, headers={"User-Agent": "research"})
        return json.load(urllib.request.urlopen(q, timeout=15))
    except Exception as e:
        return None
first, n = int(sys.argv[1]), int(sys.argv[2])
at = []
for slot in range(first, first + n):
    start = (GENESIS + 12 * slot) * 1000
    d = None
    for relay in RELAYS:
        d = get(f"{relay}/relay/v1/data/bidtraces/proposer_payload_delivered?slot={slot}")
        time.sleep(0.03)
        if d: break
    if not d:
        print(slot, "no relay lists a block taken", flush=True); continue
    h, times = d[0]["block_hash"], []
    for relay in RELAYS:
        b = get(f"{relay}/relay/v1/data/bidtraces/builder_blocks_received?slot={slot}&block_hash={h}")
        times += [(int(x["timestamp_ms"]), relay.split("//")[1][:14]) for x in (b or []) if x.get("timestamp_ms")]
        time.sleep(0.03)
    if times:
        t = min(times); at.append((t[0] - start) / 1000)
        print(slot, "%+.2f s" % at[-1], t[1], "%.5f ETH" % (int(d[0]["value"]) / 1e18), len(times), "relays list it", flush=True)
    else:
        print(slot, "taken, no time listed", flush=True)
w = sorted(at)
if w:
    q = lambda p: w[min(len(w) - 1, int(len(w) * p))]
    print("\n%d of %d slots with a time: first tenth %+.2f, quarter %+.2f, median %+.2f, three quarters %+.2f, nine tenths %+.2f" % (len(w), n, q(.1), q(.25), q(.5), q(.75), q(.9)))
    print("before the slot began: %d; before -0.85 s: %d; within 0.5 s after: %d" % (sum(x < 0 for x in w), sum(x < -0.85 for x in w), sum(0 <= x < 0.5 for x in w)))
