"""The keys a live feed's bids were signed with, from its records (builder/feed keeps one an hour): for
each, the first and the last slot a bid under it was sent to a relay, and in how many slots one was.
Usage: keys.py LOG [LOG ...]

A guest draws its key when it starts, so a new key is a guest that was started again. With a key and a
slot, a relay's public list of the blocks it received says what it had from this builder:
/relay/v1/data/bidtraces/builder_blocks_received?slot=SLOT, the rows whose builder_pubkey is the key
(tools/reached.py reads that list). Relays keep the list for a time of their own choosing."""
import datetime, json, sys

when = lambda slot: datetime.datetime.fromtimestamp(1606824023 + 12 * slot, datetime.timezone.utc).strftime("%Y-%m-%d %H:%M")
slots = {}
for path in sys.argv[1:]:
    for line in open(path, errors="replace"):
        try: r = json.loads(line)
        except ValueError: continue       # a line the feed was still writing
        if "slot" in r and r.get("builder") and any(x.get("relay") for x in r.get("rounds") or []):
            slots.setdefault(r["builder"], set()).add(r["slot"])
if not slots: sys.exit("keys.py: no bid in these records")
for key, bid in sorted(slots.items(), key=lambda kv: min(kv[1])):
    print(f"{key}  slots {min(bid)} ({when(min(bid))} UTC) to {max(bid)} ({when(max(bid))} UTC), a bid in {len(bid)}")
