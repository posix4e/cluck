"""For the slots of shadow logs, many hours at once: what the last bid of ours in each slot was worth
against what the block the proposer took paid, as relays' public lists have it, and inside each slot
what the last bid was worth against the last one whose answer was back EARLY seconds before the slot
began. Asks each relay for its list a page of 200 at a time, so a day costs each about 40 questions,
where `gap.py` asks every relay about every slot. Reads only.

    python3 -I builder/tools/gapday.py [--early 0.7] [--more ETH ...] LOG...        (from evm/)

`--more` says how many of the taken blocks our last bid would have outbid with that much ETH added.
A relay's list names what it delivered, not what the proposer chose among: a slot no relay lists was
built by its proposer or came through a relay not asked here.
"""
import json, sys, time, urllib.request, statistics as st
RELAYS = ["https://boost-relay.flashbots.net", "https://relay-builders-us.ultrasound.money", "https://aestus.live",
          "https://us-global.titanrelay.xyz", "https://agnostic-relay.net"]
args, early, more = sys.argv[1:], 0.7, []
while args and args[0].startswith("--"):
    if args[0] == "--early": early, args = float(args[1]), args[2:]
    elif args[0] == "--more":
        args = args[1:]
        while args and args[0].replace(".", "").isdigit(): more, args = more + [float(args[0])], args[1:]
    else: sys.exit(__doc__)
if not args: sys.exit(__doc__)

def sent(rnd):
    """Whether a relay answered this round's block with 200 or 202."""
    return any(a and a[0] in (200, 202) for a in rnd.get("relay") or [])

slots = {}
for path in args:
    for line in open(path, errors="replace"):
        if not line.strip(): continue
        r = json.loads(line)
        rounds = [x for x in r.get("rounds") or [] if sent(x)]
        if "slot" not in r or not rounds: continue
        last = rounds[-1]
        before = [x for x in rounds if (x.get("ready_before_slot") or -99) >= early]
        paid = any(x.get("top_up_eth") for x in r.get("rounds") or [])
        kept = slots.get(r["slot"])
        if kept is None or len(rounds) > kept["rounds"]:
            slots[r["slot"]] = {"rounds": len(rounds), "last": last.get("value_eth") or 0, "at": last.get("ready_before_slot"),
                                "early": (before[-1].get("value_eth") or 0) if before else None,
                                "early_at": before[-1].get("ready_before_slot") if before else None, "paid": paid}
if not slots: sys.exit("no slot with a bid sent in these logs")
first, end = min(slots), max(slots)

taken, asked = {}, {}
for relay in RELAYS:
    name, cursor, got, pages = relay.split("//")[1], end, 0, 0
    while cursor >= first:
        try:
            q = urllib.request.Request(f"{relay}/relay/v1/data/bidtraces/proposer_payload_delivered?limit=200&cursor={cursor}",
                                       headers={"User-Agent": "research"})
            rows = json.load(urllib.request.urlopen(q, timeout=30))
        except Exception as e:
            print(f"{name}: stopped at slot {cursor}: {repr(e)[:80]}", file=sys.stderr)
            break
        pages += 1
        if not rows: break
        for x in rows:
            s = int(x["slot"])
            if first <= s <= end:
                got += 1
                taken.setdefault(s, (int(x["value"]) / 1e18, name))
        if len(rows) < 200: break
        cursor = min(int(x["slot"]) for x in rows) - 1
        time.sleep(0.4)
    asked[name] = (pages, got)

paid = sorted(s for s in slots if slots[s]["paid"])
plain = {s: v for s, v in slots.items() if not v["paid"]}
print(f"slots {first} to {end}: {len(slots)} with a bid of ours sent" + (f", {len(paid)} of them with a payment added and left out below: {paid}" if paid else ""))
print("relays' lists: " + ", ".join(f"{n} {g} slots in {p} pages" for n, (p, g) in asked.items()))
known = [(s, v["last"], taken[s][0]) for s, v in plain.items() if s in taken and taken[s][0] > 0]
by = {}
for s, _, _ in known: by[taken[s][1]] = by.get(taken[s][1], 0) + 1
print(f"{len(known)} of them with a taken block a relay lists (first relay to list each: " + ", ".join(f"{n} {c}" for n, c in sorted(by.items(), key=lambda x: -x[1])) + ")")
if known:
    ratios = sorted(o / t for _, o, t in known)
    so, stn = sum(o for _, o, _ in known), sum(t for _, _, t in known)
    print("taken blocks: median %.5f ETH, summed %.3f | ours, the last bid: median %.5f, summed %.3f" % (st.median(t for _, _, t in known), stn, st.median(o for _, o, _ in known), so))
    print("ours as a share of the taken block: median %.1f%%, summed %.1f%%, best %.1f%%; slots where ours was worth as much or more: %d" % (100 * st.median(ratios), 100 * so / stn, 100 * ratios[-1], sum(x >= 1 for x in ratios)))
    for s, o, t in known:
        if o >= t: print("   slot %d: ours %.5f ETH, its answer back %+.2f s from the slot's start; taken %.5f through %s" % (s, o, -plain[s]["at"], t, taken[s][1]))
    for m in more:
        n = sum(o + m > t for _, o, t in known)
        print("with %.4f ETH more ours would have been above the taken block in %d of %d, %.0f%%" % (m, n, len(known), 100 * n / len(known)))
both = [(v["early"], v["last"], v["early_at"] - v["at"]) for v in plain.values() if v["early"] is not None and v["at"] is not None and v["at"] < early and v["early"] > 0]
if both:
    gains = sorted(l / e - 1 for e, l, _ in both)
    q = lambda p: 100 * gains[int(p * (len(gains) - 1))]
    print("inside the slot, the last bid against the last whose answer was back %.1f s or more before the slot (%d slots, %.2f s apart at the median): "
          "%.1f%% more summed, %.1f%% at the median, a quarter under %.1f%% and a quarter over %.1f%%; worth less in %d"
          % (early, len(both), st.median(d for _, _, d in both), 100 * (sum(l for _, l, _ in both) / sum(e for e, _, _ in both) - 1), q(.5), q(.25), q(.75), sum(g < 0 for g in gains)))
