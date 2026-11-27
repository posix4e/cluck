"""Several records of a live feed (builder/feed keeps one an hour) counted as one stretch of time: how many
slots went by, in how many a bid of ours was sent, why not in the others, what our node made of the blocks
sent and what the relays answered. Usage: day.py LOG [LOG ...]

A slot counts as gone by if it lies between the first and the last slot of the records, whether or not a
record has it. One with no record is listed by number: the records do not say why (the guest was being
changed, the feed was between runs, or the slot before had no block and nothing was asked)."""
import collections, datetime, json, statistics as st, sys

rows = {}
for path in sys.argv[1:]:
    for line in open(path):
        try: r = json.loads(line)
        except ValueError: continue       # a line the feed was still writing
        if "slot" not in r or "number" not in r: continue
        # A slot can be asked for twice (the slot before taken for empty, and then its block came): both
        # askings' blocks were sent and both count.
        rows.setdefault(r["slot"], []).append(r)
if not rows: sys.exit("day.py: no slot in these records")
first, last = min(rows), max(rows)
when = lambda slot: datetime.datetime.fromtimestamp(1606824023 + 12 * slot, datetime.timezone.utc).strftime("%Y-%m-%d %H:%M:%S")
gone = last - first + 1
print(f"{len(sys.argv) - 1} records, slots {first} ({when(first)} UTC) to {last} ({when(last)} UTC): {gone} went by")

bid, unregistered, kept, unbuilt, absent = [], [], [], [], []
for slot in range(first, last + 1):
    asked = rows.get(slot)
    if asked is None: absent.append(slot)
    elif not any(r.get("rounds") for r in asked): unbuilt.append(slot)
    elif any(x.get("relay") for r in asked for x in r.get("rounds") or []): bid.append(slot)
    elif not any(r.get("registered") for r in asked): unregistered.append(slot)
    else: kept.append(slot)
twice = [slot for slot in rows if len(rows[slot]) > 1]
def runs(slots):  # 5, 6, 7, 9 as "5-7 9"
    out, i = [], 0
    while i < len(slots):
        j = i
        while j + 1 < len(slots) and slots[j + 1] == slots[j] + 1: j += 1
        out.append(str(slots[i]) if i == j else f"{slots[i]}-{slots[j]}")
        i = j + 1
    return " ".join(out)
print(f"a bid sent to a relay in {len(bid)} of them, {100 * len(bid) / gone:.1f}%")
print(f"without: {len(unregistered)} no relay held a registration from the proposer | {len(kept)} built and nothing sent "
      f"| {len(unbuilt)} asked and nothing built | {len(absent)} with no record")
for name, slots in (("built and nothing sent", kept), ("asked and nothing built", unbuilt), ("no record", absent)):
    if slots: print(f"   {name}: {runs(slots)}")

rounds = [x for s in sorted(rows) for r in rows[s] for x in r.get("rounds") or []]
sent = [x for x in rounds if x.get("relay")]
verdicts = collections.Counter("no verdict (the guest showed no block)" if x.get("judged") is None else str(x["judged"])[:60] for x in sent)
print(f"{len(rounds)} blocks built, {len(sent)} sent | our node on those sent: {dict(verdicts)}"
      f" | found not signed as they should be: {sum(1 for x in sent if x.get('signed') is False)}")
late = [x["ready_before_slot"] for x in sent if x.get("ready_before_slot", 0) < 0]
lead = sorted(rows[s][-1]["ready_before_slot"] for s in bid if rows[s][-1].get("relay") and "ready_before_slot" in rows[s][-1])
over = [s for s in bid if any(x.get("over") for r in rows[s] for x in r.get("rounds") or [])]
print(f"rounds that ended after their slot began: {len(late)}, in {len(set(s for s in bid for r in rows[s] for x in r.get('rounds') or [] if x.get('relay') and x.get('ready_before_slot', 0) < 0))} slots"
      + f" | slots a relay said were over: {len(over)}"
      + (f" | a slot's last bid before it began (below nothing: after): median {st.median(lead)} s, a tenth under {lead[len(lead) // 10]} s" if lead else "")
      + f" | rounds a slot: median {st.median(sum(len(r.get('rounds') or []) for r in rows[s]) for s in bid)}"
      + f" | slots asked for twice: {len(twice)}")
# A round whose block has no transaction in it was cut short by the clock before the first went in (the
# guest keeps such a block back). When it is a slot's last, the slot's last bid is an earlier round's.
bare = lambda x: x.get("status") == 0 and x.get("went_in") == 0
ended_bare = [s for s in bid if bare((rows[s][-1].get("rounds") or [{}])[-1])]
before_it = sorted(x["ready_before_slot"] for s in ended_bare for x in [y for y in rows[s][-1]["rounds"] if y.get("relay")][-1:])
print(f"rounds whose block had no transaction in it: {sum(1 for x in rounds if bare(x))} | slots whose last round was one: {len(ended_bare)}"
      + (f", their last bid {st.median(before_it)} s before the slot at the median" if before_it else ""))
answers, said = collections.Counter(), collections.Counter()
for x in sent:
    for status, text in x["relay"]:
        after = " after the slot began" if x.get("over") and isinstance(status, int) and 400 <= status < 500 and status != 429 else ""
        answers[f"{status}{after}"] += 1
        if status not in (200, 202): said[(f"{status}{after}", str(text).strip()[:90])] += 1
print(f"{sum(answers.values())} answers from relays: " + ", ".join(f"{n} of {status}" for status, n in sorted(answers.items(), key=lambda a: str(a[0]))))
for (status, text), n in said.most_common(20): print(f"   {n} x {status} {text!r}")
keys = collections.Counter(rows[s][-1].get("builder") for s in bid if rows[s][-1].get("builder"))
print(f"keys the bids were under: {len(keys)}" + "".join(f"\n   {k[:18]}… in {n} slots" for k, n in keys.items()))
landed = [(r["number"], r.get("hash")) for s in sorted(rows) for r in rows[s] if r.get("landed")]
print(f"blocks of ours a proposer took: {landed if landed else 'none'}")
