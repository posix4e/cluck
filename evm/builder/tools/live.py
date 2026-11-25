"""One look at a live --rebid log: what the relays answered, whether our node judged each block valid,
how early the last block of a slot was, and whether any landed. Usage: live.py LOG"""
import json, sys, statistics as st, collections
rows = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
slots = [r for r in rows if "number" in r]
ok = [r for r in slots if r.get("rounds")]
alls = [x for r in ok for x in r["rounds"]]
sent = [x for x in alls if x.get("relay")]
print("slots", len(slots), "| with rounds", len(ok), "| slots with a bid sent", sum(1 for r in ok if any(x.get("relay") for x in r["rounds"])),
      "| no relay held the registration:", sum(1 for r in ok if not any(x.get("relay") for x in r["rounds"])), "| without rounds:", [(r["number"], str(r.get("skipped"))[:60]) for r in slots if not r.get("rounds")][:5])
print("rounds", len(alls), "| bids sent", len(sent), "| kept by the guest", sum(bool(x.get("not_sent")) for x in alls), "| by status", dict(collections.Counter(x.get("status") for x in alls)))
print("our node on the blocks sent:", dict(collections.Counter(str(x.get("judged"))[:60] for x in sent)), "| signed", dict(collections.Counter(x.get("signed") for x in sent)))
answers = collections.Counter()
for x in sent:
    for a in x["relay"]:
        answers[(a[0], a[1].strip()[:70])] += 1
for (status, text), n in answers.most_common(12): print("   relay answer", status, repr(text), "x", n)
last = sorted(r["ready_before_slot"] for r in ok if r.get("relay"))
times = [x["ready_before_slot"] for x in sent]
if last: print("bids answered after the slot began:", sum(t < 0 for t in times), "of", len(times), "| last bid of a slot before it: least", last[0], "10th", last[len(last)//10], "median", last[len(last)//2])
print("last block: txs median", st.median(r.get("went_in", 0) for r in ok), "| value median %.5f" % st.median(r.get("value_eth") or 0 for r in ok), "| rounds a slot median", st.median(len(r["rounds"]) for r in ok), "| round s median", st.median(x["seconds"] for x in alls if x.get("seconds")))
print("landed:", [(r["number"], r.get("hash"), r.get("value_eth"), r.get("delivered")) for r in slots if r.get("landed")])
text = open(sys.argv[1]).read()
print("mended", text.count('"mended"'), "| emptying given up", text.count("emptying_given_up"), "| too late, not sent", text.count('"too_late"'), "| guest replaced", text.count("guest_replaced"))
