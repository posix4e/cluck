"""One look at a shadow log made with --rebid: whether every slot got a block, whether every block sent was
valid, signed, the same at the relay and in time, and what went wrong where it did. Usage: health.py LOG"""
import json, sys, statistics as st
rows = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
slots = [r for r in rows if "number" in r]
ok = [r for r in slots if r.get("rounds")]
alls = [x for r in ok for x in r["rounds"]]
sent = [x for x in alls if x.get("status") == 0 and not x.get("not_sent")]
print("slots", len(slots), "| with a block sent", sum(1 for r in ok if any(x.get("status") == 0 and not x.get("not_sent") for x in r["rounds"])),
      "| without rounds:", [(r["number"], str(r.get("skipped", r.get("status")))[:70]) for r in slots if not r.get("rounds")][:6])
print("rounds", len(alls), "| sent", len(sent), "| kept by the guest", sum(bool(x.get("not_sent")) for x in alls),
      "| by status", {s: sum(x.get("status") == s for x in alls) for s in {x.get("status") for x in alls}}, "| skipped", sum("skipped" in x for x in alls))
print("of those sent: judged", {v: sum(str(x.get("judged"))[:40] == v for x in sent) for v in {str(x.get("judged"))[:40] for x in sent}},
      "| same at the relay", {v: sum(x.get("relay_same") == v for x in sent) for v in {x.get("relay_same") for x in sent}},
      "| signed", {v: sum(x.get("signed") == v for x in sent) for v in {x.get("signed") for x in sent}})
odd = [x.get("relay") for x in sent if x.get("relay") != [[200, ""]]]
print("relay answers other than 200:", len(odd), odd[:4])
times = sorted(x["ready_before_slot"] for x in sent)
last = sorted(r["ready_before_slot"] for r in ok)
print("sent blocks ready after the slot began:", sum(t < 0 for t in times), "| last block of a slot ready before it: least", last[0], "10th", last[len(last) // 10], "median", last[len(last) // 2], "90th", last[-max(1, len(last) // 10)])
print("last block: txs median", st.median(r.get("went_in", 0) for r in ok), "| value median %.5f sum %.4f" % (st.median(r.get("value_eth") or 0 for r in ok), sum(r.get("value_eth") or 0 for r in ok)),
      "| rounds a slot median", st.median(len(r["rounds"]) for r in ok), "| round s median", st.median(x["seconds"] for x in alls if x.get("seconds")),
      "| guest replaced", sum(1 for r in slots if r.get("guest_replaced")))
text = open(sys.argv[1]).read()
print("mended", text.count('"mended"'), "| emptying given up", text.count("emptying_given_up"), "| too late, not sent", text.count('"too_late"'), "| mend failed", text.count("mend_failed"))
