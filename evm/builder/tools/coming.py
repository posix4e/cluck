"""Reads a guest's console (on Compute Engine: gcloud compute instances get-serial-port-output NAME) for
what it says of each request to build and send: how large it was, how long it was in coming by the guest's
clock (first bytes to last), how long the guest then took, and what became of the block. Says those for
all rounds, and apart for the rounds whose block the guest kept back because it paid no more than one
already sent, each beside the round before it. Usage: coming.py CONSOLE

A round kept back is nearly always one cut short by the clock with nothing in it: the time a request
allows for transactions is counted from its first bytes, so a request slow in coming has none left. The
console holds the last megabyte the guest wrote, about two hours of rounds."""
import re, statistics as st, sys

lines = open(sys.argv[1], errors="replace").read().split("\n")
came = re.compile(r"evm: request of (\d+) bytes, (\d+) ms in coming")
built = re.compile(r"evm: status (\w+), (\d+) ms")
rounds = []      # (megabytes, ms in coming, ms building, what became of it)
for i, line in enumerate(lines[:-2]):
    a, b = came.match(line), built.match(lines[i + 1])
    if not a or not b: continue
    after = lines[i + 2]
    fate = "sent" if "sending" in after else after.partition("not sent: ")[2].split(",")[0][:60] if "not sent" in after else "other"
    rounds.append((int(a.group(1)) / 1e6, int(a.group(2)), int(b.group(2)), fate))
if not rounds: sys.exit("coming.py: no request to build in this console")

def said(name, rows):
    if not rows: return
    q = lambda v: "%.0f at the median, %.0f for one in ten" % (st.median(v), sorted(v)[len(v) * 9 // 10]) if v else "none"
    print(f"{name}: {len(rows)} | MB {st.median(r[0] for r in rows):.2f} at the median | ms in coming {q([r[1] for r in rows])}"
          f" | ms for a megabyte {q([r[1] / r[0] for r in rows if r[0] > 0.1])} | ms the guest then took {q([r[2] for r in rows])}")
said("all rounds", rounds)
for fate in sorted({r[3] for r in rounds}):
    said("   " + fate, [r for r in rounds if r[3] == fate])
back = [(rounds[i], rounds[i - 1]) for i in range(1, len(rounds)) if rounds[i][3].startswith("it pays no more")]
if back:
    print(f"kept back for paying no more than one already sent: {len(back)} of {len(rounds)} rounds")
    print("   in coming: %.0f ms at the median, the round before each %.0f | MB %.2f, before %.2f | the guest then took %.0f ms, before %.0f"
          % tuple(st.median(pair[k][j] for pair in back) for j in (1, 0, 2) for k in (0, 1)))
