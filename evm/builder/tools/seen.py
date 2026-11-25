"""Watches the node's pending transactions and, for each block the chain then gets, says how much of it
this node had seen pending beforehand, by count and by what the transactions paid over the base fee.
Reads only. Usage: seen.py BLOCKS OUT.jsonl"""
import json, sys, time, urllib.request
def rpc(m, p):
    q = urllib.request.Request("http://127.0.0.1:8545", json.dumps({"jsonrpc":"2.0","id":1,"method":m,"params":p}).encode(), {"content-type":"application/json"})
    r = json.load(urllib.request.urlopen(q, timeout=30))
    if "error" in r: raise RuntimeError(r["error"])
    return r["result"]
wanted, out = int(sys.argv[1]), open(sys.argv[2], "a")
seen = {}
f = rpc("eth_newPendingTransactionFilter", [])
began = time.time()
for by in rpc("txpool_content", [])["pending"].values():
    for tx in by.values():
        seen[tx["hash"]] = began
head, done = rpc("eth_blockNumber", []), 0
while done < wanted:
    time.sleep(0.25)
    g = rpc("eth_newPendingTransactionFilter", [])
    now = time.time()
    for h in rpc("eth_getFilterChanges", [f]):
        seen.setdefault(h, now)
    rpc("eth_uninstallFilter", [f]); f = g
    newest = rpc("eth_blockNumber", [])
    if newest == head: continue
    head = newest
    block = rpc("eth_getBlockByNumber", [head, True])
    receipts = rpc("eth_getBlockReceipts", [head])
    base, at = int(block["baseFeePerGas"], 16), int(block["timestamp"], 16)
    row = {"number": int(head, 16), "slot": (at - 1606824023) // 12, "txs": len(block["transactions"]), "watched_s": round(at - began, 1),
           "seen": 0, "tips": 0.0, "tips_seen": 0.0, "tips_by": {}, "seen_by": {}}
    for tx, r in zip(block["transactions"], receipts):
        tip = int(r["gasUsed"], 16) * (int(r["effectiveGasPrice"], 16) - base) / 1e18
        row["tips"] += tip
        first = seen.get(tx["hash"])
        if first is not None and first < at:
            row["seen"] += 1; row["tips_seen"] += tip
            row.setdefault("public", []).append([tx["hash"], tip, round(at - first, 2)])
            for cut in (0, 1, 2, 3, 4, 6, 9):      # seen at least this many seconds before the slot
                if first <= at - cut:
                    row["tips_by"][cut] = row["tips_by"].get(cut, 0) + tip
                    row["seen_by"][cut] = row["seen_by"].get(cut, 0) + 1
    out.write(json.dumps(row) + "\n"); out.flush(); done += 1
    for h in [h for h, t in seen.items() if t < now - 600]:
        del seen[h]
