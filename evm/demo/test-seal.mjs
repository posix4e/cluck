// Does what demo/seal.html does, against a running demo server: asks for the machine's sealing key with a
// report, checks the quote with verify.js and that it is for this key and this request, and seals a
// transaction to the key with seal.js. Then checks that the quote does not pass for another key or another
// request. What it cannot check is that the machine opens what was sealed: builder/shadow --sealed does.
//
//     node demo/test-seal.mjs [http://127.0.0.1:5172]
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
new Function(readFileSync(join(here, "verify.js"), "utf8"))();
new Function(readFileSync(join(here, "seal.js"), "utf8"))();
const { verifyQuote, sha256, hex, concat, same } = globalThis.TdxQuote;
const base = process.argv[2] || "http://127.0.0.1:5172";
let failures = 0;
const expect = (what, ok) => { console.log(`  ${ok ? "ok " : "NO "} ${what}`); if (!ok) failures++; };

const info = await (await fetch(base + "/api/info")).json();
const challenge = crypto.getRandomValues(new Uint8Array(32));
const answer = await (await fetch(base + "/api/sealkey", { method: "POST", body: JSON.stringify({ challenge: hex(challenge) }) })).json();
const key = Uint8Array.from(Buffer.from(answer.key, "hex"));
const quote = Uint8Array.from(Buffer.from(answer.quote, "base64"));
const { fields, steps } = await verifyQuote(quote, Date.now());
expect("every step of the quote", steps.length === 7 && steps.every((s) => s.ok));
const data = Uint8Array.from(Buffer.from(fields.reportData, "hex"));
const request = new TextEncoder().encode("JSEK1");
expect("the quote is for this request and these random bytes", same(await sha256(concat(challenge, request)), data.subarray(0, 32)));
expect("the quote is for this key", same(await sha256(key), data.subarray(32, 64)));
expect("the measurements are the ones recorded for the image",
  ["MRTD", "RTMR0", "RTMR1", "RTMR2", "RTMR3"].every((n) => info.recorded && info.recorded[n] === fields[n]));
const other = key.slice(); other[0] ^= 1;
expect("the quote is not for a key with a bit changed", !same(await sha256(other), data.subarray(32, 64)));
expect("nor for the same request with other random bytes",
  !same(await sha256(concat(crypto.getRandomValues(new Uint8Array(32)), request)), data.subarray(0, 32)));
const transaction = crypto.getRandomValues(new Uint8Array(110));
const envelope = await globalThis.cluckSeal.sealTransaction(key, 15705000n, transaction);
expect("a transaction of 110 bytes seals to 166: a public half, the slot, the transaction, a tag", envelope.length === 32 + 8 + 110 + 16);
const again = await globalThis.cluckSeal.sealTransaction(key, 15705000n, transaction);
expect("sealed twice, the same transaction gives different bytes", !same(envelope, again));
console.log(failures ? `test-seal: ${failures} FAILED` : "test-seal: all checks passed");
process.exit(failures ? 1 : 0);
