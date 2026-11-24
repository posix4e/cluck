// Runs the public page's checks (docs/live.js, docs/verify.js) under Node on the record and quote the
// page serves (docs/live/), and on the same with one thing wrong at a time, which must each fail.
//
//     node demo/test-live.mjs          (from evm/)
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const docs = join(dirname(fileURLToPath(import.meta.url)), "..", "..", "docs");
for (const name of ["verify.js", "live.js"]) new Function(readFileSync(join(docs, name), "utf8"))();
const { checkLive } = globalThis.LiveCheck;
const record = JSON.parse(readFileSync(join(docs, "live", "builder.json"), "utf8"));
const quote = Uint8Array.from(readFileSync(join(docs, "live", record.quote)));
let failures = 0;
const expect = (what, holds) => { if (!holds) { failures += 1; console.log("FAILED: " + what); } };

const real = await checkLive(record, quote, Date.now());
for (const s of real.steps) console.log(`  ${s.ok ? "holds" : "FAILS"}  ${s.title}`);
expect("the record and quote as served stand", real.good && real.steps.length === 10);

const flipped = (text) => text.slice(0, -1) + (text.endsWith("0") ? "1" : "0");
const wrong = [
  ["another builder's key", { ...record, builder: flipped(record.builder) }, quote],
  ["another challenge", { ...record, challenge: flipped(record.challenge) }, quote],
  ["another image's RTMR1", { ...record, rtmr1: flipped(record.rtmr1) }, quote],
  ["a key that is not hexadecimal", { ...record, builder: "0xzz" }, quote],
  ["a quote with a byte of its report changed", record, quote.map((b, i) => (i === 300 ? b ^ 1 : b))],
  ["a quote cut short", record, quote.subarray(0, 700)],
  ["a certificate chain judged ten years on", record, quote, Date.now() + 10 * 365 * 86400 * 1000],
];
for (const [what, r, q, when] of wrong) {
  const got = await checkLive(r, q, when || Date.now());
  expect(`${what} is refused`, !got.good);
}
expect("verify.js here is the one the demo's page uses",
       readFileSync(join(docs, "verify.js"), "utf8") === readFileSync(join(docs, "..", "evm", "demo", "verify.js"), "utf8"));
console.log(failures ? `test-live: ${failures} failed` : `test-live: all checks passed (${wrong.length} wrong ones refused)`);
process.exit(failures ? 1 : 0);
