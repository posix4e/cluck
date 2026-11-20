// Puts one question to a running demo server the way the page does, checks the quote with verify.js, and
// then checks that verify.js refuses the same quote with any one of its parts changed.
//
//     node demo/test-verify.mjs [http://127.0.0.1:5172]
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
new Function(readFileSync(join(here, "verify.js"), "utf8"))();
const { verifyQuote, sha256, hex, concat, same } = globalThis.TdxQuote;
const base = process.argv[2] || "http://127.0.0.1:5172";
let failures = 0;
const expect = (what, ok) => { if (!ok) { failures++; console.log("FAILED: " + what); } };

const info = await (await fetch(base + "/api/info")).json();
const fixture = info.fixtures.reduce((a, b) => (a.size < b.size ? a : b));
for (const alter of ["none", "root", "state"]) {
  const challenge = crypto.getRandomValues(new Uint8Array(32));
  const request = new Uint8Array(await (await fetch(`${base}/fixtures/${fixture.name}.req`)).arrayBuffer());
  if (fixture.alter[alter] != null) request[fixture.alter[alter]] ^= 1;
  const reply = await (await fetch(base + "/api/run", {
    method: "POST", body: JSON.stringify({ fixture: fixture.name, alter, challenge: hex(challenge) }),
  })).json();
  const response = Uint8Array.from(Buffer.from(reply.response, "hex"));
  const quote = Uint8Array.from(Buffer.from(reply.quote, "base64"));
  const { fields, steps } = await verifyQuote(quote, Date.now());
  for (const s of steps) console.log(`  ${s.ok ? "ok " : "NO "} ${s.title}: ${s.detail}`);
  expect(`${alter}: every step of the quote`, steps.length === 7 && steps.every((s) => s.ok));
  const data = Uint8Array.from(Buffer.from(fields.reportData, "hex"));
  expect(`${alter}: REPORTDATA names the request`, same(data.subarray(0, 32), await sha256(concat(challenge, request))));
  expect(`${alter}: REPORTDATA names the response`, same(data.subarray(32), await sha256(response)));
  const status = { none: 0, root: 3, state: 2 }[alter];
  expect(`${alter}: status ${status}, got ${response[0]}`, response[0] === status);
  if (alter === "none") expect("the fixture's answer", reply.response === fixture.expected);
  if (info.recorded) {
    expect(`${alter}: recorded measurements`,
           ["MRTD", "RTMR0", "RTMR1", "RTMR2", "RTMR3"].every((n) => info.recorded[n] === fields[n]));
  }
  console.log(`${fixture.name}, ${alter}: status ${response[0]}, ${quote.length}-byte quote`);

  if (alter !== "none") continue;
  // One bit changed anywhere that is signed, or in a signature, must fail some step. The places: the header,
  // the report (a measurement, the REPORTDATA), the quote's signature, the attestation key, the quoting
  // enclave's report and its signature, and each of the three certificates.
  const pem = new TextDecoder("latin1").decode(quote);
  const certs = [...pem.matchAll(/-----BEGIN CERTIFICATE-----/g)].map((m) => m.index + 200);
  const places = [9, 48 + 140, 48 + 530, 636 + 5, 636 + 70, 636 + 134 + 10, 636 + 134 + 130, 636 + 134 + 390, ...certs];
  for (const at of places) {
    const changed = Uint8Array.from(quote);
    // Inside base64 text a flipped bit could leave the alphabet; exchange two letters instead.
    if (certs.includes(at)) changed[at] = changed[at] === 0x41 ? 0x42 : 0x41; else changed[at] ^= 1;
    const result = await verifyQuote(changed, Date.now());
    const kept = same(Uint8Array.from(Buffer.from(result.fields.reportData || "", "hex")), data);
    expect(`a quote changed at byte ${at} was accepted`, !result.steps.every((s) => s.ok) || !kept);
  }
  const late = await verifyQuote(quote, Date.UTC(2060, 0, 1));
  expect("a quote read in 2060 was accepted", !late.steps.every((s) => s.ok));
  console.log(`changed quotes: ${places.length + 1} refused`);
}
console.log(failures ? `test-verify: ${failures} FAILED` : "test-verify: all checks passed");
process.exit(failures ? 1 : 0);
