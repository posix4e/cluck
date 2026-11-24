// Checks a quote kept in a file the way the page does, with verify.js, and prints what it says.
//
//     node demo/check-quote.mjs QUOTE-FILE [REPORT-DATA-HEX]          (from evm/)
//
// Every step of verify.js must hold: the quote's signature, the quoting enclave that vouches for the key,
// that enclave being Intel's, the processor's certificate, the chain to Intel's root, and the trust
// domain not being in debug mode. With REPORT-DATA-HEX, the 64 bytes the quote carries must be those.
// What it does not say is which program the quote is of: that is the measurements it prints, for
// scripts/gce-measure to compare with an image. Nor does it ask Intel whether the processor's
// certificate has been revoked or its firmware is out of date. Exit status 0 only if every step holds.
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
new Function(readFileSync(join(here, "verify.js"), "utf8"))();
const { verifyQuote } = globalThis.TdxQuote;
if (process.argv.length < 3) { console.log("usage: node demo/check-quote.mjs QUOTE-FILE [REPORT-DATA-HEX]"); process.exit(2); }
const quote = Uint8Array.from(readFileSync(process.argv[2]));
const { fields, steps } = await verifyQuote(quote, Date.now());
for (const s of steps) console.log(`  ${s.ok ? "holds" : "FAILS"}  ${s.title}: ${s.detail}`);
let good = steps.length === 7 && steps.every((s) => s.ok);
for (const name of ["MRTD", "RTMR0", "RTMR1", "RTMR2", "RTMR3", "reportData"]) console.log(`  ${name}: ${fields[name]}`);
if (process.argv[3]) {
  const same = fields.reportData === process.argv[3].toLowerCase().replace(/^0x/, "");
  console.log(`  ${same ? "holds" : "FAILS"}  The 64 bytes it carries are the ones given`);
  good = good && same;
}
console.log(good ? "the quote stands: a TDX trust domain with these measurements, not in debug mode, made it"
                 : "the quote does NOT stand");
process.exit(good ? 0 : 1);
