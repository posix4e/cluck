// Checks one block the builder built, from the files builder/shadow keeps for it (N.req, N.reply, N.quote,
// N.json), the way built.html does, and then checks that the same files with any one of them changed are
// refused.
//
//     node demo/test-built.mjs DIR N
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
for (const file of ["verify.js", "built.js"]) new Function(readFileSync(join(here, file), "utf8"))();
const { checkBuilt } = globalThis.Built;
const { hex } = globalThis.TdxQuote;
const [dir, name] = process.argv.slice(2);
if (!dir || !name) { console.log("usage: node demo/test-built.mjs DIR N"); process.exit(2); }
const bytes = (ending) => new Uint8Array(readFileSync(join(dir, `${name}.${ending}`)));
const meta = JSON.parse(readFileSync(join(dir, `${name}.json`), "utf8"));
const set = { request: bytes("req"), reply: bytes("reply"), quote: bytes("quote"),
              challenge: Uint8Array.from(Buffer.from(meta.challenge.slice(2), "hex")) };
let failures = 0;
const expect = (what, ok) => { if (!ok) { failures++; console.log("FAILED: " + what); } };

const { steps, built, asked, fields } = await checkBuilt(set, Date.now());
for (const s of steps) console.log(`  ${s.ok ? "ok " : "NO "} ${s.title}: ${s.detail}`);
expect("every step", steps.length === 11 && steps.every((s) => s.ok));
expect("the block the operator's file names", "0x" + hex(built.hash) === meta.hash && Number(built.number) === meta.number &&
       Number(asked.slot) === meta.slot);
console.log(`block ${built.number}, slot ${asked.slot}, ${built.transactions} transactions, value ${built.value} wei, ` +
            `MRTD ${fields.MRTD.slice(0, 16)}…`);

// One bit changed in the request, the reply, the challenge or the signed part of the quote: some step fails.
const changes = [["request", 100], ["request", set.request.length - 1], ["reply", 0], ["reply", 40],
                 ["reply", set.reply.length - 1], ["challenge", 5], ["quote", 48 + 530]];
for (const [part, at] of changes) {
  const changed = { ...set, [part]: Uint8Array.from(set[part]) };
  changed[part][at] ^= 1;
  const again = await checkBuilt(changed, Date.now());
  expect(`${part} changed at byte ${at} was accepted`, !again.steps.every((s) => s.ok));
}
console.log(`changed files: ${changes.length} refused`);
console.log(failures ? `test-built: ${failures} FAILED` : "test-built: all checks passed");
process.exit(failures ? 1 : 0);
