// Runs what the page for sealed transactions does (demo/send.js, with demo/verify.js and demo/seal.js)
// under Node.
//
//     node demo/test-send.mjs                               (from evm/)
//
// checks the door's answers kept in verify/vectors/door/, which a guest in a trust domain on Compute
// Engine gave through builder/door on 2026-11-25: the sealing key with its quote must pass against the
// record and the quote beside it, and the same with one thing wrong at a time must not. Nothing is asked
// of anybody.
//
//     node demo/test-send.mjs DOOR RECORD.json RECORD.quote
//
// does it against a door that is running (http://127.0.0.1:8080, say) and the record of the guest behind
// it: asks for the key, checks it, seals a run of random bytes as if it were a transaction, hands it in,
// and wants the guest's answer that it kept it. Then hands in the same sealed to another key, which the
// guest must say does not open.
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..", "..");
const demo = join(root, "evm", "demo");
for (const name of ["verify.js", "seal.js", "send.js"]) new Function(readFileSync(join(demo, name), "utf8"))();
const { checkKey, slotAt, lastSlot, transaction, hashOf, sealed, askKey, handIn } = globalThis.SendCheck;
let failures = 0;
const expect = (what, holds) => { console.log(`  ${holds ? "ok  " : "FAIL"}  ${what}`); if (!holds) failures += 1; };
const bytes = (path) => Uint8Array.from(readFileSync(path));
const flipped = (text) => text.slice(0, -1) + (text.endsWith("0") ? "1" : "0");

if (process.argv.length > 2) {
  const [door, recordPath, quotePath] = process.argv.slice(2);
  const record = JSON.parse(readFileSync(recordPath, "utf8")), recordQuote = bytes(quotePath);
  const { answer, sent } = await askKey(door);
  const checked = await checkKey(record, recordQuote, answer, sent, Date.now());
  for (const s of checked.steps) console.log(`    ${s.ok ? "holds" : "FAILS"}  ${s.title}`);
  expect("the key the door served is the guest's sealing key, by a quote made for this asking", checked.good && sent !== null);
  if (checked.good) {
    const made = crypto.getRandomValues(new Uint8Array(300));
    made[0] = 2;
    const last = lastSlot(Date.now(), 1);
    const said = await handIn(door, await sealed(checked.key, last, made));
    expect(`sealed to that key and handed in: the guest says "${said.means}"`, said.status === 0);
    const other = await handIn(door, await sealed(crypto.getRandomValues(new Uint8Array(32)), last, made));
    expect(`sealed to another key: the guest says "${other.means}"`, other.status === 1);
  }
} else {
  const kept = join(root, "verify", "vectors", "door");
  const record = JSON.parse(readFileSync(join(kept, "record.json"), "utf8")), recordQuote = bytes(join(kept, "builder.quote"));
  const answer = JSON.parse(readFileSync(join(kept, "sealing.json"), "utf8"));
  const forBids = JSON.parse(readFileSync(join(kept, "builder.json"), "utf8"));
  const when = Date.parse("2026-11-25T04:00:00Z");
  const sent = Uint8Array.from(Buffer.from(answer.challenge, "hex"));

  const real = await checkKey(record, recordQuote, answer, sent, when);
  for (const s of real.steps) console.log(`    ${s.ok ? "holds" : "FAILS"}  ${s.title}`);
  expect("the door's answer as kept stands, and gives the key", real.good && real.steps.length === 12 && real.key.length === 32);
  const forAll = await checkKey(record, recordQuote, answer, null, when);
  expect("the same taken as the door's answer for everybody", forAll.good && forAll.steps.length === 11);

  const wrong = [
    ["another key with the same quote", record, recordQuote, { ...answer, key: flipped(answer.key) }, sent],
    ["a quote made for somebody else's asking", record, recordQuote, answer, sent.map((b, i) => (i === 0 ? b ^ 1 : b))],
    ["a challenge said to be another", record, recordQuote, { ...answer, challenge: flipped(answer.challenge) }, null],
    // The machine's own quote of its other key: real, of this machine, and not an answer about sealing.
    ["the quote of the key for bids, offered as the sealing key's", record, recordQuote,
     { ...forBids, key: forBids.key.slice(0, 64) }, null],
    ["a record that names another program", { ...record, rtmr1: flipped(record.rtmr1) }, recordQuote, answer, sent],
    ["a kept quote with a byte of its report changed", record, recordQuote.map((b, i) => (i === 300 ? b ^ 1 : b)), answer, sent],
    ["a kept quote of other firmware", record, recordQuote.map((b, i) => (i === 48 + 136 ? b ^ 1 : b)), answer, sent],
    ["a quote with a byte of its report changed", record, recordQuote,
     { ...answer, quote: Buffer.from(Uint8Array.from(Buffer.from(answer.quote, "base64")).map((b, i) => (i === 300 ? b ^ 1 : b))).toString("base64") }, sent],
    ["a quote cut short", record, recordQuote, { ...answer, quote: answer.quote.slice(0, 900) }, sent],
    ["a key that is not hexadecimal", record, recordQuote, { ...answer, key: "zz" }, sent],
    ["no quote at all", record, recordQuote, { key: answer.key, challenge: answer.challenge }, sent],
    ["a certificate chain judged ten years on", record, recordQuote, answer, sent, when + 10 * 365 * 86400 * 1000],
  ];
  for (const [what, r, q, a, s, at] of wrong) {
    const got = await checkKey(r, q, a, s, at || when);
    expect(`${what}: refused, and no key given`, !got.good && got.key === null);
  }

  // The slots and the transaction's first look.
  const now = (1606824023 + 12 * 1000 + 5) * 1000;
  expect("the slot under way, and the last of the next minute and of the next hour",
         slotAt(now) === 1000 && lastSlot(now, 1) === 1005 && lastSlot(now, 60) === 1300 && lastSlot(now, 600) === 1300 && lastSlot(now, 0) === 1005);
  const refused = (given) => { try { transaction(given); return false; } catch { return true; } };
  expect("what could be a signed transaction is taken", transaction("0x02" + "ab".repeat(120)).length === 121 && transaction("f8" + "ab".repeat(100)).length === 101);
  expect("what could not is refused: too short, with blobs, of no known kind, not hexadecimal, too long",
         refused("0x02abcd") && refused("03" + "ab".repeat(120)) && refused("7f" + "ab".repeat(120)) && refused("0xzz") &&
         refused("02" + "ab".repeat(128 * 1024)));
  // The hash: of nothing and of three letters, as Keccak's authors give them, and of three transactions of
  // mainnet's block 26494797 (of the old kind, of the usual one, and one that sets code), by the names the
  // chain knows them by. All three are longer than the 136 bytes taken at a time.
  const hashed = (given) => Buffer.from(hashOf(typeof given === "string" ? transaction(given) : given)).toString("hex");
  expect("the hash of nothing and of abc",
         hashed(new Uint8Array(0)) === "c5d2460186f7233c927e7db2dcc703c0e500b653ca82273b7bfad8045d85a470" &&
         hashed(new TextEncoder().encode("abc")) === "4e03657aea45a94fc7d47ba826c8d667c0d1e6e33a64a036ec44f58fa12d6c45");
  expect("the hash of 135, 136 and 137 bytes differs, and each is 32 bytes",
         new Set([135, 136, 137].map((n) => hashed(new Uint8Array(n)))).size === 3 && hashOf(new Uint8Array(136)).length === 32);
  const landed = [
    ["bb6f1ef18e9b430c78026088a7632db36e4131f9bc287296dc1fb6ecaccd3cd3", "0xf8ab82138a8408d7f4a783010c2f94a0b86991c6218b36c1d19d4a2e9eb0ce3606eb4880b844a9059cbb0000000000000000000000003cc936b795a188f0e246cbb2d74c5bd190aecf18000000000000000000000000000000000000000000000000000000009c1ac4c026a0f10017ff8c02e22559249178d8e6192ba7157f84918a6d29218f270466b8d3cea025aabc5e800a2715e700b39a6af137c09634704317a498a1253798a1ebaf4d9b"],
    ["7ee564331204090b3a26b4dc425c35cb9cf8891a449efce7ec3faa40782556bd", "0x02f8b2018216ca847735940084814c30418301adb094dac17f958d2ee523a2206206994597c13d831ec780b844a9059cbb000000000000000000000000ff3f306410ff2f1060ad5fa780283c54a5d9155300000000000000000000000000000000000000000000000000000000089927c1c001a0cf178a56c3df4bf7e4288a7342cb3b20881e741809ba998155a7056d6c6767f7a04abc6d613ba260d831925c8dbe17855035e217da591493121c2a601d99bf1678"],
    ["febec7d60ef2c54eadd3748e1349526bf5a09a89ca762069e663e583f40eca1a", "0x04f8f3018303427384018b2b2d840899309c83010f2c944de23f3f0fb3318287378adbde030cf61714b2f380a4c4d66de8000000000000000000000000333333320bb4a0345a7a102c49c72b37647aa088c0f85ff85d019484d05511614272694d3a9cebe896514dbde51f40830b41ae01a005516027f713d59153fc9e6b6ae30740dde62c688d4bd6814163a2c9877cda20a04a9a52648d5b72f988765ac7201bdd94118c33cd3c496f181d3f739b09ffb05801a0f7cfff8dc13226e23d51761bfffe097fc414c16d1e6b819c2b1fae7fe0e801d3a058e798db2ff5e4ac25baa6d677e5aaf84438209eb0d91d8cbdda4b0dee3ea0d8"],
  ];
  expect("the hash of three transactions that are in the chain is the one the chain has", landed.every(([hash, raw]) => hashed(raw) === hash));
  // Sealed here, the request is the kind's name, the sender's 32 bytes, and the message with 8 bytes of slot
  // before it and 16 of tag after.
  const request = await sealed(real.key, 1005, transaction("0x02" + "ab".repeat(120)));
  expect("a sealed transaction is as long as it should be and begins with its kind", request.length === 5 + 32 + 8 + 121 + 16 &&
         new TextDecoder().decode(request.subarray(0, 5)) === "JSEA1");
  const again = await sealed(real.key, 1005, transaction("0x02" + "ab".repeat(120)));
  expect("sealed twice, nothing after the kind's name is the same", !request.subarray(5, 37).every((b, i) => b === again[5 + i]));
}
console.log(failures ? `test-send: ${failures} failed` : "test-send: all as it should be");
process.exit(failures ? 1 : 0);
