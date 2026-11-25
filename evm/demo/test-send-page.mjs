// Runs the page for sealed transactions itself (demo/send.html: the script at its end, with the three it
// loads) under Node, with a document that is only what that script asks of one and a door that is only
// answers kept from a real one.
//
//     node demo/test-send-page.mjs                          (from evm/)
//
// test-send.mjs checks what the page computes; this checks what the page then does with it: that the
// button for sending stays shut until the key's quote has passed, that what goes to the door is sealed and
// not the transaction, and that the sender is shown the transaction's hash. The door's answer about the
// key is the one kept in verify/vectors/door/, taken as the door's answer for everybody (the kept quote
// is of a challenge made on 2026-11-25, so the door here says it makes no new quotes just now). Nothing is
// asked of anybody, and no browser is run: how the page looks is not checked.
import { readFileSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const root = join(dirname(fileURLToPath(import.meta.url)), "..", "..");
const demo = join(root, "evm", "demo"), kept = join(root, "verify", "vectors", "door");
let failures = 0;
const expect = (what, holds) => { console.log(`  ${holds ? "ok  " : "FAIL"}  ${what}`); if (!holds) failures += 1; };

// What the page asks of an element: its text (setting it drops what was appended), a few switches, and
// the function to call on a click.
class Element {
  constructor() { this.own = ""; this.children = []; this.className = ""; this.disabled = false; this.hidden = false; this.value = ""; this.on = {}; }
  get textContent() { return this.own + this.children.map((c) => c.textContent).join(""); }
  set textContent(text) { this.own = String(text); this.children = []; }
  append(...nodes) { this.children.push(...nodes); }
  replaceChildren(...nodes) { this.own = ""; this.children = nodes; }
  addEventListener(kind, f) { this.on[kind] = f; }
}
const html = readFileSync(join(demo, "send.html"), "utf8");
const inline = html.slice(html.lastIndexOf("<script>") + 8, html.lastIndexOf("</script>"));
const record = readFileSync(join(kept, "record.json"), "utf8"), quote = readFileSync(join(kept, "builder.quote"));
const answer = readFileSync(join(kept, "sealing.json"), "utf8");
const DOOR = "https://door.example";
const reply = (status, body) => ({
  ok: status >= 200 && status < 300, status,
  json: async () => JSON.parse(body), arrayBuffer: async () => Uint8Array.from(body).buffer,
});

// One page, opened: `door` says what the door at /sealed answers, and may change the answer about the key.
async function opened(door) {
  const elements = {}, asked = [];
  for (const id of html.matchAll(/ id="([a-z]+)"/g)) elements[id[1]] = new Element();
  elements.minutes.value = "5";
  elements.send.disabled = true; elements.ask.disabled = true; elements.steps.hidden = true;
  globalThis.document = {
    getElementById: (id) => elements[id],
    createElement: () => new Element(),
  };
  globalThis.fetch = async (url, options = {}) => {
    asked.push({ url, method: options.method || "GET", body: options.body });
    if (url === "live/builder.json") return reply(200, record);
    if (url === "live/" + JSON.parse(record).quote) return reply(200, quote);
    if (url === "live/door.json") return reply(200, JSON.stringify({ door: DOOR + "/" }));
    if (url === DOOR + "/key") return options.method === "POST" ? reply(429, "{}") : reply(200, door.key || answer);
    if (url === DOOR + "/sealed") return reply(200, JSON.stringify(door.sealed));
    return reply(404, "{}");
  };
  for (const name of ["verify.js", "seal.js", "send.js"]) new Function(readFileSync(join(demo, name), "utf8"))();
  new Function(inline)();
  for (let i = 0; i < 200 && !elements.send.on.click; i++) await new Promise((r) => setTimeout(r, 5));
  return { elements, asked };
}

// The kept quote's certificates are judged at the day it was made, as in test-send.mjs.
Date.now = () => Date.parse("2026-11-25T04:00:00Z");
const raw = "0x02f8b2018216ca847735940084814c30418301adb094dac17f958d2ee523a2206206994597c13d831ec780b844a9059cbb000000000000000000000000ff3f306410ff2f1060ad5fa780283c54a5d9155300000000000000000000000000000000000000000000000000000000089927c1c001a0cf178a56c3df4bf7e4288a7342cb3b20881e741809ba998155a7056d6c6767f7a04abc6d613ba260d831925c8dbe17855035e217da591493121c2a601d99bf1678";
const hash = "0x7ee564331204090b3a26b4dc425c35cb9cf8891a449efce7ec3faa40782556bd";
const length = (raw.length - 2) / 2;

{
  const { elements: el, asked } = await opened({ sealed: { status: 0, means: "kept" } });
  expect("opened: the key can be asked for, and nothing can be sent yet", !el.ask.disabled && el.send.disabled && !!el.send.on.click);
  el.tx.value = raw;
  await el.send.on.click();
  expect("a press on sending before any key was checked sends nothing", !asked.some((a) => a.url.endsWith("/sealed")));
  await el.ask.on.click();
  expect("the key asked for and every check holding: sending is open, and the page says the quote is the door's for everybody",
         !el.send.disabled && el.state.className === "verdict good" && el.steps.children.length === 11 &&
         el.steps.children.every((row) => row.className === "row") && el.state.textContent.includes("latest for everybody"));
  await el.send.on.click();
  const went = asked.filter((a) => a.url === DOOR + "/sealed");
  const body = went.length === 1 ? went[0].body : new Uint8Array(0);
  expect("one thing went to the door: the kind's name, 32 bytes of the sender's, and the message with 8 before it and 16 after",
         went.length === 1 && went[0].method === "POST" && body.length === 5 + 32 + 8 + length + 16 &&
         new TextDecoder().decode(body.subarray(0, 5)) === "JSEA1");
  const plain = Buffer.from(raw.slice(2), "hex"), sent = Buffer.from(body);
  expect("no eight bytes in a row of the transaction are in it", ![...Array(length - 8).keys()].some((i) => sent.includes(plain.subarray(i, i + 8))));
  expect("the sender is told it was handed in, until which slot, and the transaction's hash",
         el.sent.textContent.startsWith("Handed in.") && el.sent.textContent.includes("until slot " + (Math.floor((Date.now() / 1000 - 1606824023) / 12) + 25)) &&
         el.sent.textContent.endsWith(hash) && !el.send.disabled);
}
{
  const { elements: el } = await opened({ sealed: { status: 3, means: "it is holding as many as it will" } });
  await el.ask.on.click();
  el.tx.value = raw;
  await el.send.on.click();
  expect("a builder that did not keep it: the sender is told so, and shown no hash",
         el.sent.textContent === "The builder did not keep it: it is holding as many as it will." && !el.sent.textContent.includes("0x"));
  el.tx.value = "0x03" + "ab".repeat(200);
  await el.send.on.click();
  expect("a transaction with blobs: refused on the page, with why", el.sent.textContent.includes("blobs"));
}
{
  const other = JSON.parse(answer);
  other.key = other.key.slice(0, -1) + (other.key.endsWith("0") ? "1" : "0");
  const { elements: el, asked } = await opened({ sealed: { status: 0, means: "kept" }, key: JSON.stringify(other) });
  await el.ask.on.click();
  el.tx.value = raw;
  await el.send.on.click();
  expect("a door that serves another key with the same quote: the page says a check fails, and sends nothing",
         el.state.className === "verdict bad" && el.send.disabled && !asked.some((a) => a.url.endsWith("/sealed")) &&
         el.steps.children.some((row) => row.className === "row fails"));
}
console.log(failures ? `test-send-page: ${failures} failed` : "test-send-page: all as it should be");
process.exit(failures ? 1 : 0);
