// What the page send.html does with the builder's door (evm/builder/door), kept apart from the page so
// that Node can run it too (demo/test-send.mjs). It needs verify.js (TdxQuote) and seal.js (cluckSeal)
// loaded first.
//
// The door is on the untrusted side: it carries a sealed transaction to the guest and could as well serve a
// key of its own. So nothing is sealed to a key until the quote that came with it has been checked here:
// that it is a real quote, that it is of the machine's answer "my key for sealing is this one", and that the
// machine it speaks for is running the program this site's record names, on the firmware of the quote this
// site keeps.
(function (scope) {
  const { verifyQuote, sha256, hex, concat } = scope.TdxQuote;
  const text = (s) => new TextEncoder().encode(s);
  const GENESIS = 1606824023;      // when the beacon chain's slot 0 began, in seconds
  const unhex = (given) => {
    const digits = String(given).trim().replace(/^0x/, "");
    if (!/^([0-9a-fA-F]{2})*$/.test(digits)) throw new Error("not hexadecimal: " + String(given).slice(0, 20));
    return Uint8Array.from(digits.match(/../g) || [], (pair) => parseInt(pair, 16));
  };
  const unbase64 = (given) => Uint8Array.from(atob(String(given)), (c) => c.charCodeAt(0));

  // `record` is live/builder.json and `recordQuote` the quote beside it; `answer` is what the door said
  // when asked for the sealing key ({ key, challenge, quote }); `sent` the 32 bytes this page asked with,
  // or null when the door's answer for everybody was taken. Comes back with each check, whether all hold,
  // and the key only if they do.
  async function checkKey(record, recordQuote, answer, sent, now) {
    const out = [];
    let key = null, fields = {};
    try {
      key = unhex(answer.key);
      const challenge = unhex(answer.challenge), quote = unbase64(answer.quote);
      if (key.length !== 32 || challenge.length !== 32) throw new Error("a sealing key is 32 bytes and a challenge 32");
      const checked = await verifyQuote(quote, now);
      fields = checked.fields;
      for (const s of checked.steps) out.push({ title: s.title, ok: !!s.ok, detail: s.detail });
      // The seven of verify.js; fewer means it stopped at something it could not read.
      if (checked.steps.length !== 7) out.push({ title: "The quote could be read to its end", ok: false, detail: "" });
      if (sent) out.push({ title: "The quote was made after this page asked",
                           ok: hex(challenge) === hex(sent), detail: "it is of the 32 random bytes this page made" });
      // evm/Evm/Attest.lean: SHA-256 of the challenge and the question, then SHA-256 of the answer.
      const wanted = hex(concat(await sha256(concat(challenge, text("JSEK1"))), await sha256(key)));
      out.push({ title: "The quote is of the machine's answer that its key for sealing is this one",
                 ok: fields.reportData === wanted,
                 detail: "its report data are SHA-256 of the challenge and the question, and SHA-256 of the key" });
      out.push({ title: "The program measured is the one the record names",
                 ok: !!fields.RTMR1 && fields.RTMR1 === String(record.rtmr1 || "").toLowerCase(),
                 detail: "RTMR1 " + String(fields.RTMR1 || "").slice(0, 24) + "…" });
      const kept = await verifyQuote(recordQuote, now);
      out.push({ title: "Its firmware and configuration are those of the quote this site keeps",
                 ok: kept.steps.length === 7 && kept.steps.every((s) => s.ok) &&
                     ["MRTD", "RTMR0"].every((n) => !!fields[n] && fields[n] === kept.fields[n]),
                 detail: "MRTD " + String(fields.MRTD || "").slice(0, 24) + "…, which the command on the other page checks against Google's statement" });
      out.push({ title: "It never left the firmware, and no second program was measured",
                 ok: /^0{96}$/.test(fields.RTMR2 || "") && /^0{96}$/.test(fields.RTMR3 || ""),
                 detail: "RTMR2 and RTMR3 are nothing" });
    } catch (error) {
      out.push({ title: "The door's answer could be read", ok: false, detail: String(error.message || error) });
    }
    const good = out.length >= 11 && out.every((s) => s.ok);
    return { steps: out, good, key: good ? key : null, fields };
  }

  // The slot under way at `now` (milliseconds), and the last slot of the next `minutes`.
  const slotAt = (now) => Math.floor((now / 1000 - GENESIS) / 12);
  const lastSlot = (now, minutes) => slotAt(now) + Math.ceil(Math.min(60, Math.max(1, minutes)) * 5);

  // A signed transaction as it goes on the wire, from hexadecimal; throws with what is wrong with it.
  function transaction(given) {
    const bytes = unhex(given);
    if (bytes.length < 60) throw new Error("that is too short to be a signed transaction");
    if (bytes.length > 128 * 1024) throw new Error("a transaction is at most 128 KB");
    if (bytes[0] === 3) throw new Error("a transaction that carries blobs cannot be sealed here: its blobs travel beside it, not in it");
    if (!(bytes[0] >= 0xc0 || bytes[0] === 1 || bytes[0] === 2 || bytes[0] === 4))
      throw new Error("that does not begin as a signed transaction does");
    return bytes;
  }

  // The request that hands a transaction in, sealed to `key`: only the machine holding the other half
  // can read anything of it but its length.
  async function sealed(key, last, bytes) {
    return concat(text("JSEA1"), await scope.cluckSeal.sealTransaction(key, BigInt(last), bytes));
  }

  // Asks the door at `door` for the key, with 32 random bytes of this page's; if new quotes are not being
  // made just now, takes the one the door has for everybody. Comes back with the answer and what was sent.
  async function askKey(door, fetcher) {
    const ask = fetcher || fetch;
    const sent = crypto.getRandomValues(new Uint8Array(32));
    let reply = await ask(door + "/key", { method: "POST", body: JSON.stringify({ challenge: hex(sent) }) });
    if (reply.status === 429) {
      reply = await ask(door + "/key");
      const answer = await reply.json();
      if (!reply.ok) throw new Error(answer.error || "the door answered " + reply.status);
      return { answer, sent: null };
    }
    const answer = await reply.json();
    if (!reply.ok) throw new Error(answer.error || "the door answered " + reply.status);
    return { answer, sent };
  }

  // Hands a sealed transaction in. Comes back with the guest's byte and what it means.
  async function handIn(door, request, fetcher) {
    const reply = await (fetcher || fetch)(door + "/sealed", { method: "POST", body: request });
    const answer = await reply.json();
    if (!reply.ok) throw new Error(answer.error || "the door answered " + reply.status);
    return answer;
  }

  scope.SendCheck = { checkKey, slotAt, lastSlot, transaction, sealed, askKey, handIn, unhex };
})(typeof window !== "undefined" ? window : globalThis);
