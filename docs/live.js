// What the page at live.html checks of the builder's guest, kept apart from the page so that Node can run
// it too (evm/demo/test-live.mjs). It needs verify.js loaded first (TdxQuote).
//
// A record says which guest is meant: its key for bids, the challenge the key was asked for with, and the
// RTMR1 worked out for the image (scripts/gce-measure). The quote is the guest's own. Every check is of
// the quote against the record, and each comes back with whether it holds and what was seen.
(function (scope) {
  const { verifyQuote, sha256, hex, concat } = scope.TdxQuote;
  const unhex = (text) => {
    const digits = String(text).replace(/^0x/, "");
    if (!/^([0-9a-fA-F]{2})*$/.test(digits)) throw new Error("not hexadecimal: " + String(text).slice(0, 20));
    return Uint8Array.from(digits.match(/../g) || [], (pair) => parseInt(pair, 16));
  };

  async function checkLive(record, quote, now) {
    const { fields, steps } = await verifyQuote(quote, now);
    const out = steps.map((s) => ({ title: s.title, ok: !!s.ok, detail: s.detail }));
    // The seven of verify.js; fewer means it stopped at something it could not read.
    const whole = steps.length === 7;
    let key, challenge;
    try {
      key = unhex(record.builder); challenge = unhex(record.challenge);
      if (key.length !== 48 || challenge.length !== 32) throw new Error("a key is 48 bytes and a challenge 32");
      // evm/Evm/Attest.lean: SHA-256 of the challenge and the question, then SHA-256 of the answer.
      const wanted = hex(concat(await sha256(concat(challenge, new TextEncoder().encode("JKEY1"))), await sha256(key)));
      out.push({ title: "The quote is of this machine's answer that its key for bids is the one shown",
                 ok: fields.reportData === wanted,
                 detail: "its 64 bytes of report data are SHA-256 of the challenge and the question, and SHA-256 of the key" });
    } catch (error) {
      out.push({ title: "The record's key and challenge could be read", ok: false, detail: String(error.message || error) });
    }
    out.push({ title: "The program measured is the one the record names",
               ok: !!fields.RTMR1 && fields.RTMR1 === String(record.rtmr1 || "").toLowerCase(),
               detail: "RTMR1 in the quote " + String(fields.RTMR1 || "").slice(0, 24) + "…; the record's, worked out from the image's file, " +
                       String(record.rtmr1 || "").slice(0, 24) + "…" });
    out.push({ title: "It never left the firmware, and no second program was measured",
               ok: /^0{96}$/.test(fields.RTMR2 || "") && /^0{96}$/.test(fields.RTMR3 || ""),
               detail: "RTMR2 and RTMR3 are nothing" });
    return { fields, steps: out, good: whole && out.every((s) => s.ok) };
  }

  scope.LiveCheck = { checkLive, unhex };
})(typeof window !== "undefined" ? window : globalThis);
