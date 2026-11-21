// Reads what the builder in the trust domain was asked and what it answered, and checks that a TDX quote
// is for exactly that. Used by built.html in a browser and by test-built.mjs under node, after verify.js.
//
// The three things checked, besides the quote itself (verify.js): the quote's REPORTDATA is
// SHA-256(challenge ‖ request) ‖ SHA-256(reply), as Evm/Attest.lean makes it; the challenge is the hash of
// the block's parent, read out of the header in the reply, so the quote is no older than the parent; and
// the reply is a block that was built, for the slot the request names. Not checked: the builder's BLS
// signature over the bid (bid-verify does that), and whether the block is on the chain, which is for
// whoever reads this to look up somewhere they trust.
"use strict";

(function (scope) {
  const { verifyQuote, sha256, hex, concat, same } = scope.TdxQuote;
  const text = (bytes) => String.fromCharCode(...bytes);
  const number = (bytes) => bytes.reduce((n, b) => n * 256n + BigInt(b), 0n);

  // One RLP item at `at`: where its payload starts and ends, and whether it is a list.
  function item(bytes, at) {
    const b = bytes[at];
    if (b === undefined) throw new Error("the header is cut short");
    if (b < 0x80) return { list: false, start: at, end: at + 1 };
    const long = (base) => {
      const count = b - base;
      const size = Number(number(bytes.subarray(at + 1, at + 1 + count)));
      return { start: at + 1 + count, end: at + 1 + count + size };
    };
    const span = b < 0xb8 ? { start: at + 1, end: at + 1 + b - 0x80 } : b < 0xc0 ? long(0xb7)
      : b < 0xf8 ? { start: at + 1, end: at + 1 + b - 0xc0 } : long(0xf7);
    if (span.end > bytes.length) throw new Error("the header is cut short");
    return { list: b >= 0xc0, ...span };
  }

  // The fields of a block header, as byte strings.
  function headerFields(bytes) {
    const whole = item(bytes, 0);
    if (!whole.list || whole.end !== bytes.length) throw new Error("the header is not one RLP list");
    const fields = [];
    for (let at = whole.start; at < whole.end;) {
      const field = item(bytes, at);
      fields.push(bytes.subarray(field.start, field.end));
      at = field.end;
    }
    if (fields.length < 16) throw new Error("the header has too few fields");
    return fields;
  }

  // A request for a bid (Evm/Bid.lean): which slot and proposer it names.
  function readRequest(request) {
    if (request.length < 69 || text(request.subarray(0, 5)) !== "JBID2") throw new Error("not a request for a bid");
    return { slot: number(request.subarray(5, 13)), proposerKey: request.subarray(13, 61),
             allowedMs: Number(number(request.subarray(65, 69))) };
  }

  // The reply to one (Evm/Build.lean, then the builder's key and signature).
  function readReply(reply) {
    if (reply.length < 33) throw new Error("the reply is cut short");
    if (reply[0] !== 0) return { status: reply[0] };
    const u32 = (at) => Number(number(reply.subarray(at, at + 4)));
    const count = u32(105);
    let at = 109 + 4 * count;
    const headerSize = u32(at);
    const header = reply.subarray(at + 4, at + 4 + headerSize);
    at += 4 + headerSize;
    const requests = u32(at);
    at += 4;
    for (let i = 0; i < requests; i++) at += 4 + u32(at);
    if (reply.length !== at + 144) throw new Error("the reply does not end with a key and a signature");
    const fields = headerFields(header);
    return {
      status: 0, hash: reply.subarray(1, 33), stateRoot: reply.subarray(33, 65),
      value: number(reply.subarray(65, 97)), gasUsed: number(reply.subarray(97, 105)), transactions: count,
      parentHash: fields[0], feeRecipient: fields[2], number: number(fields[8]), gasLimit: number(fields[9]),
      timestamp: number(fields[11]), extraData: fields[12],
      builderKey: reply.subarray(at, at + 48), signature: reply.subarray(at + 48, at + 144),
    };
  }

  // Everything checked about one block built: the quote's own steps, then the three above.
  async function checkBuilt({ request, reply, quote, challenge }, now) {
    const { fields, steps } = await verifyQuote(quote, now);
    let asked = null, built = null;
    try {
      asked = readRequest(request);
      built = readReply(reply);
    } catch (error) {
      steps.push({ title: "The request and the reply could be read", ok: false, detail: String(error.message || error) });
      return { fields, steps, asked, built };
    }
    const data = Uint8Array.from((fields.reportData || "").match(/../g) || [], (h) => parseInt(h, 16));
    const wanted = await sha256(concat(challenge, request));
    const answered = await sha256(reply);
    steps.push({
      title: "The quote is for this request",
      ok: data.length === 64 && same(wanted, data.subarray(0, 32)),
      detail: `SHA-256 of the 32-byte challenge and the ${request.length}-byte request, computed here: ${hex(wanted)}`,
    }, {
      title: "The quote is for this reply",
      ok: data.length === 64 && same(answered, data.subarray(32, 64)),
      detail: `SHA-256 of the ${reply.length}-byte reply, computed here: ${hex(answered)}`,
    }, {
      title: "The reply is a block that was built",
      ok: built.status === 0,
      detail: built.status === 0 ? `status 0, block ${built.number} for slot ${asked.slot}`
        : `status ${built.status}: nothing was built`,
    });
    if (built.status === 0) {
      steps.push({
        title: "The challenge is the hash of the block's parent",
        ok: same(challenge, built.parentHash),
        detail: "so the quote was made after the parent block existed: " + hex(built.parentHash),
      });
    }
    return { fields, steps, asked, built };
  }

  scope.Built = { checkBuilt, readRequest, readReply };
})(typeof window !== "undefined" ? window : globalThis);
