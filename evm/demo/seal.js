// Seals a transaction to a builder's key, so that only the machine holding the other half can read it.
//
// The format is the machine's (Evm/Seal.lean): HPKE (RFC 9180) in base mode with X25519, HKDF-SHA-256 and
// ChaCha20-Poly1305, `info` the words "sealed transaction v1", no data beside the message; and what is
// sealed is eight bytes, the last slot the transaction may go in a block for, then the transaction as it
// goes on the wire. X25519, HMAC and SHA-256 are the browser's own. ChaCha20-Poly1305 is not something
// browsers offer, so it is written out here from RFC 8439, and `scripts/seal-check` holds it to node's and
// the whole of this to OpenSSL's HPKE.
//
// Nothing here is constant-time, and it need not be on the sender's side for the secrets it holds: a key
// made for one message and thrown away, and the sender's own transaction.
//
// The same file runs under node (scripts/seal-check).
"use strict";

(function (scope) {
  const subtle = crypto.subtle;
  const text = (s) => new TextEncoder().encode(s);
  const concat = (...parts) => {
    const out = new Uint8Array(parts.reduce((n, p) => n + p.length, 0));
    let at = 0;
    for (const p of parts) { out.set(p, at); at += p.length; }
    return out;
  };
  const hmac = async (key, data) => {
    const k = await subtle.importKey("raw", key.length ? key : new Uint8Array(32), { name: "HMAC", hash: "SHA-256" }, false, ["sign"]);
    return new Uint8Array(await subtle.sign("HMAC", k, data));
  };

  // ---- ChaCha20 (RFC 8439, 2.3): a block of key stream from a key, a counter and a nonce.

  const rotl = (x, n) => ((x << n) | (x >>> (32 - n))) >>> 0;
  function quarter(s, a, b, c, d) {
    s[a] = (s[a] + s[b]) >>> 0; s[d] = rotl(s[d] ^ s[a], 16);
    s[c] = (s[c] + s[d]) >>> 0; s[b] = rotl(s[b] ^ s[c], 12);
    s[a] = (s[a] + s[b]) >>> 0; s[d] = rotl(s[d] ^ s[a], 8);
    s[c] = (s[c] + s[d]) >>> 0; s[b] = rotl(s[b] ^ s[c], 7);
  }
  function block(key, counter, nonce) {
    const view = (b) => new DataView(b.buffer, b.byteOffset, b.byteLength);
    const start = new Uint32Array(16);
    start.set([0x61707865, 0x3320646e, 0x79622d32, 0x6b206574]);
    for (let i = 0; i < 8; i++) start[4 + i] = view(key).getUint32(4 * i, true);
    start[12] = counter;
    for (let i = 0; i < 3; i++) start[13 + i] = view(nonce).getUint32(4 * i, true);
    const s = start.slice();
    for (let round = 0; round < 10; round++) {
      quarter(s, 0, 4, 8, 12); quarter(s, 1, 5, 9, 13); quarter(s, 2, 6, 10, 14); quarter(s, 3, 7, 11, 15);
      quarter(s, 0, 5, 10, 15); quarter(s, 1, 6, 11, 12); quarter(s, 2, 7, 8, 13); quarter(s, 3, 4, 9, 14);
    }
    const out = new Uint8Array(64);
    for (let i = 0; i < 16; i++) view(out).setUint32(4 * i, (s[i] + start[i]) >>> 0, true);
    return out;
  }
  function chacha20(key, counter, nonce, data) {
    const out = new Uint8Array(data.length);
    for (let at = 0; at < data.length; at += 64) {
      const stream = block(key, counter + at / 64, nonce);
      for (let i = 0; i < 64 && at + i < data.length; i++) out[at + i] = data[at + i] ^ stream[i];
    }
    return out;
  }

  // ---- Poly1305 (RFC 8439, 2.5): a tag over a message under a key used once. On big numbers.

  function poly1305(key, message) {
    const number = (bytes) => bytes.reduceRight((n, b) => (n << 8n) | BigInt(b), 0n);
    const r = number(key.subarray(0, 16)) & 0x0ffffffc0ffffffc0ffffffc0fffffffn;
    const s = number(key.subarray(16, 32));
    const p = (1n << 130n) - 5n;
    let acc = 0n;
    for (let at = 0; at < message.length; at += 16) {
      const piece = message.subarray(at, Math.min(at + 16, message.length));
      acc = ((acc + number(piece) + (1n << BigInt(8 * piece.length))) * r) % p;
    }
    let tag = (acc + s) & ((1n << 128n) - 1n);
    const out = new Uint8Array(16);
    for (let i = 0; i < 16; i++) { out[i] = Number(tag & 0xffn); tag >>= 8n; }
    return out;
  }

  // ---- The two together (RFC 8439, 2.8): the hidden bytes, then sixteen bytes of tag.

  function sealWith(key, nonce, aad, plain) {
    const hidden = chacha20(key, 1, nonce, plain);
    const pad = (n) => new Uint8Array((16 - (n % 16)) % 16);
    const length = (n) => { const b = new Uint8Array(8); new DataView(b.buffer).setBigUint64(0, BigInt(n), true); return b; };
    const tag = poly1305(block(key, 0, nonce).subarray(0, 32),
      concat(aad, pad(aad.length), hidden, pad(hidden.length), length(aad.length), length(hidden.length)));
    return concat(hidden, tag);
  }

  // ---- HPKE, base mode, one message (RFC 9180, 4.1, 5.1, 5.2).

  const two = (n) => new Uint8Array([n >> 8, n & 255]);
  const KEM = concat(text("KEM"), two(0x0020));
  const SUITE = concat(text("HPKE"), two(0x0020), two(0x0001), two(0x0003));
  const labeledExtract = (suite, salt, label, material) => hmac(salt, concat(text("HPKE-v1"), suite, text(label), material));
  async function labeledExpand(suite, key, label, info, length) {
    // One block of HKDF's expansion is all that is ever asked for here.
    const out = await hmac(key, concat(two(length), text("HPKE-v1"), suite, text(label), info, new Uint8Array([1])));
    return out.subarray(0, length);
  }

  // A message sealed to `recipient` (32 bytes): the sender's public half, then the sealed message.
  // `ephemeral`, for tests only, is a key pair to use where a fresh one would be made.
  async function hpkeSeal(recipient, info, aad, plain, ephemeral) {
    const pair = ephemeral || await subtle.generateKey({ name: "X25519" }, true, ["deriveBits"]);
    const enc = new Uint8Array(await subtle.exportKey("raw", pair.publicKey));
    const theirs = await subtle.importKey("raw", recipient, { name: "X25519" }, false, []);
    const dh = new Uint8Array(await subtle.deriveBits({ name: "X25519", public: theirs }, pair.privateKey, 256));
    if (dh.every((b) => b === 0)) throw new Error("a key that no message can be sealed to");
    const shared = await labeledExpand(KEM, await labeledExtract(KEM, new Uint8Array(0), "eae_prk", dh), "shared_secret",
      concat(enc, recipient), 32);
    const context = concat(new Uint8Array([0]), await labeledExtract(SUITE, new Uint8Array(0), "psk_id_hash", new Uint8Array(0)),
      await labeledExtract(SUITE, new Uint8Array(0), "info_hash", info));
    const secret = await labeledExtract(SUITE, shared, "secret", new Uint8Array(0));
    const key = await labeledExpand(SUITE, secret, "key", context, 32);
    const nonce = await labeledExpand(SUITE, secret, "base_nonce", context, 12);
    return concat(enc, sealWith(key, nonce, aad, plain));
  }

  // A transaction sealed for a builder: what follows "JSEA1" in the request that hands it in.
  // `key` is the builder's sealing key, `lastSlot` the last slot it may go in a block for, `transaction`
  // the signed transaction's bytes.
  async function sealTransaction(key, lastSlot, transaction) {
    if (key.length !== 32) throw new Error("a sealing key is 32 bytes");
    const slot = new Uint8Array(8);
    new DataView(slot.buffer).setBigUint64(0, BigInt(lastSlot), false);
    return hpkeSeal(key, text("sealed transaction v1"), new Uint8Array(0), concat(slot, transaction));
  }

  scope.cluckSeal = { sealTransaction, hpkeSeal, sealWith };
})(typeof window !== "undefined" ? window : globalThis);
