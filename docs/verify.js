// Checks an Intel TDX quote (version 4, ECDSA P-256) with the browser's own cryptography.
//
// What is checked: the quote's signature by its attestation key; that key's endorsement by a quoting
// enclave; that the quoting enclave is Intel's (its signer measurement); that enclave's report against the
// platform's PCK certificate; and the PCK certificate's chain to Intel's SGX root key, which is written
// below. What is not: whether the platform's firmware is current (Intel's TCB information), whether a
// certificate has been revoked, and the quoting enclave's version. Intel's DCAP library checks those.
//
// The same file runs under node for testing: node demo/test-verify.mjs
"use strict";

(function (scope) {
  // The public key of "Intel SGX Root CA", as SubjectPublicKeyInfo. From
  // https://certificates.trustedservices.intel.com/Intel_SGX_Provisioning_Certification_RootCA.pem
  // (certificate SHA-256 44a0196b2b99f889b8e149e95b807a350e7424964399e885a7cbb8ccfab674d3).
  const INTEL_ROOT_KEY =
    "3059301306072a8648ce3d020106082a8648ce3d030107034200040ba9c4c0c0c86193a3fe23d6b02cda10a8bbd4e88e48" +
    "b4458561a36e705525f567918e2edc88e40d860bd0cc4ee26aacc988e505a953558c453f6b0904ae7394";
  // Who signed Intel's TD quoting enclave, and its product number. From the "TD_QE" identity at
  // https://api.trustedservices.intel.com/tdx/certification/v4/qe/identity
  const TD_QE_SIGNER = "dc9e2a7c6f948f17474e34a7fc43ed030f7c1563f1babddf6340c82e0e54a8c5";
  const TD_QE_PRODUCT = 2;

  const hex = (bytes) => Array.from(bytes, (b) => b.toString(16).padStart(2, "0")).join("");
  const same = (a, b) => a.length === b.length && a.every((x, i) => x === b[i]);
  const sha256 = async (bytes) => new Uint8Array(await crypto.subtle.digest("SHA-256", bytes));
  const concat = (...parts) => {
    const out = new Uint8Array(parts.reduce((n, p) => n + p.length, 0));
    let at = 0;
    for (const p of parts) { out.set(p, at); at += p.length; }
    return out;
  };

  // ---- Just enough DER to take a certificate apart.

  function element(bytes, at) {
    if (at + 2 > bytes.length) throw new Error("certificate cut short");
    const tag = bytes[at];
    let length = bytes[at + 1], body = at + 2;
    if (length & 0x80) {
      const count = length & 0x7f;
      if (count === 0 || count > 3 || body + count > bytes.length) throw new Error("unsupported DER length");
      length = 0;
      for (let i = 0; i < count; i++) length = length * 256 + bytes[body++];
    }
    if (body + length > bytes.length) throw new Error("certificate cut short");
    return { tag, at, body, end: body + length };
  }

  function inside(bytes, parent) {
    const out = [];
    for (let at = parent.body; at < parent.end;) {
      const e = element(bytes, at);
      out.push(e);
      at = e.end;
    }
    return out;
  }

  const slice = (bytes, e) => bytes.subarray(e.at, e.end);

  function time(bytes, e) {
    const s = String.fromCharCode(...bytes.subarray(e.body, e.end));
    const m = e.tag === 0x17 ? /^(\d\d)(\d\d)(\d\d)(\d\d)(\d\d)(\d\d)Z$/.exec(s)
                             : /^(\d{4})(\d\d)(\d\d)(\d\d)(\d\d)(\d\d)Z$/.exec(s);
    if (!m) throw new Error("unreadable date in certificate");
    const year = e.tag === 0x17 ? (m[1] < 50 ? 2000 : 1900) + Number(m[1]) : Number(m[1]);
    return Date.UTC(year, m[2] - 1, m[3], m[4], m[5], m[6]);
  }

  // An ECDSA signature as certificates carry it, two INTEGERs, to the 64 bytes WebCrypto takes.
  function rawSignature(bytes) {
    const [r, s] = inside(bytes, element(bytes, 0));
    const fixed = (e) => {
      let v = bytes.subarray(e.body, e.end);
      while (v.length > 32 && v[0] === 0) v = v.subarray(1);
      if (v.length > 32) throw new Error("signature too long");
      const out = new Uint8Array(32);
      out.set(v, 32 - v.length);
      return out;
    };
    return concat(fixed(r), fixed(s));
  }

  function commonName(bytes, name) {
    const oid = [0x06, 0x03, 0x55, 0x04, 0x03];
    for (let i = name.body; i + 7 < name.end; i++) {
      if (oid.every((b, k) => bytes[i + k] === b)) {
        const text = element(bytes, i + 5);
        return new TextDecoder().decode(bytes.subarray(text.body, text.end));
      }
    }
    return "(no name)";
  }

  function certificate(bytes) {
    const [tbs, , signature] = inside(bytes, element(bytes, 0));
    const fields = inside(bytes, tbs);
    if (fields[0].tag !== 0xa0) throw new Error("not a version 3 certificate");
    const [, , , issuer, validity, subject, key] = fields;
    const [notBefore, notAfter] = inside(bytes, validity);
    return {
      signed: slice(bytes, tbs),
      // A BIT STRING's first byte counts unused bits; it is zero here.
      signature: rawSignature(bytes.subarray(signature.body + 1, signature.end)),
      issuer: slice(bytes, issuer), subject: slice(bytes, subject), key: slice(bytes, key),
      name: commonName(bytes, subject),
      notBefore: time(bytes, notBefore), notAfter: time(bytes, notAfter),
    };
  }

  function certificates(pem) {
    const out = [];
    const block = /-----BEGIN CERTIFICATE-----([A-Za-z0-9+/=\s]+)-----END CERTIFICATE-----/g;
    for (let m; (m = block.exec(pem));) {
      out.push(certificate(Uint8Array.from(atob(m[1].replace(/\s+/g, "")), (c) => c.charCodeAt(0))));
    }
    return out;
  }

  async function signedBy(keyInfo, signature, message) {
    const key = await crypto.subtle.importKey("spki", keyInfo, { name: "ECDSA", namedCurve: "P-256" },
                                              false, ["verify"]);
    return crypto.subtle.verify({ name: "ECDSA", hash: "SHA-256" }, key, signature, message);
  }

  // A bare P-256 point (x then y) as SubjectPublicKeyInfo: the same prefix every P-256 key has.
  const pointKey = (xy) => concat(Uint8Array.from(INTEL_ROOT_KEY.slice(0, 54).match(/../g),
                                                  (h) => parseInt(h, 16)), xy);

  // ---- The quote.

  const u16 = (b, at) => b[at] | (b[at + 1] << 8);
  const u32 = (b, at) => (b[at] | (b[at + 1] << 8) | (b[at + 2] << 16) | (b[at + 3] << 24)) >>> 0;

  /** Returns { fields, steps }. Each step is { title, ok, detail }; the quote stands only if all are ok. */
  async function verifyQuote(quote, now) {
    const steps = [];
    const step = (title, ok, detail) => { steps.push({ title, ok: Boolean(ok), detail }); return ok; };
    const fields = {};
    try {
      if (quote.length < 636) throw new Error("too short to be a quote");
      const version = u16(quote, 0), keyType = u16(quote, 2), tee = u32(quote, 4);
      if (!step("It is an Intel TDX quote", version === 4 && keyType === 2 && tee === 0x81,
                `version ${version}, key type ${keyType}, TEE type 0x${tee.toString(16)}, ${quote.length} bytes`)) {
        return { fields, steps };
      }
      const body = quote.subarray(48, 632);
      const at = (from, size) => hex(body.subarray(from, from + size));
      Object.assign(fields, {
        teeTcbSvn: at(0, 16), mrSeam: at(16, 48), tdAttributes: at(120, 8), xfam: at(128, 8),
        MRTD: at(136, 48), mrConfigId: at(184, 48), mrOwner: at(232, 48), mrOwnerConfig: at(280, 48),
        RTMR0: at(328, 48), RTMR1: at(376, 48), RTMR2: at(424, 48), RTMR3: at(472, 48),
        reportData: at(520, 64),
      });

      const size = u32(quote, 632);
      if (636 + size > quote.length) throw new Error("signature data cut short");
      let p = 636;
      const signature = quote.subarray(p, p + 64), attestationKey = quote.subarray(p + 64, p + 128);
      p += 128;
      if (u16(quote, p) !== 6) throw new Error("unexpected certification data type " + u16(quote, p));
      p += 6;
      const qeReport = quote.subarray(p, p + 384), qeSignature = quote.subarray(p + 384, p + 448);
      p += 448;
      const authSize = u16(quote, p);
      const auth = quote.subarray(p + 2, p + 2 + authSize);
      p += 2 + authSize;
      if (u16(quote, p) !== 5) throw new Error("no PCK certificate chain in the quote");
      const chainSize = u32(quote, p + 2);
      if (p + 6 + chainSize > quote.length) throw new Error("certificate chain cut short");
      const chain = certificates(new TextDecoder().decode(quote.subarray(p + 6, p + 6 + chainSize)));
      if (chain.length !== 3) throw new Error(`expected three certificates, found ${chain.length}`);
      const [pck, intermediate, root] = chain;
      fields.certificates = chain.map((c) => c.name);

      step("The quote is signed by its attestation key",
           await signedBy(pointKey(attestationKey), signature, quote.subarray(0, 632)),
           "ECDSA P-256 over the quote's header and the trust domain's report, " +
           `key ${hex(attestationKey).slice(0, 24)}…`);

      const endorsed = await sha256(concat(attestationKey, auth));
      step("A quoting enclave vouches for that key",
           same(endorsed, qeReport.subarray(320, 352)) && qeReport.subarray(352, 384).every((b) => b === 0),
           "the enclave's own report carries SHA-256 of the attestation key: " + hex(endorsed).slice(0, 24) + "…");

      // Attribute flags: bit 1 is DEBUG. Intel's identity for the enclave wants flags 0x11 under its mask.
      const flags = qeReport.subarray(48, 56);
      const mask = [0xfb, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff, 0xff];
      const wanted = [0x11, 0, 0, 0, 0, 0, 0, 0];
      step("That enclave is Intel's TD quoting enclave, not in debug",
           hex(qeReport.subarray(128, 160)) === TD_QE_SIGNER && u16(qeReport, 256) === TD_QE_PRODUCT &&
           wanted.every((w, i) => (flags[i] & mask[i]) === w),
           `signer ${hex(qeReport.subarray(128, 160)).slice(0, 24)}…, product ${u16(qeReport, 256)}, ` +
           `version ${u16(qeReport, 258)}`);

      step("The enclave's report is signed by this processor's certified key",
           await signedBy(pck.key, qeSignature, qeReport), `certificate "${pck.name}"`);

      const links = [
        await signedBy(intermediate.key, pck.signature, pck.signed) && same(pck.issuer, intermediate.subject),
        await signedBy(root.key, intermediate.signature, intermediate.signed) && same(intermediate.issuer, root.subject),
        await signedBy(root.key, root.signature, root.signed) && same(root.issuer, root.subject),
      ];
      const current = chain.every((c) => c.notBefore <= now && now <= c.notAfter);
      const pinned = hex(root.key) === INTEL_ROOT_KEY;
      step("Its certificate chain ends at Intel's SGX root key",
           links.every(Boolean) && current && pinned,
           chain.map((c) => `"${c.name}"`).join(" ← ") +
           (current ? "" : "; a certificate is outside its dates") +
           (pinned ? "; root key as published by Intel" : "; ROOT KEY IS NOT INTEL'S"));

      step("The trust domain is not in debug mode", (body[120] & 1) === 0,
           "TD attributes " + fields.tdAttributes);
    } catch (error) {
      step("The quote could be read", false, String(error.message || error));
    }
    return { fields, steps };
  }

  scope.TdxQuote = { verifyQuote, sha256, hex, concat, same };
})(typeof window !== "undefined" ? window : globalThis);
