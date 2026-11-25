# Real attestation documents

Two documents a real Nitro Enclave returned, kept so that the verifier is tested against the real thing and
not only against documents forged for the purpose (`verify/test-verify-attestation` uses both).

They came from `silo-os.eif` as CI built it, started on an m5.xlarge in us-east-2 on 2026-11-15 and asked
with `ask attest`. The instance is long gone; its identifier is in the documents.

| File | What it is | Nonce sent |
|---|---|---|
| `enclave.bin` | From the enclave started normally. | `4fae66f91d89c3177d2af9ce33bce1ebb91783f42805b40c2859dd90184248b2` |
| `enclave-debug.bin` | From the same image started in debug mode: every measurement is zero. | `2cf96176623863ca589de4e3cea906dfaa8fc1368ed0cfd85dc8be554985dc72` |
| `enclave.pcrs.json` | The image's measurements, as `scripts/build-eif` wrote them in CI. | |

The certificate that signs a document is good for about three hours, so the test checks both as of
1794770000 (seconds since 1970), a moment inside that time for each. Checked as of today they are refused,
as they should be.

## What Intel answered about a TDX platform (`intel/`)

For `verify/test-tdx-standing`, which tests `scripts/tdx-standing`. Fetched on 2026-11-24 at about 23:25 UTC
with `scripts/tdx-standing QUOTE --keep`, and checked in the test as of 1795564800 (the midnight after).

| File | What it is |
|---|---|
| `quote` | The quote of the builder's guest on Google Cloud (`docs/live/builder.quote` as it was that day). |
| `levels`, `levels.chain` | Intel's TDX levels for processor family 00806f050000, and the certificates of who signed them (from the answer's `TCB-Info-Issuer-Chain` heading). |
| `enclave`, `enclave.chain` | Intel's identity for the TD quoting enclave, and the same for it. |
| `withdrawn` | The list of platform certificates Intel's "SGX PCK Platform CA" has revoked. |
| `withdrawn-root` | The list of what Intel's SGX root has revoked. |

The levels, the identity and the first list say they are good until 2026-12-24. Checked as of a later day
they are refused, as they should be, which is one of the test's cases.

## `door/`: what the builder's door served for one guest

The answers of `evm/builder/door`, run here on 2026-11-25 in front of a guest in a trust domain on
Compute Engine that ran the builder's image `e2010f12…e0e3b4`: for `evm/demo/test-send.mjs`, which
checks them as the page for sealed transactions would, as of 04:00 UTC that day.

| File | What it is |
|---|---|
| `sealing.json` | The door's answer to `GET /key`: the guest's sealing key, the challenge the door asked with, and the quote. |
| `builder.json` | The same for `GET /builder`, the guest's key for bids. |
| `builder.quote` | The quote out of `builder.json`, as `docs/live/` keeps one. |
| `record.json` | What `docs/live/builder.json` would say of that guest: RTMR1 as `scripts/gce-measure` works it out for the image, the key for bids, the challenge. |
