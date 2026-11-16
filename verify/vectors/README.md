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
