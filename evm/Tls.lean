import Tls.Sha256
import Tls.Sha512
import Tls.Hkdf
import Tls.ChaCha20
import Tls.Poly1305
import Tls.Aead
import Tls.X25519

/-! What the guest needs to keep a secret on a wire. So far the pieces: SHA-256, SHA-384 and SHA-512, HMAC
and HKDF, ChaCha20-Poly1305, X25519. `TODO.md` says where it stands. -/
