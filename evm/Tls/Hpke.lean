import Tls.Aead
import Tls.Hkdf
import Tls.X25519
import Tls.Wire

/-! A message sealed to a public key, so that only the holder of the private key can open it: HPKE
(RFC 9180) in its base mode, with X25519, HKDF-SHA-256 and ChaCha20-Poly1305 (the suite 0x0020, 0x0001,
0x0003), one message to a sealing.

The standard is used as it stands so that anything that speaks it can seal to this: a library, a browser
with a few lines of script, OpenSSL. The sender makes a key pair for the one message, and from its
private half and the receiver's public key comes a secret that the receiver gets again from its own
private half and the sender's public half, which travels with the message. The key and nonce that seal
the message are drawn from that secret together with both public keys and with `info`, words both sides
must give the same, so a message sealed for one purpose does not open as another.

Opening is what the machine does with its private key; sealing is here for tests and takes the sender's
one-time key as given. The private key is bytes that go into `X25519` and nowhere else. -/

namespace Tls.Hpke

def kemSuite : ByteArray := "KEM".toUTF8 ++ u16 0x0020
def suite : ByteArray := "HPKE".toUTF8 ++ u16 0x0020 ++ u16 0x0001 ++ u16 0x0003

def labeledExtract (suite salt : ByteArray) (label : String) (material : ByteArray) : ByteArray :=
  Hkdf.extract salt ("HPKE-v1".toUTF8 ++ suite ++ label.toUTF8 ++ material)

def labeledExpand (suite key : ByteArray) (label : String) (info : ByteArray) (length : Nat) : ByteArray :=
  Hkdf.expand key (u16 length ++ "HPKE-v1".toUTF8 ++ suite ++ label.toUTF8 ++ info) length

/-- The secret two sides share, from what X25519 gave and both public halves. Nothing when the exchange
came to nothing, which only a public half made to do that causes. -/
def shared? (dh enc recipient : ByteArray) : Option ByteArray :=
  if Secret.equal dh (ByteArray.mk (Array.replicate 32 0)) then none
  else some (labeledExpand kemSuite (labeledExtract kemSuite .empty "eae_prk" dh) "shared_secret" (enc ++ recipient) 32)

/-- The key and the nonce for the one message. -/
def keys (shared info : ByteArray) : ByteArray × ByteArray :=
  let context := ByteArray.mk #[0] ++ labeledExtract suite .empty "psk_id_hash" .empty ++ labeledExtract suite .empty "info_hash" info
  let secret := labeledExtract suite shared "secret" .empty
  (labeledExpand suite secret "key" context 32, labeledExpand suite secret "base_nonce" context 12)

/-- What was sealed, for the holder of `secretKey`, whose public half is `publicKey`: `enc` is the sender's
public half, `sealed` the message with its tag. Nothing unless every byte is as it was sealed. -/
def open? (secretKey publicKey enc info aad sealed : ByteArray) : Option ByteArray :=
  if enc.size != 32 || secretKey.size != 32 then none else
  match shared? (X25519.x25519 secretKey enc) enc publicKey with
  | none => none
  | some shared =>
    let (key, nonce) := keys shared info
    Aead.decrypt? key nonce aad sealed

/-- A message sealed to `recipient` with the one-time key `ephemeral`: the public half to send, and the
sealed message. For tests: a sender in earnest draws `ephemeral` fresh and never uses it twice. -/
def seal? (ephemeral recipient info aad plain : ByteArray) : Option (ByteArray × ByteArray) :=
  let enc := X25519.publicKey ephemeral
  match shared? (X25519.x25519 ephemeral recipient) enc recipient with
  | none => none
  | some shared =>
    let (key, nonce) := keys shared info
    some (enc, Aead.encrypt key nonce aad plain)

end Tls.Hpke
