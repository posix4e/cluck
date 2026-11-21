import Tls.ChaCha20
import Tls.Poly1305
import Secret

/-! ChaCha20-Poly1305 (RFC 8439): a message sealed under a key and a nonce, with data beside it that is
authenticated and not hidden. Opening compares the tag in time that does not depend on where it differs,
and gives nothing back unless it is right. -/

namespace Tls.Aead

/-- What the tag is taken over: the data beside, the sealed message, each padded to sixteen bytes, and the
two lengths. -/
def authenticated (aad sealed : ByteArray) : ByteArray :=
  let pad (b : ByteArray) : ByteArray := ByteArray.mk (Array.replicate ((16 - b.size % 16) % 16) 0)
  let length (b : ByteArray) : ByteArray := Fast.store (ByteArray.mk (Array.replicate 8 0)) 0 b.size.toUInt64
  aad ++ pad aad ++ sealed ++ pad sealed ++ length aad ++ length sealed

/-- `plain` sealed under a 32-byte `key` and a 12-byte `nonce`: the hidden bytes, then 16 bytes of tag. -/
def encrypt (key nonce aad plain : ByteArray) : ByteArray :=
  let oneTime := ChaCha20.stream key nonce 0 32
  let hidden := ChaCha20.apply key nonce 1 plain
  hidden ++ Poly1305.tag oneTime (authenticated aad hidden)

/-- What was sealed, if the tag is right; nothing if it is not, or there is no room for one. -/
def decrypt? (key nonce aad sealed : ByteArray) : Option ByteArray :=
  if sealed.size < 16 then none else
  let hidden := sealed.extract 0 (sealed.size - 16)
  let oneTime := ChaCha20.stream key nonce 0 32
  if Secret.equal (Poly1305.tag oneTime (authenticated aad hidden)) (sealed.extract (sealed.size - 16) sealed.size) then
    some (ChaCha20.apply key nonce 1 hidden)
  else none

end Tls.Aead
