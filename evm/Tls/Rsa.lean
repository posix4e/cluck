import Tls.Sha256

/-! RSA signatures checked, in the two shapes TLS meets them: PKCS #1 v1.5 on certificates, and PSS with
SHA-256 on a server's proof that it holds its key (RFC 8017). Everything here is public (a signature, a
public key, a hash of public bytes), so the numbers are `Nat`s and nothing is done about time. No signature
is ever made here: the guest holds no RSA key. -/

namespace Tls

/-- A number from bytes, most significant first, and back to exactly `size` bytes. -/
def natOf (b : @& ByteArray) : Nat := b.foldl (fun n x => n * 256 + x.toNat) 0

def bytesOf (n size : Nat) : ByteArray :=
  ByteArray.mk ((List.range size).map fun i => (n >>> (8 * (size - 1 - i))).toUInt8).toArray

/-- `base` to the power `exponent` modulo `modulus`, by squaring, a bit of the exponent at a time. -/
def powerMod (base exponent modulus : Nat) : Nat :=
  go (base % modulus) exponent 1 (exponent.log2 + 1)
where
  go (base exponent acc : Nat) : Nat → Nat
    | 0 => acc
    | fuel + 1 =>
      if exponent == 0 then acc
      else go (base * base % modulus) (exponent / 2) (if exponent % 2 == 1 then acc * base % modulus else acc) fuel

namespace Rsa

/-- A public key: the modulus, the exponent, and the modulus's length in bytes. -/
structure Key where
  modulus : Nat
  exponent : Nat
  size : Nat

/-- What a signature opens to under the key: as many bytes as the modulus has. None for a signature of the
wrong length or not under the modulus, or a key too small or odd to be one. -/
def opened (key : Key) (signature : @& ByteArray) : Option ByteArray :=
  if signature.size != key.size || key.size < 256 || key.exponent < 3 || key.exponent % 2 == 0 then none else
  let s := natOf signature
  if s ≥ key.modulus then none else some (bytesOf (powerMod s key.exponent key.modulus) key.size)

/-- What goes before a digest in a PKCS #1 v1.5 signature: the name of the hash, as DER. -/
def digestInfo (digestSize : Nat) : Option ByteArray :=
  if digestSize == 32 then some ⟨#[0x30, 0x31, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x01, 0x05, 0x00, 0x04, 0x20]⟩
  else if digestSize == 48 then some ⟨#[0x30, 0x41, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x02, 0x05, 0x00, 0x04, 0x30]⟩
  else if digestSize == 64 then some ⟨#[0x30, 0x51, 0x30, 0x0d, 0x06, 0x09, 0x60, 0x86, 0x48, 0x01, 0x65, 0x03, 0x04, 0x02, 0x03, 0x05, 0x00, 0x04, 0x40]⟩
  else none

/-- A PKCS #1 v1.5 signature over a SHA-256, SHA-384 or SHA-512 `digest`: the signature must open to
exactly 00 01, ones, 00, the hash's name and the digest, with nothing else allowed anywhere. -/
def verifyPkcs1 (key : Key) (digest signature : @& ByteArray) : Bool :=
  match opened key signature, digestInfo digest.size with
  | some em, some info =>
    let tail := info ++ digest
    if tail.size + 11 > em.size then false
    else
      let ones := em.size - tail.size - 3
      em == (ByteArray.mk #[0x00, 0x01] ++ ByteArray.mk (Array.replicate ones 0xff)).push 0x00 ++ tail
  | _, _ => false

/-- MGF1 with SHA-256: `length` bytes spun out of `seed`. -/
def mgf1 (seed : ByteArray) (length : Nat) : ByteArray :=
  ((List.range (length / 32 + 1)).foldl (fun out i =>
    out ++ Sha256.hash (seed ++ bytesOf i 4)) ByteArray.empty).extract 0 length

/-- An RSASSA-PSS signature over a SHA-256 `digest`, with MGF1 on SHA-256 and a salt as long as the digest,
which is what TLS 1.3 fixes (RFC 8017, 9.1.2). -/
def verifyPss (key : Key) (digest signature : @& ByteArray) : Bool :=
  match opened key signature with
  | none => false
  | some full =>
    -- The message is one bit shorter than the modulus; with a modulus of whole bytes that is all its
    -- bytes with the top bit clear.
    let bits := key.modulus.log2          -- modulus bits less one
    let size := (bits + 7) / 8
    let em := full.extract (full.size - size) full.size
    if digest.size != 32 || size < 66 || (full.extract 0 (full.size - size)).data.any (· != 0) then false
    else if Fast.byte em (size - 1) != 0xbc then false
    else
      let masked := em.extract 0 (size - 33)
      let h := em.extract (size - 33) (size - 1)
      let clear := 8 * size - bits
      if Fast.byte masked 0 >>> (8 - clear).toUInt8 != 0 then false
      else
        let mask := mgf1 h masked.size
        let db := ByteArray.mk ((List.range masked.size).map fun i => Fast.byte masked i ^^^ Fast.byte mask i).toArray
        let db := db.set! 0 (Fast.byte db 0 &&& (0xff >>> clear.toUInt8))
        let pad := db.size - 33
        if (db.extract 0 pad).data.any (· != 0) || Fast.byte db pad != 0x01 then false
        else h == Sha256.hash (ByteArray.mk (Array.replicate 8 0) ++ digest ++ db.extract (pad + 1) db.size)

end Rsa
end Tls
