import Tls.Sha256

/-! HMAC and HKDF over SHA-256 (RFC 2104, RFC 5869), and the labelled expansion TLS 1.3 derives its keys
with (RFC 8446, 7.1). Keys pass through here; nothing is done with them but hashing. -/

namespace Tls

/-- HMAC-SHA-256 of `message` under `key`. -/
def hmac (key message : ByteArray) : ByteArray :=
  let key := if key.size > 64 then Sha256.hash key else key
  let block := key ++ ByteArray.mk (Array.replicate (64 - key.size) 0)
  let inner := ByteArray.mk (block.data.map (· ^^^ 0x36))
  let outer := ByteArray.mk (block.data.map (· ^^^ 0x5c))
  Sha256.hash (outer ++ Sha256.hash (inner ++ message))

namespace Hkdf

/-- A key of fixed length out of whatever there is to make one from. -/
def extract (salt material : ByteArray) : ByteArray := hmac salt material

/-- `length` bytes out of a key, for the purpose `info` names: at most 255 blocks of 32. -/
def expand (key info : ByteArray) (length : Nat) : ByteArray :=
  go key info length 1 ByteArray.empty ByteArray.empty (length / 32 + 1)
where
  go (key info : ByteArray) (length : Nat) (counter : UInt8) (last out : ByteArray) : Nat → ByteArray
    | 0 => out.extract 0 length
    | fuel + 1 =>
      if out.size ≥ length then out.extract 0 length
      else
        let next := hmac key ((last ++ info).push counter)
        go key info length (counter + 1) next (out ++ next) fuel

/-- TLS 1.3's HKDF-Expand-Label: `length` bytes from `secret` for `label` and `context`. -/
def expandLabel (secret : ByteArray) (label : String) (context : ByteArray) (length : Nat) : ByteArray :=
  let full := "tls13 ".toUTF8 ++ label.toUTF8
  let info := (ByteArray.mk #[(length / 256).toUInt8, length.toUInt8, full.size.toUInt8] ++ full).push context.size.toUInt8 ++ context
  expand secret info length

end Hkdf
end Tls
