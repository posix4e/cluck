import Tls.Ecdsa
import Tls.Sha512

/-! Certificates read and checked (RFC 5280), as far as a TLS client that trusts a few named roots needs.

A certificate is read out of its DER bytes: what was signed, by which algorithm, the signature, who issued
it and to whom, when it is good, the key in it, the names it is for, and whether it may sign others. A
chain as a server sends it is then walked from the server's own certificate up: each must be signed by the
next, the next must be allowed to sign, all must be in date, the first must be for the name asked, and the
walk must reach a root this client was built with. Anything not understood is a refusal, never a pass.

It is deliberately small. No revocation is checked. Of the limits a certificate can put on what it is good
for, only whether it may sign others is read. The time is handed in by the caller, and the caller here has
no clock of its own (see THREAT_MODEL.md). Everything in a certificate is public. -/

namespace Tls.X509

/-- One element of DER: its tag, where its contents lie, and where the next element begins. -/
structure Element where
  tag : UInt8
  start : Nat
  stop : Nat
  deriving Inhabited

/-- The element at `at_` of `b`, which must lie wholly before `limit`. Lengths of up to four bytes. -/
def element? (b : @& ByteArray) (at_ limit : Nat) : Option Element :=
  if at_ + 2 > limit || limit > b.size then none else
  let tag := Fast.byte b at_
  let first := (Fast.byte b (at_ + 1)).toNat
  if first < 0x80 then
    if at_ + 2 + first > limit then none else some ⟨tag, at_ + 2, at_ + 2 + first⟩
  else
    let count := first - 0x80
    if count == 0 || count > 4 || at_ + 2 + count > limit then none else
    let length := (List.range count).foldl (fun n i => n * 256 + (Fast.byte b (at_ + 2 + i)).toNat) 0
    -- A length must be written the shortest way.
    if length < 0x80 || (count > 1 && Fast.byte b (at_ + 2) == 0) then none
    else if at_ + 2 + count + length > limit then none
    else some ⟨tag, at_ + 2 + count, at_ + 2 + count + length⟩

/-- The elements that fill `start` to `stop`, end to end; none if they do not fit exactly. -/
def elements? (b : @& ByteArray) (start stop : Nat) : Option (Array Element) :=
  go b stop (stop - start + 1) start #[]
where
  go (b : @& ByteArray) (stop : Nat) : Nat → Nat → Array Element → Option (Array Element)
    | 0, _, _ => none
    | fuel + 1, at_, found =>
      if at_ == stop then some found
      else match element? b at_ stop with
        | none => none
        | some e => go b stop fuel e.stop (found.push e)

/-- The elements inside `e`. -/
def inside? (b : @& ByteArray) (e : Element) : Option (Array Element) := elements? b e.start e.stop

/-- The contents of an element, and the whole of it with its tag and length. -/
def contents (b : @& ByteArray) (e : Element) : ByteArray := b.extract e.start e.stop

/-- A non-negative INTEGER as a number and its length in bytes without a leading zero. -/
def integer? (b : @& ByteArray) (e : Element) : Option (Nat × Nat) :=
  if e.tag != 0x02 || e.stop == e.start || Fast.byte b e.start ≥ 0x80 then none else
  let bytes := contents b e
  let skip := if bytes.size > 1 && Fast.byte bytes 0 == 0 then 1 else 0
  some (natOf (bytes.extract skip bytes.size), bytes.size - skip)

/-- The key in a certificate. -/
inductive Key where
  | rsa (key : Rsa.Key)
  | p256 (x y : Nat)
  | p384 (x y : Nat)

/-- How a certificate was signed. -/
inductive Signed where
  | rsaSha256 | rsaSha384 | ecdsaSha256 | ecdsaSha384
  deriving BEq

structure Certificate where
  /-- The bytes that were signed. -/
  signed : ByteArray
  how : Signed
  signature : ByteArray
  /-- The issuer's and the subject's names, as their DER bytes, which is how they are compared. -/
  issuer : ByteArray
  subject : ByteArray
  /-- Good from and until, in seconds since 1970. -/
  notBefore : Nat
  notAfter : Nat
  key : Key
  /-- The DNS names it is for. -/
  names : Array ByteArray
  /-- Whether it may sign other certificates. -/
  authority : Bool

def oid (bytes : List UInt8) : ByteArray := ByteArray.mk bytes.toArray
def oidRsaEncryption := oid [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x01]
def oidRsaSha256 := oid [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0b]
def oidRsaSha384 := oid [0x2a, 0x86, 0x48, 0x86, 0xf7, 0x0d, 0x01, 0x01, 0x0c]
def oidEcdsaSha256 := oid [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x02]
def oidEcdsaSha384 := oid [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x04, 0x03, 0x03]
def oidEcPublicKey := oid [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x02, 0x01]
def oidP256 := oid [0x2a, 0x86, 0x48, 0xce, 0x3d, 0x03, 0x01, 0x07]
def oidP384 := oid [0x2b, 0x81, 0x04, 0x00, 0x22]
def oidNames := oid [0x55, 0x1d, 0x11]
def oidBasicConstraints := oid [0x55, 0x1d, 0x13]

/-- Seconds since 1970 for a date and time of day, by the usual count of days. -/
def seconds (year month day hour minute second : Nat) : Nat :=
  let y := if month ≤ 2 then year - 1 else year
  let era := y / 400
  let yoe := y - era * 400
  let m := if month > 2 then month - 3 else month + 9
  let doy := (153 * m + 2) / 5 + day - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  (era * 146097 + doe - 719468) * 86400 + hour * 3600 + minute * 60 + second

/-- A time as certificates write it: thirteen characters with a two-digit year, or fifteen with four. -/
def time? (b : @& ByteArray) (e : Element) : Option Nat :=
  let text := contents b e
  let digits (at_ count : Nat) : Option Nat :=
    (List.range count).foldlM (fun n i =>
      let c := Fast.byte text (at_ + i)
      if c ≥ 0x30 && c ≤ 0x39 then some (n * 10 + (c.toNat - 0x30)) else none) 0
  let rest (year at_ : Nat) : Option Nat := do
    if Fast.byte text (at_ + 10) != 0x5a then none
    let month ← digits at_ 2
    let day ← digits (at_ + 2) 2
    if month == 0 || month > 12 || day == 0 || day > 31 then none
    pure (seconds year month day (← digits (at_ + 4) 2) (← digits (at_ + 6) 2) (← digits (at_ + 8) 2))
  if e.tag == 0x17 && text.size == 13 then do
    let yy ← digits 0 2
    rest (if yy < 50 then 2000 + yy else 1900 + yy) 2
  else if e.tag == 0x18 && text.size == 15 then do
    rest (← digits 0 4) 4
  else none

/-- The key in a SubjectPublicKeyInfo. -/
def key? (b : @& ByteArray) (info : Element) : Option Key := do
  let parts ← inside? b info
  if parts.size != 2 || info.tag != 0x30 then none
  let algorithm ← inside? b parts[0]!
  let bits := parts[1]!
  -- A BIT STRING with no unused bits.
  if bits.tag != 0x03 || bits.stop ≤ bits.start || Fast.byte b bits.start != 0 then none
  let name := contents b (← algorithm[0]?)
  if name == oidRsaEncryption then
    let whole ← element? b (bits.start + 1) bits.stop
    let numbers ← inside? b whole
    if whole.tag != 0x30 || whole.stop != bits.stop || numbers.size != 2 then none
    let (modulus, size) ← integer? b numbers[0]!
    let (exponent, _) ← integer? b numbers[1]!
    pure (.rsa ⟨modulus, exponent, size⟩)
  else if name == oidEcPublicKey then
    let curve := contents b (← algorithm[1]?)
    let point := b.extract (bits.start + 1) bits.stop
    -- An uncompressed point: 04, then the two coordinates.
    let size := if curve == oidP256 then 32 else if curve == oidP384 then 48 else 0
    if size == 0 || point.size != 1 + 2 * size || Fast.byte point 0 != 0x04 then none
    let x := natOf (point.extract 1 (1 + size))
    let y := natOf (point.extract (1 + size) point.size)
    pure (if size == 32 then .p256 x y else .p384 x y)
  else none

/-- A certificate from its DER bytes. -/
def read? (der : @& ByteArray) : Option Certificate := do
  let whole ← element? der 0 der.size
  if whole.tag != 0x30 || whole.stop != der.size then none
  let top ← inside? der whole
  if top.size != 3 then none
  let tbs := top[0]!
  let fields ← inside? der tbs
  -- Version 3, then: serial, algorithm, issuer, validity, subject, key, and extensions.
  if tbs.tag != 0x30 || fields.size < 8 || fields[0]!.tag != 0xa0 then none
  let how ← do
    let outer ← inside? der top[1]!
    let inner ← inside? der fields[2]!
    let name := contents der (← outer[0]?)
    -- The algorithm is named twice, inside what was signed and outside, and the two must agree.
    if contents der top[1]! != contents der fields[2]! || inner.size == 0 then none
    if name == oidRsaSha256 then pure Signed.rsaSha256
    else if name == oidRsaSha384 then pure Signed.rsaSha384
    else if name == oidEcdsaSha256 then pure Signed.ecdsaSha256
    else if name == oidEcdsaSha384 then pure Signed.ecdsaSha384
    else none
  let signature := top[2]!
  if signature.tag != 0x03 || signature.stop ≤ signature.start || Fast.byte der signature.start != 0 then none
  let validity ← inside? der fields[4]!
  if validity.size != 2 then none
  let key ← key? der fields[6]!
  -- Extensions: the last field, tagged [3], holding a sequence of them.
  let last := fields[fields.size - 1]!
  if last.tag != 0xa3 then none
  let listed ← inside? der (← element? der last.start last.stop)
  let mut names : Array ByteArray := #[]
  let mut authority := false
  for extension in listed do
    let parts ← inside? der extension
    let value ← parts.back?
    let name := contents der (← parts[0]?)
    if value.tag != 0x04 then none
    if name == oidNames then
      let general ← inside? der (← element? der value.start value.stop)
      for entry in general do
        -- [2] is a DNS name.
        if entry.tag == 0x82 then
          let text := contents der entry
          -- A DNS name is plain letters; one with any other byte in it is left out, not guessed at.
          if text.data.all (fun c => c > 0x20 && c < 0x7f) then
            names := names.push text
    else if name == oidBasicConstraints then
      let inner ← inside? der (← element? der value.start value.stop)
      authority := match inner[0]? with
        | some first => first.tag == 0x01 && first.stop == first.start + 1 && Fast.byte der first.start != 0
        | none => false
  -- What was signed is the first element of the certificate, tag and length and all: it begins where the
  -- certificate's own contents begin.
  pure { signed := der.extract whole.start tbs.stop,
         how, signature := der.extract (signature.start + 1) signature.stop,
         issuer := contents der fields[3]!, subject := contents der fields[5]!,
         notBefore := ← time? der validity[0]!, notAfter := ← time? der validity[1]!,
         key, names, authority }

/-- Whether `cert` carries a good signature by the holder of `key`. -/
def signedBy (cert : Certificate) (key : Key) : Bool :=
  let digest := match cert.how with
    | .rsaSha256 | .ecdsaSha256 => Sha256.hash cert.signed
    | .rsaSha384 | .ecdsaSha384 => Sha512.hash384 cert.signed
  let ecdsa (curve : Ecdsa.Curve) (x y : Nat) : Bool :=
    -- An ECDSA signature is a sequence of two numbers.
    (do
      let whole ← element? cert.signature 0 cert.signature.size
      let parts ← inside? cert.signature whole
      if whole.tag != 0x30 || whole.stop != cert.signature.size || parts.size != 2 then none
      let (r, _) ← integer? cert.signature parts[0]!
      let (s, _) ← integer? cert.signature parts[1]!
      pure (Ecdsa.verify curve x y digest r s)).getD false
  match cert.how, key with
  | .rsaSha256, .rsa k | .rsaSha384, .rsa k => Rsa.verifyPkcs1 k digest cert.signature
  | .ecdsaSha256, .p256 x y | .ecdsaSha384, .p256 x y => ecdsa Ecdsa.p256 x y
  | .ecdsaSha256, .p384 x y | .ecdsaSha384, .p384 x y => ecdsa Ecdsa.p384 x y
  | _, _ => false

/-- A name with its capital letters made small. -/
def lower (name : @& ByteArray) : ByteArray :=
  ByteArray.mk (name.data.map fun c => if c ≥ 0x41 && c ≤ 0x5a then c + 0x20 else c)

/-- Whether a certificate's name covers `host`: the same name, letter case aside, or a name whose first
label is `*` and whose rest, with its dot, is `host` after a first label that is not empty and holds no
dot, so that a star stands for one label and never for none or for two. -/
def covers (name host : @& ByteArray) : Bool :=
  let name := lower name
  let host := lower host
  if name == host then true
  else if name.size > 2 && Fast.byte name 0 == 0x2a && Fast.byte name 1 == 0x2e then
    let rest := name.extract 1 name.size            -- from the dot
    if host.size ≤ rest.size then false
    else
      let first := host.extract 0 (host.size - rest.size)
      host.extract (host.size - rest.size) host.size == rest && !first.data.any (· == 0x2e)
        -- What follows the star is itself a name of two labels at the least.
        && (rest.extract 1 rest.size).data.any (· == 0x2e)
  else false

/-- A root this client trusts: its name, as DER, and its key. -/
structure Anchor where
  subject : ByteArray
  key : Key

/-- A root, from its own certificate. Its signature on itself and its dates are not looked at: it is
trusted because it was put here, and for as long as it is here. -/
def Anchor.of (der : @& ByteArray) : Option Anchor := (read? der).map fun c => ⟨c.subject, c.key⟩

/-- A chain as a server sends it, its own certificate first, checked for `host` at the time `now`: the key
in the server's certificate if every link holds, and otherwise the reason it does not. -/
def validate (anchors : @& Array Anchor) (chain : @& Array ByteArray) (host : @& ByteArray) (now : Nat) : Except String Key := do
  let certs ← chain.mapM fun der => match read? der with
    | some c => pure c
    | none => .error "a certificate that cannot be read"
  let some leaf := certs[0]? | .error "no certificate"
  if !leaf.names.any (covers · host) then .error "a certificate for another name"
  walk anchors certs now leaf.key 0 certs.size
where
  walk (anchors : @& Array Anchor) (certs : @& Array Certificate) (now : Nat) (found : Key) : Nat → Nat → Except String Key
    | _, 0 => .error "a chain that does not reach a root this client trusts"
    | i, fuel + 1 =>
      match certs[i]? with
      | none => .error "a chain that does not reach a root this client trusts"
      | some cert =>
        if now < cert.notBefore || now > cert.notAfter then .error "a certificate out of date"
        else if anchors.any (fun a => a.subject == cert.issuer && signedBy cert a.key) then .ok found
        else match certs[i + 1]? with
          | some next =>
            if next.subject != cert.issuer then .error "a chain out of order"
            else if !next.authority then .error "a certificate signed by one that may not sign"
            else if !signedBy cert next.key then .error "a certificate with a bad signature"
            else walk anchors certs now found (i + 1) fuel
          | none => .error "a chain that does not reach a root this client trusts"

end Tls.X509
