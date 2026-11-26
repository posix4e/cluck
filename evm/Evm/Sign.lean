import Evm.Sign.Hash
import JauneConsensus.Crypto.Codec

/-! A BLS key that is used without ever being a `Nat`: its public key, and signatures with it.

The curve arithmetic on the key is `Evm/Sign/Curve.lean`. Everything else a signature needs is public:
hashing a message to a point, which is `Evm/Sign/Hash.lean` on the same arithmetic (and
`JauneConsensus`'s for the first step, SHA-256), and writing a point as bytes, which is
`JauneConsensus`'s. So this file is the crossings: a public point in, the key applied, a public point
out.

The scheme is the one Ethereum's consensus layer and its builders use, BLS signatures with public keys in
G1 and signatures in G2, and a signature made here is byte for byte the one `JauneConsensus.sign` makes
with the same key and message; `bls-test` checks that. -/

namespace Evm.Sign

open Jaune JauneConsensus

/-- Three times the `4` of `y^2 = x^3 + 4`. -/
def b3G1 : Fp := Fp.ofPublic 12

def generatorG1 : Point Fp :=
  Point.ofAffine (Fp.ofPublic blsG1Generator.x.val) (Fp.ofPublic blsG1Generator.y.val)

/-- A point of G2 that is not a secret, such as the hash of a message. -/
def ofPublicG2 (q : Bls12G2) : Point Fp2 :=
  if q = g2Identity then Point.infinity else
  let (x0, x1) := blsF2Coeffs q.x
  let (y0, y1) := blsF2Coeffs q.y
  Point.ofAffine ⟨Fp.ofPublic x0.val, Fp.ofPublic x1.val⟩ ⟨Fp.ofPublic y0.val, Fp.ofPublic y1.val⟩

/-- The affine point a multiplication ended at, made public. The division is by a fixed sequence of
products; only what comes out of it is turned into numbers. -/
def toPublicG1 (p : Point Fp) : Bls12G1 :=
  let z := p.z.inv
  let x := (p.x * z).toPublic
  let y := (p.y * z).toPublic
  -- The point at infinity has `z` zero, and so `x` and `y` zero, which is how `Jaune` writes it.
  ⟨FinField.ofNat x, FinField.ofNat y⟩

def toPublicG2 (p : Point Fp2) : Bls12G2 :=
  let z := p.z.inv
  let x := Fp2.mul p.x z
  let y := Fp2.mul p.y z
  ⟨Bls12Fp2.mk x.c0.toPublic x.c1.toPublic, Bls12Fp2.mk y.c0.toPublic y.c1.toPublic⟩

/-- The public key of a key: the key times the generator of G1, as its 48 bytes. -/
def publicKey (k : Scalar) : Bytes :=
  g1Compress (toPublicG1 (Point.mul b3G1 k generatorG1))

/-- The key times a public point of G2. -/
def applyG2 (k : Scalar) (q : Bls12G2) : Bls12G2 :=
  toPublicG2 (Point.mul b3G2 k (ofPublicG2 q))

/-- The tag under which a message is hashed to a point, for signatures in G2 with proof of possession:
the one Ethereum's consensus layer uses. -/
def messageTag : Bytes := "BLS_SIG_BLS12381G2_XMD:SHA-256_SSWU_RO_POP_".toUTF8.toList

/-- The signature of a message: the key times the message's point, as its 96 bytes. -/
def sign (k : Scalar) (message : Bytes) : Except String Bytes := do
  let q ← Hash.toPoint message messageTag
  pure (g2Compress (toPublicG2 (Point.mul b3G2 k q)))

end Evm.Sign
