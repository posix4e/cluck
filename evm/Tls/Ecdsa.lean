import Tls.Rsa

/-! ECDSA signatures checked on the two curves certificates use, P-256 and P-384 (FIPS 186-4, SEC 1). All
of it is public: a signature, a public key, a hash. The numbers are `Nat`s, the points are in Jacobian
coordinates, and nothing is done about time. No signature is made here. -/

namespace Tls.Ecdsa

/-- A curve `y² = x³ - 3x + b` over the numbers modulo `p`, with a point of order `n`. -/
structure Curve where
  p : Nat
  b : Nat
  n : Nat
  gx : Nat
  gy : Nat
  /-- The length of a coordinate in bytes. -/
  size : Nat

def p256 : Curve :=
  { p := 0xffffffff00000001000000000000000000000000ffffffffffffffffffffffff
    b := 0x5ac635d8aa3a93e7b3ebbd55769886bc651d06b0cc53b0f63bce3c3e27d2604b
    n := 0xffffffff00000000ffffffffffffffffbce6faada7179e84f3b9cac2fc632551
    gx := 0x6b17d1f2e12c4247f8bce6e563a440f277037d812deb33a0f4a13945d898c296
    gy := 0x4fe342e2fe1a7f9b8ee7eb4a7c0f9e162bce33576b315ececbb6406837bf51f5
    size := 32 }

def p384 : Curve :=
  { p := 0xfffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffeffffffff0000000000000000ffffffff
    b := 0xb3312fa7e23ee7e4988e056be3f82d19181d9c6efe8141120314088f5013875ac656398d8a2ed19d2a85c8edd3ec2aef
    n := 0xffffffffffffffffffffffffffffffffffffffffffffffffc7634d81f4372ddf581a0db248b0a77aecec196accc52973
    gx := 0xaa87ca22be8b05378eb1c71ef320ad746e1d3b628ba79b9859f741e082542a385502f25dbf55296c3a545e3872760ab7
    gy := 0x3617de4a96262c6f5d9e98bf9292dc29f8f41dbd289a147ce9da3113b5f0b8c00a60b1ce1d7e819d7a431d7c90ea0e5f
    size := 48 }

/-- A point in Jacobian coordinates, `(x / z², y / z³)`; `z = 0` is the point at infinity. -/
structure Point where
  x : Nat
  y : Nat
  z : Nat

def infinity : Point := ⟨1, 1, 0⟩

def double (c : Curve) (q : Point) : Point :=
  if q.z == 0 || q.y == 0 then infinity else
  let p := c.p
  let zz := q.z * q.z % p
  let yy := q.y * q.y % p
  -- 3 (x - z²)(x + z²), the slope's numerator for a curve with a = -3
  let m := 3 * ((q.x + p - zz) % p) % p * ((q.x + zz) % p) % p
  let s := 4 * q.x % p * yy % p
  let x := (m * m + 2 * (p - s)) % p
  let y := (m * ((s + p - x) % p) + (p - 8 * (yy * yy % p) % p)) % p
  ⟨x, y, 2 * q.y % p * q.z % p⟩

def add (c : Curve) (q r : Point) : Point :=
  if q.z == 0 then r else if r.z == 0 then q else
  let p := c.p
  let z1z1 := q.z * q.z % p
  let z2z2 := r.z * r.z % p
  let u1 := q.x * z2z2 % p
  let u2 := r.x * z1z1 % p
  let s1 := q.y * r.z % p * z2z2 % p
  let s2 := r.y * q.z % p * z1z1 % p
  if u1 == u2 then (if s1 == s2 then double c q else infinity) else
  let h := (u2 + p - u1) % p
  let rr := (s2 + p - s1) % p
  let hh := h * h % p
  let hhh := hh * h % p
  let v := u1 * hh % p
  let x := (rr * rr + (p - hhh) + 2 * (p - v)) % p
  let y := (rr * ((v + p - x) % p) + (p - s1 * hhh % p)) % p
  ⟨x, y, q.z * r.z % p * h % p⟩

/-- `k` times `q`, by doubling, a bit of `k` at a time from the top. -/
def mul (c : Curve) (k : Nat) (q : Point) : Point :=
  go k (k.log2 + 1) infinity
where
  go (k : Nat) : Nat → Point → Point
    | 0, acc => acc
    | left + 1, acc =>
      let acc := double c acc
      go k left (if (k >>> left) % 2 == 1 then add c acc q else acc)

/-- Whether `(x, y)` is a point of the curve, with both numbers under the modulus. -/
def onCurve (c : Curve) (x y : Nat) : Bool :=
  x < c.p && y < c.p && y * y % c.p == (x * x % c.p * x + (c.p - 3 * x % c.p) + c.b) % c.p

/-- Whether `(r, s)` is a signature of `digest` under the public key `(qx, qy)`. A digest longer than the
curve's order is cut to its leftmost bytes. -/
def verify (c : Curve) (qx qy : Nat) (digest : @& ByteArray) (r s : Nat) : Bool :=
  if r == 0 || r ≥ c.n || s == 0 || s ≥ c.n || !onCurve c qx qy then false else
  let z := natOf (digest.extract 0 (min digest.size c.size))
  let w := powerMod s (c.n - 2) c.n
  let u1 := z * w % c.n
  let u2 := r * w % c.n
  let sum := add c (mul c u1 ⟨c.gx, c.gy, 1⟩) (mul c u2 ⟨qx, qy, 1⟩)
  if sum.z == 0 then false
  else
    let zInverse := powerMod sum.z (c.p - 2) c.p
    sum.x * (zInverse * zInverse % c.p) % c.p % c.n == r

end Tls.Ecdsa
