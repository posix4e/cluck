import Fast.Bytes

/-! SHA-256 (FIPS 180-4) on machine words: a block's 64 rounds written out, the working variables and the message's
words in variables of their own. The constants are the standard's, worked out from the primes. Jaune has a
SHA-256 too, on arrays of bytes it builds for each block; this one is for the TLS client and for keys, reads
its input where it lies, and does nothing that depends on the bytes it hashes but arithmetic on them.
`tls-test` holds it to the standard's examples and to OpenSSL's. -/

namespace Tls.Sha256

/-- The eight words of the state. -/
structure State where
  a : UInt32
  b : UInt32
  c : UInt32
  d : UInt32
  e : UInt32
  f : UInt32
  g : UInt32
  h : UInt32

@[inline] def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- One block of 64 bytes at `off` taken into the state. -/
def compress (s : State) (b : @& ByteArray) (off : USize) (h : off.toNat + 63 < b.size) : State :=
  let x0 := Fast.swap (Fast.loadAt b off 0 (by omega))
  let w0 := (x0 >>> 32).toUInt32
  let w1 := x0.toUInt32
  let x1 := Fast.swap (Fast.loadAt b off 8 (by omega))
  let w2 := (x1 >>> 32).toUInt32
  let w3 := x1.toUInt32
  let x2 := Fast.swap (Fast.loadAt b off 16 (by omega))
  let w4 := (x2 >>> 32).toUInt32
  let w5 := x2.toUInt32
  let x3 := Fast.swap (Fast.loadAt b off 24 (by omega))
  let w6 := (x3 >>> 32).toUInt32
  let w7 := x3.toUInt32
  let x4 := Fast.swap (Fast.loadAt b off 32 (by omega))
  let w8 := (x4 >>> 32).toUInt32
  let w9 := x4.toUInt32
  let x5 := Fast.swap (Fast.loadAt b off 40 (by omega))
  let w10 := (x5 >>> 32).toUInt32
  let w11 := x5.toUInt32
  let x6 := Fast.swap (Fast.loadAt b off 48 (by omega))
  let w12 := (x6 >>> 32).toUInt32
  let w13 := x6.toUInt32
  let x7 := Fast.swap (Fast.loadAt b off 56 (by omega))
  let w14 := (x7 >>> 32).toUInt32
  let w15 := x7.toUInt32
  let w16 := w0 + (rotr w1 7 ^^^ rotr w1 18 ^^^ (w1 >>> 3)) + w9 + (rotr w14 17 ^^^ rotr w14 19 ^^^ (w14 >>> 10))
  let w17 := w1 + (rotr w2 7 ^^^ rotr w2 18 ^^^ (w2 >>> 3)) + w10 + (rotr w15 17 ^^^ rotr w15 19 ^^^ (w15 >>> 10))
  let w18 := w2 + (rotr w3 7 ^^^ rotr w3 18 ^^^ (w3 >>> 3)) + w11 + (rotr w16 17 ^^^ rotr w16 19 ^^^ (w16 >>> 10))
  let w19 := w3 + (rotr w4 7 ^^^ rotr w4 18 ^^^ (w4 >>> 3)) + w12 + (rotr w17 17 ^^^ rotr w17 19 ^^^ (w17 >>> 10))
  let w20 := w4 + (rotr w5 7 ^^^ rotr w5 18 ^^^ (w5 >>> 3)) + w13 + (rotr w18 17 ^^^ rotr w18 19 ^^^ (w18 >>> 10))
  let w21 := w5 + (rotr w6 7 ^^^ rotr w6 18 ^^^ (w6 >>> 3)) + w14 + (rotr w19 17 ^^^ rotr w19 19 ^^^ (w19 >>> 10))
  let w22 := w6 + (rotr w7 7 ^^^ rotr w7 18 ^^^ (w7 >>> 3)) + w15 + (rotr w20 17 ^^^ rotr w20 19 ^^^ (w20 >>> 10))
  let w23 := w7 + (rotr w8 7 ^^^ rotr w8 18 ^^^ (w8 >>> 3)) + w16 + (rotr w21 17 ^^^ rotr w21 19 ^^^ (w21 >>> 10))
  let w24 := w8 + (rotr w9 7 ^^^ rotr w9 18 ^^^ (w9 >>> 3)) + w17 + (rotr w22 17 ^^^ rotr w22 19 ^^^ (w22 >>> 10))
  let w25 := w9 + (rotr w10 7 ^^^ rotr w10 18 ^^^ (w10 >>> 3)) + w18 + (rotr w23 17 ^^^ rotr w23 19 ^^^ (w23 >>> 10))
  let w26 := w10 + (rotr w11 7 ^^^ rotr w11 18 ^^^ (w11 >>> 3)) + w19 + (rotr w24 17 ^^^ rotr w24 19 ^^^ (w24 >>> 10))
  let w27 := w11 + (rotr w12 7 ^^^ rotr w12 18 ^^^ (w12 >>> 3)) + w20 + (rotr w25 17 ^^^ rotr w25 19 ^^^ (w25 >>> 10))
  let w28 := w12 + (rotr w13 7 ^^^ rotr w13 18 ^^^ (w13 >>> 3)) + w21 + (rotr w26 17 ^^^ rotr w26 19 ^^^ (w26 >>> 10))
  let w29 := w13 + (rotr w14 7 ^^^ rotr w14 18 ^^^ (w14 >>> 3)) + w22 + (rotr w27 17 ^^^ rotr w27 19 ^^^ (w27 >>> 10))
  let w30 := w14 + (rotr w15 7 ^^^ rotr w15 18 ^^^ (w15 >>> 3)) + w23 + (rotr w28 17 ^^^ rotr w28 19 ^^^ (w28 >>> 10))
  let w31 := w15 + (rotr w16 7 ^^^ rotr w16 18 ^^^ (w16 >>> 3)) + w24 + (rotr w29 17 ^^^ rotr w29 19 ^^^ (w29 >>> 10))
  let w32 := w16 + (rotr w17 7 ^^^ rotr w17 18 ^^^ (w17 >>> 3)) + w25 + (rotr w30 17 ^^^ rotr w30 19 ^^^ (w30 >>> 10))
  let w33 := w17 + (rotr w18 7 ^^^ rotr w18 18 ^^^ (w18 >>> 3)) + w26 + (rotr w31 17 ^^^ rotr w31 19 ^^^ (w31 >>> 10))
  let w34 := w18 + (rotr w19 7 ^^^ rotr w19 18 ^^^ (w19 >>> 3)) + w27 + (rotr w32 17 ^^^ rotr w32 19 ^^^ (w32 >>> 10))
  let w35 := w19 + (rotr w20 7 ^^^ rotr w20 18 ^^^ (w20 >>> 3)) + w28 + (rotr w33 17 ^^^ rotr w33 19 ^^^ (w33 >>> 10))
  let w36 := w20 + (rotr w21 7 ^^^ rotr w21 18 ^^^ (w21 >>> 3)) + w29 + (rotr w34 17 ^^^ rotr w34 19 ^^^ (w34 >>> 10))
  let w37 := w21 + (rotr w22 7 ^^^ rotr w22 18 ^^^ (w22 >>> 3)) + w30 + (rotr w35 17 ^^^ rotr w35 19 ^^^ (w35 >>> 10))
  let w38 := w22 + (rotr w23 7 ^^^ rotr w23 18 ^^^ (w23 >>> 3)) + w31 + (rotr w36 17 ^^^ rotr w36 19 ^^^ (w36 >>> 10))
  let w39 := w23 + (rotr w24 7 ^^^ rotr w24 18 ^^^ (w24 >>> 3)) + w32 + (rotr w37 17 ^^^ rotr w37 19 ^^^ (w37 >>> 10))
  let w40 := w24 + (rotr w25 7 ^^^ rotr w25 18 ^^^ (w25 >>> 3)) + w33 + (rotr w38 17 ^^^ rotr w38 19 ^^^ (w38 >>> 10))
  let w41 := w25 + (rotr w26 7 ^^^ rotr w26 18 ^^^ (w26 >>> 3)) + w34 + (rotr w39 17 ^^^ rotr w39 19 ^^^ (w39 >>> 10))
  let w42 := w26 + (rotr w27 7 ^^^ rotr w27 18 ^^^ (w27 >>> 3)) + w35 + (rotr w40 17 ^^^ rotr w40 19 ^^^ (w40 >>> 10))
  let w43 := w27 + (rotr w28 7 ^^^ rotr w28 18 ^^^ (w28 >>> 3)) + w36 + (rotr w41 17 ^^^ rotr w41 19 ^^^ (w41 >>> 10))
  let w44 := w28 + (rotr w29 7 ^^^ rotr w29 18 ^^^ (w29 >>> 3)) + w37 + (rotr w42 17 ^^^ rotr w42 19 ^^^ (w42 >>> 10))
  let w45 := w29 + (rotr w30 7 ^^^ rotr w30 18 ^^^ (w30 >>> 3)) + w38 + (rotr w43 17 ^^^ rotr w43 19 ^^^ (w43 >>> 10))
  let w46 := w30 + (rotr w31 7 ^^^ rotr w31 18 ^^^ (w31 >>> 3)) + w39 + (rotr w44 17 ^^^ rotr w44 19 ^^^ (w44 >>> 10))
  let w47 := w31 + (rotr w32 7 ^^^ rotr w32 18 ^^^ (w32 >>> 3)) + w40 + (rotr w45 17 ^^^ rotr w45 19 ^^^ (w45 >>> 10))
  let w48 := w32 + (rotr w33 7 ^^^ rotr w33 18 ^^^ (w33 >>> 3)) + w41 + (rotr w46 17 ^^^ rotr w46 19 ^^^ (w46 >>> 10))
  let w49 := w33 + (rotr w34 7 ^^^ rotr w34 18 ^^^ (w34 >>> 3)) + w42 + (rotr w47 17 ^^^ rotr w47 19 ^^^ (w47 >>> 10))
  let w50 := w34 + (rotr w35 7 ^^^ rotr w35 18 ^^^ (w35 >>> 3)) + w43 + (rotr w48 17 ^^^ rotr w48 19 ^^^ (w48 >>> 10))
  let w51 := w35 + (rotr w36 7 ^^^ rotr w36 18 ^^^ (w36 >>> 3)) + w44 + (rotr w49 17 ^^^ rotr w49 19 ^^^ (w49 >>> 10))
  let w52 := w36 + (rotr w37 7 ^^^ rotr w37 18 ^^^ (w37 >>> 3)) + w45 + (rotr w50 17 ^^^ rotr w50 19 ^^^ (w50 >>> 10))
  let w53 := w37 + (rotr w38 7 ^^^ rotr w38 18 ^^^ (w38 >>> 3)) + w46 + (rotr w51 17 ^^^ rotr w51 19 ^^^ (w51 >>> 10))
  let w54 := w38 + (rotr w39 7 ^^^ rotr w39 18 ^^^ (w39 >>> 3)) + w47 + (rotr w52 17 ^^^ rotr w52 19 ^^^ (w52 >>> 10))
  let w55 := w39 + (rotr w40 7 ^^^ rotr w40 18 ^^^ (w40 >>> 3)) + w48 + (rotr w53 17 ^^^ rotr w53 19 ^^^ (w53 >>> 10))
  let w56 := w40 + (rotr w41 7 ^^^ rotr w41 18 ^^^ (w41 >>> 3)) + w49 + (rotr w54 17 ^^^ rotr w54 19 ^^^ (w54 >>> 10))
  let w57 := w41 + (rotr w42 7 ^^^ rotr w42 18 ^^^ (w42 >>> 3)) + w50 + (rotr w55 17 ^^^ rotr w55 19 ^^^ (w55 >>> 10))
  let w58 := w42 + (rotr w43 7 ^^^ rotr w43 18 ^^^ (w43 >>> 3)) + w51 + (rotr w56 17 ^^^ rotr w56 19 ^^^ (w56 >>> 10))
  let w59 := w43 + (rotr w44 7 ^^^ rotr w44 18 ^^^ (w44 >>> 3)) + w52 + (rotr w57 17 ^^^ rotr w57 19 ^^^ (w57 >>> 10))
  let w60 := w44 + (rotr w45 7 ^^^ rotr w45 18 ^^^ (w45 >>> 3)) + w53 + (rotr w58 17 ^^^ rotr w58 19 ^^^ (w58 >>> 10))
  let w61 := w45 + (rotr w46 7 ^^^ rotr w46 18 ^^^ (w46 >>> 3)) + w54 + (rotr w59 17 ^^^ rotr w59 19 ^^^ (w59 >>> 10))
  let w62 := w46 + (rotr w47 7 ^^^ rotr w47 18 ^^^ (w47 >>> 3)) + w55 + (rotr w60 17 ^^^ rotr w60 19 ^^^ (w60 >>> 10))
  let w63 := w47 + (rotr w48 7 ^^^ rotr w48 18 ^^^ (w48 >>> 3)) + w56 + (rotr w61 17 ^^^ rotr w61 19 ^^^ (w61 >>> 10))
  let a := s.a
  let b' := s.b
  let c := s.c
  let d := s.d
  let e := s.e
  let f := s.f
  let g := s.g
  let h' := s.h
  let t1 := h' + (rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25) + ((e &&& f) ^^^ (~~~e &&& g)) + 0x428a2f98 + w0
  let t2 := (rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22) + ((a &&& b') ^^^ (a &&& c) ^^^ (b' &&& c))
  let e0 := d + t1
  let a0 := t1 + t2
  let t1 := g + (rotr e0 6 ^^^ rotr e0 11 ^^^ rotr e0 25) + ((e0 &&& e) ^^^ (~~~e0 &&& f)) + 0x71374491 + w1
  let t2 := (rotr a0 2 ^^^ rotr a0 13 ^^^ rotr a0 22) + ((a0 &&& a) ^^^ (a0 &&& b') ^^^ (a &&& b'))
  let e1 := c + t1
  let a1 := t1 + t2
  let t1 := f + (rotr e1 6 ^^^ rotr e1 11 ^^^ rotr e1 25) + ((e1 &&& e0) ^^^ (~~~e1 &&& e)) + 0xb5c0fbcf + w2
  let t2 := (rotr a1 2 ^^^ rotr a1 13 ^^^ rotr a1 22) + ((a1 &&& a0) ^^^ (a1 &&& a) ^^^ (a0 &&& a))
  let e2 := b' + t1
  let a2 := t1 + t2
  let t1 := e + (rotr e2 6 ^^^ rotr e2 11 ^^^ rotr e2 25) + ((e2 &&& e1) ^^^ (~~~e2 &&& e0)) + 0xe9b5dba5 + w3
  let t2 := (rotr a2 2 ^^^ rotr a2 13 ^^^ rotr a2 22) + ((a2 &&& a1) ^^^ (a2 &&& a0) ^^^ (a1 &&& a0))
  let e3 := a + t1
  let a3 := t1 + t2
  let t1 := e0 + (rotr e3 6 ^^^ rotr e3 11 ^^^ rotr e3 25) + ((e3 &&& e2) ^^^ (~~~e3 &&& e1)) + 0x3956c25b + w4
  let t2 := (rotr a3 2 ^^^ rotr a3 13 ^^^ rotr a3 22) + ((a3 &&& a2) ^^^ (a3 &&& a1) ^^^ (a2 &&& a1))
  let e4 := a0 + t1
  let a4 := t1 + t2
  let t1 := e1 + (rotr e4 6 ^^^ rotr e4 11 ^^^ rotr e4 25) + ((e4 &&& e3) ^^^ (~~~e4 &&& e2)) + 0x59f111f1 + w5
  let t2 := (rotr a4 2 ^^^ rotr a4 13 ^^^ rotr a4 22) + ((a4 &&& a3) ^^^ (a4 &&& a2) ^^^ (a3 &&& a2))
  let e5 := a1 + t1
  let a5 := t1 + t2
  let t1 := e2 + (rotr e5 6 ^^^ rotr e5 11 ^^^ rotr e5 25) + ((e5 &&& e4) ^^^ (~~~e5 &&& e3)) + 0x923f82a4 + w6
  let t2 := (rotr a5 2 ^^^ rotr a5 13 ^^^ rotr a5 22) + ((a5 &&& a4) ^^^ (a5 &&& a3) ^^^ (a4 &&& a3))
  let e6 := a2 + t1
  let a6 := t1 + t2
  let t1 := e3 + (rotr e6 6 ^^^ rotr e6 11 ^^^ rotr e6 25) + ((e6 &&& e5) ^^^ (~~~e6 &&& e4)) + 0xab1c5ed5 + w7
  let t2 := (rotr a6 2 ^^^ rotr a6 13 ^^^ rotr a6 22) + ((a6 &&& a5) ^^^ (a6 &&& a4) ^^^ (a5 &&& a4))
  let e7 := a3 + t1
  let a7 := t1 + t2
  let t1 := e4 + (rotr e7 6 ^^^ rotr e7 11 ^^^ rotr e7 25) + ((e7 &&& e6) ^^^ (~~~e7 &&& e5)) + 0xd807aa98 + w8
  let t2 := (rotr a7 2 ^^^ rotr a7 13 ^^^ rotr a7 22) + ((a7 &&& a6) ^^^ (a7 &&& a5) ^^^ (a6 &&& a5))
  let e8 := a4 + t1
  let a8 := t1 + t2
  let t1 := e5 + (rotr e8 6 ^^^ rotr e8 11 ^^^ rotr e8 25) + ((e8 &&& e7) ^^^ (~~~e8 &&& e6)) + 0x12835b01 + w9
  let t2 := (rotr a8 2 ^^^ rotr a8 13 ^^^ rotr a8 22) + ((a8 &&& a7) ^^^ (a8 &&& a6) ^^^ (a7 &&& a6))
  let e9 := a5 + t1
  let a9 := t1 + t2
  let t1 := e6 + (rotr e9 6 ^^^ rotr e9 11 ^^^ rotr e9 25) + ((e9 &&& e8) ^^^ (~~~e9 &&& e7)) + 0x243185be + w10
  let t2 := (rotr a9 2 ^^^ rotr a9 13 ^^^ rotr a9 22) + ((a9 &&& a8) ^^^ (a9 &&& a7) ^^^ (a8 &&& a7))
  let e10 := a6 + t1
  let a10 := t1 + t2
  let t1 := e7 + (rotr e10 6 ^^^ rotr e10 11 ^^^ rotr e10 25) + ((e10 &&& e9) ^^^ (~~~e10 &&& e8)) + 0x550c7dc3 + w11
  let t2 := (rotr a10 2 ^^^ rotr a10 13 ^^^ rotr a10 22) + ((a10 &&& a9) ^^^ (a10 &&& a8) ^^^ (a9 &&& a8))
  let e11 := a7 + t1
  let a11 := t1 + t2
  let t1 := e8 + (rotr e11 6 ^^^ rotr e11 11 ^^^ rotr e11 25) + ((e11 &&& e10) ^^^ (~~~e11 &&& e9)) + 0x72be5d74 + w12
  let t2 := (rotr a11 2 ^^^ rotr a11 13 ^^^ rotr a11 22) + ((a11 &&& a10) ^^^ (a11 &&& a9) ^^^ (a10 &&& a9))
  let e12 := a8 + t1
  let a12 := t1 + t2
  let t1 := e9 + (rotr e12 6 ^^^ rotr e12 11 ^^^ rotr e12 25) + ((e12 &&& e11) ^^^ (~~~e12 &&& e10)) + 0x80deb1fe + w13
  let t2 := (rotr a12 2 ^^^ rotr a12 13 ^^^ rotr a12 22) + ((a12 &&& a11) ^^^ (a12 &&& a10) ^^^ (a11 &&& a10))
  let e13 := a9 + t1
  let a13 := t1 + t2
  let t1 := e10 + (rotr e13 6 ^^^ rotr e13 11 ^^^ rotr e13 25) + ((e13 &&& e12) ^^^ (~~~e13 &&& e11)) + 0x9bdc06a7 + w14
  let t2 := (rotr a13 2 ^^^ rotr a13 13 ^^^ rotr a13 22) + ((a13 &&& a12) ^^^ (a13 &&& a11) ^^^ (a12 &&& a11))
  let e14 := a10 + t1
  let a14 := t1 + t2
  let t1 := e11 + (rotr e14 6 ^^^ rotr e14 11 ^^^ rotr e14 25) + ((e14 &&& e13) ^^^ (~~~e14 &&& e12)) + 0xc19bf174 + w15
  let t2 := (rotr a14 2 ^^^ rotr a14 13 ^^^ rotr a14 22) + ((a14 &&& a13) ^^^ (a14 &&& a12) ^^^ (a13 &&& a12))
  let e15 := a11 + t1
  let a15 := t1 + t2
  let t1 := e12 + (rotr e15 6 ^^^ rotr e15 11 ^^^ rotr e15 25) + ((e15 &&& e14) ^^^ (~~~e15 &&& e13)) + 0xe49b69c1 + w16
  let t2 := (rotr a15 2 ^^^ rotr a15 13 ^^^ rotr a15 22) + ((a15 &&& a14) ^^^ (a15 &&& a13) ^^^ (a14 &&& a13))
  let e16 := a12 + t1
  let a16 := t1 + t2
  let t1 := e13 + (rotr e16 6 ^^^ rotr e16 11 ^^^ rotr e16 25) + ((e16 &&& e15) ^^^ (~~~e16 &&& e14)) + 0xefbe4786 + w17
  let t2 := (rotr a16 2 ^^^ rotr a16 13 ^^^ rotr a16 22) + ((a16 &&& a15) ^^^ (a16 &&& a14) ^^^ (a15 &&& a14))
  let e17 := a13 + t1
  let a17 := t1 + t2
  let t1 := e14 + (rotr e17 6 ^^^ rotr e17 11 ^^^ rotr e17 25) + ((e17 &&& e16) ^^^ (~~~e17 &&& e15)) + 0x0fc19dc6 + w18
  let t2 := (rotr a17 2 ^^^ rotr a17 13 ^^^ rotr a17 22) + ((a17 &&& a16) ^^^ (a17 &&& a15) ^^^ (a16 &&& a15))
  let e18 := a14 + t1
  let a18 := t1 + t2
  let t1 := e15 + (rotr e18 6 ^^^ rotr e18 11 ^^^ rotr e18 25) + ((e18 &&& e17) ^^^ (~~~e18 &&& e16)) + 0x240ca1cc + w19
  let t2 := (rotr a18 2 ^^^ rotr a18 13 ^^^ rotr a18 22) + ((a18 &&& a17) ^^^ (a18 &&& a16) ^^^ (a17 &&& a16))
  let e19 := a15 + t1
  let a19 := t1 + t2
  let t1 := e16 + (rotr e19 6 ^^^ rotr e19 11 ^^^ rotr e19 25) + ((e19 &&& e18) ^^^ (~~~e19 &&& e17)) + 0x2de92c6f + w20
  let t2 := (rotr a19 2 ^^^ rotr a19 13 ^^^ rotr a19 22) + ((a19 &&& a18) ^^^ (a19 &&& a17) ^^^ (a18 &&& a17))
  let e20 := a16 + t1
  let a20 := t1 + t2
  let t1 := e17 + (rotr e20 6 ^^^ rotr e20 11 ^^^ rotr e20 25) + ((e20 &&& e19) ^^^ (~~~e20 &&& e18)) + 0x4a7484aa + w21
  let t2 := (rotr a20 2 ^^^ rotr a20 13 ^^^ rotr a20 22) + ((a20 &&& a19) ^^^ (a20 &&& a18) ^^^ (a19 &&& a18))
  let e21 := a17 + t1
  let a21 := t1 + t2
  let t1 := e18 + (rotr e21 6 ^^^ rotr e21 11 ^^^ rotr e21 25) + ((e21 &&& e20) ^^^ (~~~e21 &&& e19)) + 0x5cb0a9dc + w22
  let t2 := (rotr a21 2 ^^^ rotr a21 13 ^^^ rotr a21 22) + ((a21 &&& a20) ^^^ (a21 &&& a19) ^^^ (a20 &&& a19))
  let e22 := a18 + t1
  let a22 := t1 + t2
  let t1 := e19 + (rotr e22 6 ^^^ rotr e22 11 ^^^ rotr e22 25) + ((e22 &&& e21) ^^^ (~~~e22 &&& e20)) + 0x76f988da + w23
  let t2 := (rotr a22 2 ^^^ rotr a22 13 ^^^ rotr a22 22) + ((a22 &&& a21) ^^^ (a22 &&& a20) ^^^ (a21 &&& a20))
  let e23 := a19 + t1
  let a23 := t1 + t2
  let t1 := e20 + (rotr e23 6 ^^^ rotr e23 11 ^^^ rotr e23 25) + ((e23 &&& e22) ^^^ (~~~e23 &&& e21)) + 0x983e5152 + w24
  let t2 := (rotr a23 2 ^^^ rotr a23 13 ^^^ rotr a23 22) + ((a23 &&& a22) ^^^ (a23 &&& a21) ^^^ (a22 &&& a21))
  let e24 := a20 + t1
  let a24 := t1 + t2
  let t1 := e21 + (rotr e24 6 ^^^ rotr e24 11 ^^^ rotr e24 25) + ((e24 &&& e23) ^^^ (~~~e24 &&& e22)) + 0xa831c66d + w25
  let t2 := (rotr a24 2 ^^^ rotr a24 13 ^^^ rotr a24 22) + ((a24 &&& a23) ^^^ (a24 &&& a22) ^^^ (a23 &&& a22))
  let e25 := a21 + t1
  let a25 := t1 + t2
  let t1 := e22 + (rotr e25 6 ^^^ rotr e25 11 ^^^ rotr e25 25) + ((e25 &&& e24) ^^^ (~~~e25 &&& e23)) + 0xb00327c8 + w26
  let t2 := (rotr a25 2 ^^^ rotr a25 13 ^^^ rotr a25 22) + ((a25 &&& a24) ^^^ (a25 &&& a23) ^^^ (a24 &&& a23))
  let e26 := a22 + t1
  let a26 := t1 + t2
  let t1 := e23 + (rotr e26 6 ^^^ rotr e26 11 ^^^ rotr e26 25) + ((e26 &&& e25) ^^^ (~~~e26 &&& e24)) + 0xbf597fc7 + w27
  let t2 := (rotr a26 2 ^^^ rotr a26 13 ^^^ rotr a26 22) + ((a26 &&& a25) ^^^ (a26 &&& a24) ^^^ (a25 &&& a24))
  let e27 := a23 + t1
  let a27 := t1 + t2
  let t1 := e24 + (rotr e27 6 ^^^ rotr e27 11 ^^^ rotr e27 25) + ((e27 &&& e26) ^^^ (~~~e27 &&& e25)) + 0xc6e00bf3 + w28
  let t2 := (rotr a27 2 ^^^ rotr a27 13 ^^^ rotr a27 22) + ((a27 &&& a26) ^^^ (a27 &&& a25) ^^^ (a26 &&& a25))
  let e28 := a24 + t1
  let a28 := t1 + t2
  let t1 := e25 + (rotr e28 6 ^^^ rotr e28 11 ^^^ rotr e28 25) + ((e28 &&& e27) ^^^ (~~~e28 &&& e26)) + 0xd5a79147 + w29
  let t2 := (rotr a28 2 ^^^ rotr a28 13 ^^^ rotr a28 22) + ((a28 &&& a27) ^^^ (a28 &&& a26) ^^^ (a27 &&& a26))
  let e29 := a25 + t1
  let a29 := t1 + t2
  let t1 := e26 + (rotr e29 6 ^^^ rotr e29 11 ^^^ rotr e29 25) + ((e29 &&& e28) ^^^ (~~~e29 &&& e27)) + 0x06ca6351 + w30
  let t2 := (rotr a29 2 ^^^ rotr a29 13 ^^^ rotr a29 22) + ((a29 &&& a28) ^^^ (a29 &&& a27) ^^^ (a28 &&& a27))
  let e30 := a26 + t1
  let a30 := t1 + t2
  let t1 := e27 + (rotr e30 6 ^^^ rotr e30 11 ^^^ rotr e30 25) + ((e30 &&& e29) ^^^ (~~~e30 &&& e28)) + 0x14292967 + w31
  let t2 := (rotr a30 2 ^^^ rotr a30 13 ^^^ rotr a30 22) + ((a30 &&& a29) ^^^ (a30 &&& a28) ^^^ (a29 &&& a28))
  let e31 := a27 + t1
  let a31 := t1 + t2
  let t1 := e28 + (rotr e31 6 ^^^ rotr e31 11 ^^^ rotr e31 25) + ((e31 &&& e30) ^^^ (~~~e31 &&& e29)) + 0x27b70a85 + w32
  let t2 := (rotr a31 2 ^^^ rotr a31 13 ^^^ rotr a31 22) + ((a31 &&& a30) ^^^ (a31 &&& a29) ^^^ (a30 &&& a29))
  let e32 := a28 + t1
  let a32 := t1 + t2
  let t1 := e29 + (rotr e32 6 ^^^ rotr e32 11 ^^^ rotr e32 25) + ((e32 &&& e31) ^^^ (~~~e32 &&& e30)) + 0x2e1b2138 + w33
  let t2 := (rotr a32 2 ^^^ rotr a32 13 ^^^ rotr a32 22) + ((a32 &&& a31) ^^^ (a32 &&& a30) ^^^ (a31 &&& a30))
  let e33 := a29 + t1
  let a33 := t1 + t2
  let t1 := e30 + (rotr e33 6 ^^^ rotr e33 11 ^^^ rotr e33 25) + ((e33 &&& e32) ^^^ (~~~e33 &&& e31)) + 0x4d2c6dfc + w34
  let t2 := (rotr a33 2 ^^^ rotr a33 13 ^^^ rotr a33 22) + ((a33 &&& a32) ^^^ (a33 &&& a31) ^^^ (a32 &&& a31))
  let e34 := a30 + t1
  let a34 := t1 + t2
  let t1 := e31 + (rotr e34 6 ^^^ rotr e34 11 ^^^ rotr e34 25) + ((e34 &&& e33) ^^^ (~~~e34 &&& e32)) + 0x53380d13 + w35
  let t2 := (rotr a34 2 ^^^ rotr a34 13 ^^^ rotr a34 22) + ((a34 &&& a33) ^^^ (a34 &&& a32) ^^^ (a33 &&& a32))
  let e35 := a31 + t1
  let a35 := t1 + t2
  let t1 := e32 + (rotr e35 6 ^^^ rotr e35 11 ^^^ rotr e35 25) + ((e35 &&& e34) ^^^ (~~~e35 &&& e33)) + 0x650a7354 + w36
  let t2 := (rotr a35 2 ^^^ rotr a35 13 ^^^ rotr a35 22) + ((a35 &&& a34) ^^^ (a35 &&& a33) ^^^ (a34 &&& a33))
  let e36 := a32 + t1
  let a36 := t1 + t2
  let t1 := e33 + (rotr e36 6 ^^^ rotr e36 11 ^^^ rotr e36 25) + ((e36 &&& e35) ^^^ (~~~e36 &&& e34)) + 0x766a0abb + w37
  let t2 := (rotr a36 2 ^^^ rotr a36 13 ^^^ rotr a36 22) + ((a36 &&& a35) ^^^ (a36 &&& a34) ^^^ (a35 &&& a34))
  let e37 := a33 + t1
  let a37 := t1 + t2
  let t1 := e34 + (rotr e37 6 ^^^ rotr e37 11 ^^^ rotr e37 25) + ((e37 &&& e36) ^^^ (~~~e37 &&& e35)) + 0x81c2c92e + w38
  let t2 := (rotr a37 2 ^^^ rotr a37 13 ^^^ rotr a37 22) + ((a37 &&& a36) ^^^ (a37 &&& a35) ^^^ (a36 &&& a35))
  let e38 := a34 + t1
  let a38 := t1 + t2
  let t1 := e35 + (rotr e38 6 ^^^ rotr e38 11 ^^^ rotr e38 25) + ((e38 &&& e37) ^^^ (~~~e38 &&& e36)) + 0x92722c85 + w39
  let t2 := (rotr a38 2 ^^^ rotr a38 13 ^^^ rotr a38 22) + ((a38 &&& a37) ^^^ (a38 &&& a36) ^^^ (a37 &&& a36))
  let e39 := a35 + t1
  let a39 := t1 + t2
  let t1 := e36 + (rotr e39 6 ^^^ rotr e39 11 ^^^ rotr e39 25) + ((e39 &&& e38) ^^^ (~~~e39 &&& e37)) + 0xa2bfe8a1 + w40
  let t2 := (rotr a39 2 ^^^ rotr a39 13 ^^^ rotr a39 22) + ((a39 &&& a38) ^^^ (a39 &&& a37) ^^^ (a38 &&& a37))
  let e40 := a36 + t1
  let a40 := t1 + t2
  let t1 := e37 + (rotr e40 6 ^^^ rotr e40 11 ^^^ rotr e40 25) + ((e40 &&& e39) ^^^ (~~~e40 &&& e38)) + 0xa81a664b + w41
  let t2 := (rotr a40 2 ^^^ rotr a40 13 ^^^ rotr a40 22) + ((a40 &&& a39) ^^^ (a40 &&& a38) ^^^ (a39 &&& a38))
  let e41 := a37 + t1
  let a41 := t1 + t2
  let t1 := e38 + (rotr e41 6 ^^^ rotr e41 11 ^^^ rotr e41 25) + ((e41 &&& e40) ^^^ (~~~e41 &&& e39)) + 0xc24b8b70 + w42
  let t2 := (rotr a41 2 ^^^ rotr a41 13 ^^^ rotr a41 22) + ((a41 &&& a40) ^^^ (a41 &&& a39) ^^^ (a40 &&& a39))
  let e42 := a38 + t1
  let a42 := t1 + t2
  let t1 := e39 + (rotr e42 6 ^^^ rotr e42 11 ^^^ rotr e42 25) + ((e42 &&& e41) ^^^ (~~~e42 &&& e40)) + 0xc76c51a3 + w43
  let t2 := (rotr a42 2 ^^^ rotr a42 13 ^^^ rotr a42 22) + ((a42 &&& a41) ^^^ (a42 &&& a40) ^^^ (a41 &&& a40))
  let e43 := a39 + t1
  let a43 := t1 + t2
  let t1 := e40 + (rotr e43 6 ^^^ rotr e43 11 ^^^ rotr e43 25) + ((e43 &&& e42) ^^^ (~~~e43 &&& e41)) + 0xd192e819 + w44
  let t2 := (rotr a43 2 ^^^ rotr a43 13 ^^^ rotr a43 22) + ((a43 &&& a42) ^^^ (a43 &&& a41) ^^^ (a42 &&& a41))
  let e44 := a40 + t1
  let a44 := t1 + t2
  let t1 := e41 + (rotr e44 6 ^^^ rotr e44 11 ^^^ rotr e44 25) + ((e44 &&& e43) ^^^ (~~~e44 &&& e42)) + 0xd6990624 + w45
  let t2 := (rotr a44 2 ^^^ rotr a44 13 ^^^ rotr a44 22) + ((a44 &&& a43) ^^^ (a44 &&& a42) ^^^ (a43 &&& a42))
  let e45 := a41 + t1
  let a45 := t1 + t2
  let t1 := e42 + (rotr e45 6 ^^^ rotr e45 11 ^^^ rotr e45 25) + ((e45 &&& e44) ^^^ (~~~e45 &&& e43)) + 0xf40e3585 + w46
  let t2 := (rotr a45 2 ^^^ rotr a45 13 ^^^ rotr a45 22) + ((a45 &&& a44) ^^^ (a45 &&& a43) ^^^ (a44 &&& a43))
  let e46 := a42 + t1
  let a46 := t1 + t2
  let t1 := e43 + (rotr e46 6 ^^^ rotr e46 11 ^^^ rotr e46 25) + ((e46 &&& e45) ^^^ (~~~e46 &&& e44)) + 0x106aa070 + w47
  let t2 := (rotr a46 2 ^^^ rotr a46 13 ^^^ rotr a46 22) + ((a46 &&& a45) ^^^ (a46 &&& a44) ^^^ (a45 &&& a44))
  let e47 := a43 + t1
  let a47 := t1 + t2
  let t1 := e44 + (rotr e47 6 ^^^ rotr e47 11 ^^^ rotr e47 25) + ((e47 &&& e46) ^^^ (~~~e47 &&& e45)) + 0x19a4c116 + w48
  let t2 := (rotr a47 2 ^^^ rotr a47 13 ^^^ rotr a47 22) + ((a47 &&& a46) ^^^ (a47 &&& a45) ^^^ (a46 &&& a45))
  let e48 := a44 + t1
  let a48 := t1 + t2
  let t1 := e45 + (rotr e48 6 ^^^ rotr e48 11 ^^^ rotr e48 25) + ((e48 &&& e47) ^^^ (~~~e48 &&& e46)) + 0x1e376c08 + w49
  let t2 := (rotr a48 2 ^^^ rotr a48 13 ^^^ rotr a48 22) + ((a48 &&& a47) ^^^ (a48 &&& a46) ^^^ (a47 &&& a46))
  let e49 := a45 + t1
  let a49 := t1 + t2
  let t1 := e46 + (rotr e49 6 ^^^ rotr e49 11 ^^^ rotr e49 25) + ((e49 &&& e48) ^^^ (~~~e49 &&& e47)) + 0x2748774c + w50
  let t2 := (rotr a49 2 ^^^ rotr a49 13 ^^^ rotr a49 22) + ((a49 &&& a48) ^^^ (a49 &&& a47) ^^^ (a48 &&& a47))
  let e50 := a46 + t1
  let a50 := t1 + t2
  let t1 := e47 + (rotr e50 6 ^^^ rotr e50 11 ^^^ rotr e50 25) + ((e50 &&& e49) ^^^ (~~~e50 &&& e48)) + 0x34b0bcb5 + w51
  let t2 := (rotr a50 2 ^^^ rotr a50 13 ^^^ rotr a50 22) + ((a50 &&& a49) ^^^ (a50 &&& a48) ^^^ (a49 &&& a48))
  let e51 := a47 + t1
  let a51 := t1 + t2
  let t1 := e48 + (rotr e51 6 ^^^ rotr e51 11 ^^^ rotr e51 25) + ((e51 &&& e50) ^^^ (~~~e51 &&& e49)) + 0x391c0cb3 + w52
  let t2 := (rotr a51 2 ^^^ rotr a51 13 ^^^ rotr a51 22) + ((a51 &&& a50) ^^^ (a51 &&& a49) ^^^ (a50 &&& a49))
  let e52 := a48 + t1
  let a52 := t1 + t2
  let t1 := e49 + (rotr e52 6 ^^^ rotr e52 11 ^^^ rotr e52 25) + ((e52 &&& e51) ^^^ (~~~e52 &&& e50)) + 0x4ed8aa4a + w53
  let t2 := (rotr a52 2 ^^^ rotr a52 13 ^^^ rotr a52 22) + ((a52 &&& a51) ^^^ (a52 &&& a50) ^^^ (a51 &&& a50))
  let e53 := a49 + t1
  let a53 := t1 + t2
  let t1 := e50 + (rotr e53 6 ^^^ rotr e53 11 ^^^ rotr e53 25) + ((e53 &&& e52) ^^^ (~~~e53 &&& e51)) + 0x5b9cca4f + w54
  let t2 := (rotr a53 2 ^^^ rotr a53 13 ^^^ rotr a53 22) + ((a53 &&& a52) ^^^ (a53 &&& a51) ^^^ (a52 &&& a51))
  let e54 := a50 + t1
  let a54 := t1 + t2
  let t1 := e51 + (rotr e54 6 ^^^ rotr e54 11 ^^^ rotr e54 25) + ((e54 &&& e53) ^^^ (~~~e54 &&& e52)) + 0x682e6ff3 + w55
  let t2 := (rotr a54 2 ^^^ rotr a54 13 ^^^ rotr a54 22) + ((a54 &&& a53) ^^^ (a54 &&& a52) ^^^ (a53 &&& a52))
  let e55 := a51 + t1
  let a55 := t1 + t2
  let t1 := e52 + (rotr e55 6 ^^^ rotr e55 11 ^^^ rotr e55 25) + ((e55 &&& e54) ^^^ (~~~e55 &&& e53)) + 0x748f82ee + w56
  let t2 := (rotr a55 2 ^^^ rotr a55 13 ^^^ rotr a55 22) + ((a55 &&& a54) ^^^ (a55 &&& a53) ^^^ (a54 &&& a53))
  let e56 := a52 + t1
  let a56 := t1 + t2
  let t1 := e53 + (rotr e56 6 ^^^ rotr e56 11 ^^^ rotr e56 25) + ((e56 &&& e55) ^^^ (~~~e56 &&& e54)) + 0x78a5636f + w57
  let t2 := (rotr a56 2 ^^^ rotr a56 13 ^^^ rotr a56 22) + ((a56 &&& a55) ^^^ (a56 &&& a54) ^^^ (a55 &&& a54))
  let e57 := a53 + t1
  let a57 := t1 + t2
  let t1 := e54 + (rotr e57 6 ^^^ rotr e57 11 ^^^ rotr e57 25) + ((e57 &&& e56) ^^^ (~~~e57 &&& e55)) + 0x84c87814 + w58
  let t2 := (rotr a57 2 ^^^ rotr a57 13 ^^^ rotr a57 22) + ((a57 &&& a56) ^^^ (a57 &&& a55) ^^^ (a56 &&& a55))
  let e58 := a54 + t1
  let a58 := t1 + t2
  let t1 := e55 + (rotr e58 6 ^^^ rotr e58 11 ^^^ rotr e58 25) + ((e58 &&& e57) ^^^ (~~~e58 &&& e56)) + 0x8cc70208 + w59
  let t2 := (rotr a58 2 ^^^ rotr a58 13 ^^^ rotr a58 22) + ((a58 &&& a57) ^^^ (a58 &&& a56) ^^^ (a57 &&& a56))
  let e59 := a55 + t1
  let a59 := t1 + t2
  let t1 := e56 + (rotr e59 6 ^^^ rotr e59 11 ^^^ rotr e59 25) + ((e59 &&& e58) ^^^ (~~~e59 &&& e57)) + 0x90befffa + w60
  let t2 := (rotr a59 2 ^^^ rotr a59 13 ^^^ rotr a59 22) + ((a59 &&& a58) ^^^ (a59 &&& a57) ^^^ (a58 &&& a57))
  let e60 := a56 + t1
  let a60 := t1 + t2
  let t1 := e57 + (rotr e60 6 ^^^ rotr e60 11 ^^^ rotr e60 25) + ((e60 &&& e59) ^^^ (~~~e60 &&& e58)) + 0xa4506ceb + w61
  let t2 := (rotr a60 2 ^^^ rotr a60 13 ^^^ rotr a60 22) + ((a60 &&& a59) ^^^ (a60 &&& a58) ^^^ (a59 &&& a58))
  let e61 := a57 + t1
  let a61 := t1 + t2
  let t1 := e58 + (rotr e61 6 ^^^ rotr e61 11 ^^^ rotr e61 25) + ((e61 &&& e60) ^^^ (~~~e61 &&& e59)) + 0xbef9a3f7 + w62
  let t2 := (rotr a61 2 ^^^ rotr a61 13 ^^^ rotr a61 22) + ((a61 &&& a60) ^^^ (a61 &&& a59) ^^^ (a60 &&& a59))
  let e62 := a58 + t1
  let a62 := t1 + t2
  let t1 := e59 + (rotr e62 6 ^^^ rotr e62 11 ^^^ rotr e62 25) + ((e62 &&& e61) ^^^ (~~~e62 &&& e60)) + 0xc67178f2 + w63
  let t2 := (rotr a62 2 ^^^ rotr a62 13 ^^^ rotr a62 22) + ((a62 &&& a61) ^^^ (a62 &&& a60) ^^^ (a61 &&& a60))
  let e63 := a59 + t1
  let a63 := t1 + t2
  ⟨s.a + a63, s.b + a62, s.c + a61, s.d + a60, s.e + e63, s.f + e62, s.g + e61, s.h + e60⟩

/-- Every whole block of `b` from `off`, `left` of them. -/
def blocks (b : @& ByteArray) : Nat → USize → State → State
  | 0, _, s => s
  | left + 1, off, s =>
    if h : off.toNat + 63 < b.size then blocks b left (off + 64) (compress s b off h) else s

/-- What is left of a message after its whole blocks, padded as the standard has it: a one bit, zeros,
and the length of the whole message in bits. One block, or two when the rest leaves no room. -/
def padded (b : @& ByteArray) (whole : Nat) : ByteArray :=
  let rest := b.extract whole b.size
  let lengthBytes := 8
  let total := if rest.size + 1 + lengthBytes ≤ 64 then 64 else 128
  let zeros := ByteArray.mk (Array.replicate (total - rest.size - 1 - 8) 0)
  let bitsLong := (b.size * 8).toUInt64
  (rest.push 0x80 ++ zeros) ++ ByteArray.mk ((List.range 8).map fun i => (bitsLong >>> (56 - 8 * i).toUInt64).toUInt8).toArray

/-- The state after all of `b`, from the starting state `start`. -/
def run (start : State) (b : @& ByteArray) : State :=
  let count := b.size / 64
  let s := blocks b count 0 start
  let last := padded b (count * 64)
  blocks last (last.size / 64) 0 s

def start : State := ⟨0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19⟩

@[inline] def word (out : ByteArray) (x : UInt32) : ByteArray :=
  out.push (x >>> 24).toUInt8 |>.push (x >>> 16).toUInt8 |>.push (x >>> 8).toUInt8 |>.push x.toUInt8

/-- SHA-256 of `b`: 32 bytes. -/
def hash (b : @& ByteArray) : ByteArray :=
  let s := run start b
  [s.a, s.b, s.c, s.d, s.e, s.f, s.g, s.h].foldl word (ByteArray.emptyWithCapacity 32)

end Tls.Sha256
