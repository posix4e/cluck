/-! Reading and writing machine words in a byte array where they lie, for the fast engine. Every access is
`uget` or `uset` with its bound proved from one comparison the caller made, so a word costs one check, and a
write is in place whenever the array has one owner. -/

namespace Fast

theorem within {n : Nat} {off : USize} (k : Nat) (h : off.toNat + k < n) : (off + USize.ofNat k).toNat < n := by
  have h1 : (off + USize.ofNat k).toNat ≤ off.toNat + (USize.ofNat k).toNat := by
    rw [USize.toNat_add]; exact Nat.mod_le _ _
  have h2 : (USize.ofNat k).toNat ≤ k := by
    rw [USize.toNat_ofNat']; exact Nat.mod_le _ _
  omega

theorem size_uset (a : ByteArray) (i : USize) (v : UInt8) (h : i.toNat < a.size) : (a.uset i v h).size = a.size := by
  cases a; simp [ByteArray.uset, ByteArray.size]

/-- Eight bytes from `off`, least significant first. -/
@[inline] def load (a : @& ByteArray) (off : USize) (h : off.toNat + 7 < a.size) : UInt64 :=
  (a.uget off (by omega)).toUInt64 |||
  ((a.uget (off + USize.ofNat 1) (within 1 (by omega))).toUInt64 <<< 8) |||
  ((a.uget (off + USize.ofNat 2) (within 2 (by omega))).toUInt64 <<< 16) |||
  ((a.uget (off + USize.ofNat 3) (within 3 (by omega))).toUInt64 <<< 24) |||
  ((a.uget (off + USize.ofNat 4) (within 4 (by omega))).toUInt64 <<< 32) |||
  ((a.uget (off + USize.ofNat 5) (within 5 (by omega))).toUInt64 <<< 40) |||
  ((a.uget (off + USize.ofNat 6) (within 6 (by omega))).toUInt64 <<< 48) |||
  ((a.uget (off + USize.ofNat 7) (within 7 (by omega))).toUInt64 <<< 56)

/-- Eight bytes from `off + k`, least significant first, within a run of bytes the caller has checked. -/
@[inline] def loadAt (a : @& ByteArray) (off : USize) (k : Nat) (h : off.toNat + k + 7 < a.size) : UInt64 :=
  load a (off + USize.ofNat k) (by have := within (n := a.size - 7) (off := off) k (by omega); omega)

/-- One byte written, with the array's size carried along so that the next write needs no new check. -/
@[inline] def set1 {n : Nat} (a : {a : ByteArray // a.size = n}) (off : USize) (v : UInt8) (h : off.toNat < n) :
    {a : ByteArray // a.size = n} :=
  ⟨a.1.uset off v (by rw [a.2]; exact h), by rw [size_uset]; exact a.2⟩

/-- Eight bytes written at `off`, least significant first, when they fit; the array as it was when not. -/
@[inline] def store (a : ByteArray) (off : USize) (x : UInt64) : ByteArray :=
  if h : off.toNat + 7 < a.size then
    let r : {b : ByteArray // b.size = a.size} := ⟨a, rfl⟩
    let r := set1 r off x.toUInt8 (by omega)
    let r := set1 r (off + USize.ofNat 1) (x >>> 8).toUInt8 (within 1 (by omega))
    let r := set1 r (off + USize.ofNat 2) (x >>> 16).toUInt8 (within 2 (by omega))
    let r := set1 r (off + USize.ofNat 3) (x >>> 24).toUInt8 (within 3 (by omega))
    let r := set1 r (off + USize.ofNat 4) (x >>> 32).toUInt8 (within 4 (by omega))
    let r := set1 r (off + USize.ofNat 5) (x >>> 40).toUInt8 (within 5 (by omega))
    let r := set1 r (off + USize.ofNat 6) (x >>> 48).toUInt8 (within 6 (by omega))
    (set1 r (off + USize.ofNat 7) (x >>> 56).toUInt8 (within 7 (by omega))).1
  else a

/-- The byte at `i`, and nothing for a place past the end. -/
@[inline] def byte (b : @& ByteArray) (i : Nat) : UInt8 := if h : i < b.size then b[i] else 0

/-- The eight bytes of a word in the opposite order. -/
@[inline] def swap (x : UInt64) : UInt64 :=
  let x := ((x &&& 0x00ff00ff00ff00ff) <<< 8) ||| ((x >>> 8) &&& 0x00ff00ff00ff00ff)
  let x := ((x &&& 0x0000ffff0000ffff) <<< 16) ||| ((x >>> 16) &&& 0x0000ffff0000ffff)
  (x <<< 32) ||| (x >>> 32)

end Fast
