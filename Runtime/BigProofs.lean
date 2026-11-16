import Runtime.Big

/-! # What the runtime's arithmetic computes

`Runtime/Big.lean` works on limbs. This says what number a row of limbs is, and proves that each operation
returns the limbs of the number it should: the sum, the difference, the product, and so on, as Lean's `Nat`
defines them. Nothing here runs; no image imports it. -/

namespace Runtime.Big

local notation "B" => (4294967296 : Nat)

/-- The number a list of limbs is, least significant first. -/
def valueList : List UInt32 → Nat
  | [] => 0
  | x :: xs => x.toNat + B * valueList xs

/-- The number an array of limbs is. -/
def value (a : Limbs) : Nat := valueList a.toList

/-- The number the limbs from `i` up are. -/
def tail (a : Limbs) (i : Nat) : Nat := valueList (a.toList.drop i)

/-- Limb `i` as a number; zero beyond the end. -/
def digit (a : Limbs) (i : Nat) : Nat := (a.getD i 0).toNat

theorem valueList_append (xs ys : List UInt32) :
    valueList (xs ++ ys) = valueList xs + B ^ xs.length * valueList ys := by
  induction xs with
  | nil => simp [valueList]
  | cons x xs ih =>
    simp only [List.cons_append, valueList, ih, List.length_cons, Nat.pow_succ]
    rw [Nat.mul_add, Nat.add_assoc, Nat.mul_left_comm, Nat.mul_assoc]

theorem value_push (a : Limbs) (x : UInt32) : value (a.push x) = value a + B ^ a.size * x.toNat := by
  simp [value, Array.toList_push, valueList_append, valueList]

theorem tail_zero (a : Limbs) : tail a 0 = value a := by simp [tail, value]

theorem digit_lt (a : Limbs) (i : Nat) : digit a i < B := (a.getD i 0).toNat_lt

theorem tail_step (a : Limbs) (i : Nat) : tail a i = digit a i + B * tail a (i + 1) := by
  by_cases h : i < a.size
  · have : a.toList.drop i = a[i] :: a.toList.drop (i + 1) := by
      rw [List.drop_eq_getElem_cons (by simpa using h)]; simp
    simp [tail, digit, this, valueList, Array.getD, h]
  · have h1 : a.toList.drop i = [] := List.drop_eq_nil_of_le (by simp; omega)
    have h2 : a.toList.drop (i + 1) = [] := List.drop_eq_nil_of_le (by simp; omega)
    simp [tail, digit, h1, h2, valueList, Array.getD, h]

theorem tail_of_le (a : Limbs) (i : Nat) (h : a.size ≤ i) : tail a i = 0 := by
  simp [tail, valueList, List.drop_eq_nil_of_le (show a.toList.length ≤ i by simpa using h)]

theorem limb_toNat (a : Limbs) (i : Nat) : (limb a i).toNat = digit a i := by
  simp [limb, digit]

/-! ## Addition -/

theorem addLoop_value (a b : Limbs) (n i : Nat) (carry : UInt64) (r : Limbs)
    (ha : a.size ≤ n) (hb : b.size ≤ n) (hc : carry.toNat ≤ 1) :
    value (addLoop a b n i carry r) = value r + B ^ r.size * (carry.toNat + tail a i + tail b i) := by
  fun_induction addLoop a b n i carry r with
  | case1 i carry r h t ih =>
    have la := digit_lt a i; have lb := digit_lt b i
    have ht : t.toNat = digit a i + digit b i + carry.toNat := by
      simp only [t, UInt64.toNat_add, limb_toNat]; omega
    have hhigh : (t >>> 32).toNat = t.toNat / B := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    rw [ih (by rw [hhigh]; omega), value_push, Array.size_push, Nat.pow_succ, hhigh, hlow,
      tail_step a i, tail_step b i, Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add]
    congr 2
    omega
  | case2 i carry r h =>
    have hlow : carry.toUInt32.toNat = carry.toNat := by
      simp only [UInt64.toNat_toUInt32]; omega
    rw [value_push, hlow, tail_of_le a i (by omega), tail_of_le b i (by omega)]
    simp

/-- The limbs `add` returns are those of the sum. -/
theorem add_value (a b : Limbs) : value (add a b) = value a + value b := by
  simp only [add]
  split <;> rw [addLoop_value _ _ _ _ _ _ (by omega) (by omega) (by decide)] <;>
    simp [value, valueList, tail]

/-! ## Subtraction -/

theorem subLoop_value (a b : Limbs) (i : Nat) (borrow : UInt64) (r : Limbs)
    (hb : borrow.toNat ≤ 1) (h : tail b i + borrow.toNat ≤ tail a i) :
    value (subLoop a b i borrow r) = value r + B ^ r.size * (tail a i - tail b i - borrow.toNat) := by
  fun_induction subLoop a b i borrow r with
  | case1 i borrow r hi t ih =>
    have la := digit_lt a i; have lb := digit_lt b i
    have sa := tail_step a i; have sb := tail_step b i
    have ht : t.toNat = (digit a i + 18446744073709551616 - digit b i - borrow.toNat) % 18446744073709551616 := by
      simp only [t, UInt64.toNat_sub, limb_toNat]; omega
    have hhigh : (t >>> 63).toNat = t.toNat / 9223372036854775808 := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    rw [ih (by rw [hhigh]; omega) (by rw [hhigh]; omega), value_push, Array.size_push, Nat.pow_succ, hhigh, hlow,
      Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add]
    congr 2
    omega
  | case2 i borrow r hi =>
    have := tail_of_le a i (by omega)
    have : tail a i - tail b i - borrow.toNat = 0 := by omega
    simp [this]

/-- For `a` at least `b`, the limbs `sub` returns are those of the difference. -/
theorem sub_value (a b : Limbs) (h : value b ≤ value a) : value (sub a b) = value a - value b := by
  simp only [sub]
  rw [subLoop_value _ _ _ _ _ (by decide) (by simpa [tail_zero] using h)]
  simp [value, valueList, tail]

/-! ## Zero limbs on top -/

theorem value_pop (a : Limbs) (h : a.size ≠ 0) (top : a.getD (a.size - 1) 0 = 0) : value a.pop = value a := by
  have ne : a.toList ≠ [] := by intro e; apply h; simpa using congrArg List.length e
  have last : a.toList.getLast ne = 0 := by
    rw [List.getLast_eq_getElem]
    have hlt : a.size - 1 < a.size := by omega
    have := top
    simp [Array.getD, hlt] at this
    simpa using this
  have split := List.dropLast_concat_getLast ne
  rw [last] at split
  have := congrArg valueList split
  rw [valueList_append] at this
  simpa [value, Array.toList_pop, valueList] using this

/-- Taking the zero limbs off the top leaves the same number. -/
theorem trim_value (a : Limbs) : value (trim a) = value a := by
  fun_induction trim a with
  | case1 a h => rfl
  | case2 a h top ih => rw [ih, value_pop a h (by simpa using top)]
  | case3 a h top => rfl

/-! ## Writing a limb -/

theorem value_set (r : Limbs) (k : Nat) (v : UInt32) (h : k < r.size) :
    value (r.setIfInBounds k v) + B ^ k * digit r k = value r + B ^ k * v.toNat := by
  have hk : k < r.toList.length := by simpa using h
  have before : r.toList = r.toList.take k ++ r[k] :: r.toList.drop (k + 1) := by
    conv => lhs; rw [← List.take_append_drop k r.toList, List.drop_eq_getElem_cons hk]
    simp
  have after : (r.setIfInBounds k v).toList = r.toList.take k ++ v :: r.toList.drop (k + 1) := by
    simp [Array.toList_setIfInBounds, List.set_eq_take_append_cons_drop]
    intro hle; omega
  have len : (r.toList.take k).length = k := by simp; omega
  have d : digit r k = r[k].toNat := by simp [digit, Array.getD, h]
  rw [value, after, valueList_append, len, d]
  conv => rhs; rw [value, before, valueList_append, len]
  simp only [valueList]
  generalize valueList (r.toList.take k) = low
  generalize valueList (r.toList.drop (k + 1)) = high
  generalize B ^ k = P
  rw [Nat.mul_add, Nat.mul_add]
  omega

theorem digit_set_ne (r : Limbs) (k m : Nat) (v : UInt32) (h : m ≠ k) :
    digit (r.setIfInBounds k v) m = digit r m := by
  simp [digit, Array.getD_eq_getD_getElem?, Array.getElem?_setIfInBounds_ne (Ne.symm h)]

/-! ## Multiplication by one limb, and decimal literals -/

theorem scaleLoop_value (a : Limbs) (m : UInt64) (i : Nat) (carry : UInt64) (r : Limbs)
    (hm : m.toNat < B) (hc : carry.toNat < B) :
    value (scaleLoop a m i carry r) = value r + B ^ r.size * (carry.toNat + m.toNat * tail a i) := by
  fun_induction scaleLoop a m i carry r with
  | case1 i carry r h t ih =>
    have la := digit_lt a i
    have bound : digit a i * m.toNat ≤ 4294967295 * 4294967295 := Nat.mul_le_mul (by omega) (by omega)
    have ht : t.toNat = digit a i * m.toNat + carry.toNat := by
      simp only [t, UInt64.toNat_add, UInt64.toNat_mul, limb_toNat]; omega
    have hhigh : (t >>> 32).toNat = t.toNat / B := by
      simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]
    have hlow : t.toUInt32.toNat = t.toNat % B := by simp
    rw [ih (by rw [hhigh]; omega), value_push, Array.size_push, Nat.pow_succ, hhigh, hlow,
      tail_step a i, Nat.add_assoc, Nat.mul_assoc, ← Nat.mul_add, Nat.mul_add m.toNat, Nat.mul_left_comm m.toNat,
      Nat.mul_comm m.toNat (digit a i)]
    congr 2
    generalize m.toNat * tail a (i + 1) = rest
    omega
  | case2 i carry r h =>
    have hlow : carry.toUInt32.toNat = carry.toNat := by
      simp only [UInt64.toNat_toUInt32]; omega
    rw [value_push, hlow, tail_of_le a i (by omega)]
    simp

/-- One more digit of a decimal literal. -/
theorem decimal_value (a : Limbs) (d : UInt32) : value (decimal a d) = value a * 10 + d.toNat := by
  have hd := d.toNat_lt
  rw [decimal, trim_value, scaleLoop_value _ _ _ _ _ (by decide) (by simpa using hd)]
  simp [value, valueList, tail_zero, Nat.mul_comm, Nat.add_comm]

end Runtime.Big
