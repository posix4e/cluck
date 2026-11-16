import Mini.AllocProofs

/-! # A heap that is in order

The theorems in `Mini/AllocProofs.lean` say what one call does to a state. This says what a state has to be
for calls to go on being safe, and shows that a call leaves it that way: the blocks handed out so far lie
one after another from where the heap began, each behind sixteen bytes that hold its class and whether it
is in use, and none of them shares a byte with another. -/

namespace Mini.Alloc

/-- A block that has been handed out at some time: where it is and the class it was cut for. -/
structure Block where
  address : UInt64
  size_class : UInt64

/-- How many bytes a block of a small class holds. -/
def Block.bytes (b : Block) : Nat := b.size_class.toNat * 16

/-- The blocks lie one after another from byte `start` to byte `finish`, each behind its header, and the
header of each says its class and one of the two states. -/
def Laid (memory : UInt64 → Option UInt8) : Nat → List Block → Nat → Prop
  | start, [], finish => start = finish
  | start, b :: rest, finish =>
    b.address.toNat = start + 16 ∧ 1 ≤ b.size_class.toNat ∧ b.size_class.toNat < 257 ∧
    readBytes memory (b.address - 16) 8 = .ok b.size_class ∧
    (readBytes memory (b.address - 16 + 8) 8 = .ok (UInt64.ofNat inUse) ∨
      readBytes memory (b.address - 16 + 8) 8 = .ok (UInt64.ofNat freed)) ∧
    Laid memory (start + 16 + b.bytes) rest finish

theorem Laid.le {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    (h : Laid memory start blocks finish) : start ≤ finish := by
  induction blocks generalizing start with
  | nil => exact Nat.le_of_eq h
  | cons b rest ih => have := ih h.2.2.2.2.2; omega

/-- A word written at or after byte `to` shares no byte with a word that ends at or before it. -/
theorem below_apart (x start : UInt64) (h : x.toNat + 8 ≤ start.toNat) (i : Nat) (hi : i < 8) (k : Nat) (hk : k < 8)
    (room : start.toNat + 8 ≤ 18446744073709551616) : start + UInt64.ofNat k ≠ x + UInt64.ofNat i := by
  intro e
  have := congrArg UInt64.toNat e
  simp only [UInt64.toNat_add, UInt64.toNat_ofNat'] at this
  omega

/-- Writing a word beyond the last block leaves the blocks as they were. -/
theorem Laid.frame {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    (h : Laid memory start blocks finish) (at_ word : UInt64) (beyond : finish ≤ at_.toNat)
    (room : at_.toNat + 8 ≤ 18446744073709551616) :
    Laid (writeBytes memory at_ word 8) start blocks finish := by
  induction blocks generalizing start with
  | nil => exact h
  | cons b rest ih =>
    obtain ⟨where_, low, high, hclass, hstate, hrest⟩ := h
    have order := hrest.le
    have header : (b.address - 16).toNat = start := by
      simp only [UInt64.toNat_sub, show (16 : UInt64).toNat = 16 from rfl]; have := b.address.toNat_lt; omega
    have second : (b.address - 16 + 8).toNat = start + 8 := by
      simp only [UInt64.toNat_add, header, show (8 : UInt64).toNat = 8 from rfl]; have := b.address.toNat_lt; omega
    have keep1 : readBytes (writeBytes memory at_ word 8) (b.address - 16) 8 = readBytes memory (b.address - 16) 8 :=
      readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => below_apart _ _ (by simp only [Block.bytes] at order; omega) i hi k hk room)
    have keep2 : readBytes (writeBytes memory at_ word 8) (b.address - 16 + 8) 8 =
        readBytes memory (b.address - 16 + 8) 8 :=
      readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => below_apart _ _ (by simp only [Block.bytes] at order; omega) i hi k hk room)
    exact ⟨where_, low, high, by rw [keep1]; exact hclass, by rw [keep2]; exact hstate, ih hrest⟩

/-- One more block on the end. -/
theorem Laid.append {memory : UInt64 → Option UInt8} {start finish : Nat} {blocks : List Block}
    (h : Laid memory start blocks finish) (b : Block) (last : Laid memory finish [b] (finish + 16 + b.bytes)) :
    Laid memory start (blocks ++ [b]) (finish + 16 + b.bytes) := by
  induction blocks generalizing start with
  | nil => rw [show start = finish from h]; exact last
  | cons first rest ih =>
    obtain ⟨where_, low, high, hclass, hstate, hrest⟩ := h
    exact ⟨where_, low, high, hclass, hstate, ih hrest⟩

/-- A heap in order: the blocks handed out so far are laid from `base` to the front of the heap, and the
front has not passed the end. -/
def InOrder (s : State) (base : Nat) (blocks : List Block) : Prop :=
  Laid s.memory base blocks (s.globals "heap_at").toNat ∧
    (s.globals "heap_at").toNat ≤ (s.globals "heap_end").toNat

/-- The state `malloc_fresh` shows `rt_malloc` leaves. -/
def afterFresh (s : State) (size : UInt64) : State :=
  { s with
    globals := put s.globals "heap_at" (s.globals "heap_at" + (16 + smallClass size * 16))
    memory := writeBytes (writeBytes s.memory (s.globals "heap_at") (smallClass size) 8)
      (s.globals "heap_at" + 8) (UInt64.ofNat inUse) 8 }

/-- Taking a block from fresh heap keeps the heap in order, with that block added after the others. So it
shares no byte with any block handed out before, and every header written before is as it was. -/
theorem fresh_keeps (s : State) (base : Nat) (blocks : List Block) (size : UInt64)
    (low : 1 ≤ size) (high : size ≤ 4096) (order : InOrder s base blocks)
    (room : ¬ s.globals "heap_end" - s.globals "heap_at" < 16 + smallClass size * 16) :
    InOrder (afterFresh s size) base (blocks ++ [⟨s.globals "heap_at" + 16, smallClass size⟩]) := by
  obtain ⟨laid, within⟩ := order
  have fits := smallClass_fits size low high
  have csmall : (smallClass size).toNat < 257 := by simpa [UInt64.lt_iff_toNat_lt] using fits.1
  have sized : 1 ≤ size.toNat := by simpa [UInt64.le_iff_toNat_le] using low
  have cpos : 1 ≤ (smallClass size).toNat := by
    have := fits.2.1
    simp only [UInt64.le_iff_toNat_le, UInt64.toNat_mul, show (16 : UInt64).toNat = 16 from rfl] at this
    omega
  have need : (16 + smallClass size * 16).toNat = 16 + (smallClass size).toNat * 16 := by
    simp only [UInt64.toNat_add, UInt64.toNat_mul, show (16 : UInt64).toNat = 16 from rfl]; omega
  have fitsHeap : (s.globals "heap_at").toNat + 16 + (smallClass size).toNat * 16 ≤ (s.globals "heap_end").toNat := by
    have := room
    simp only [UInt64.lt_iff_toNat_lt, UInt64.toNat_sub_of_le _ _ (by simpa [UInt64.le_iff_toNat_le] using within),
      need] at this
    omega
  have top := (s.globals "heap_end").toNat_lt
  have front : (s.globals "heap_at" + (16 + smallClass size * 16)).toNat =
      (s.globals "heap_at").toNat + 16 + (smallClass size).toNat * 16 := by
    rw [UInt64.toNat_add, need]; omega
  have second : (s.globals "heap_at" + 8).toNat = (s.globals "heap_at").toNat + 8 := by
    simp only [UInt64.toNat_add, show (8 : UInt64).toNat = 8 from rfl]; omega
  have address : (s.globals "heap_at" + 16).toNat = (s.globals "heap_at").toNat + 16 := by
    simp only [UInt64.toNat_add, show (16 : UInt64).toNat = 16 from rfl]; omega
  have back : s.globals "heap_at" + 16 - 16 = s.globals "heap_at" := UInt64.add_sub_cancel _ _
  refine ⟨?_, ?_⟩
  · simp only [afterFresh, put, ↓reduceIte, front]
    have kept := (laid.frame (s.globals "heap_at") (smallClass size) (Nat.le_refl _) (by omega)).frame
      (s.globals "heap_at" + 8) (UInt64.ofNat inUse) (by omega) (by omega)
    refine kept.append ⟨s.globals "heap_at" + 16, smallClass size⟩ ⟨address, cpos, csmall, ?_, Or.inl ?_, rfl⟩
    · show readBytes _ (s.globals "heap_at" + 16 - 16) 8 = _
      rw [back, readBytes_writeBytes_other _ _ _ _ _ _ (fun i hi k hk => state_apart _ i hi k hk)]
      exact readBytes_writeBytes_word _ _ _
    · show readBytes _ (s.globals "heap_at" + 16 - 16 + 8) 8 = _
      rw [back]
      exact readBytes_writeBytes_word _ _ _
  · simp only [afterFresh, put, ↓reduceIte, front]
    have : (if "heap_end" = "heap_at" then s.globals "heap_at" + (16 + smallClass size * 16)
        else s.globals "heap_end") = s.globals "heap_end" := by simp
    simpa [this] using fitsHeap

/-- The two together, about the program itself: on a heap in order, a small request served from fresh heap
does nothing C leaves open, returns a block, and leaves the heap in order with that block added. -/
theorem malloc_fresh_in_order (outside : Outside) (fuel : Nat) (size : UInt64) (s : State) (lists : Array UInt64)
    (base : Nat) (blocks : List Block) (low : 1 ≤ size) (high : size ≤ 4096)
    (hlists : s.arrays "free_small" = some lists)
    (hsize : (smallClass size).toNat < lists.size)
    (hempty : lists[(smallClass size).toNat]'hsize = 0)
    (asked : s.globals "heap_asked" = 1)
    (started : s.globals "heap_at" ≠ 0)
    (room : ¬ s.globals "heap_end" - s.globals "heap_at" < 16 + smallClass size * 16)
    (order : InOrder s base blocks) :
    ∃ after, program.call outside (fuel + 20) "rt_malloc" [size] s = .ok (.gave (s.globals "heap_at" + 16), after) ∧
      InOrder after base (blocks ++ [⟨s.globals "heap_at" + 16, smallClass size⟩]) :=
  ⟨afterFresh s size, malloc_fresh outside fuel size s lists low high hlists hsize hempty asked started room,
    fresh_keeps s base blocks size low high order room⟩

end Mini.Alloc
