/-! # `Nat.powMod`, for the minimal runtime

Lean compiles `Nat.powMod` to a call of its runtime's `lean_nat_powmod`, which the minimal runtime does not
have. Jaune's MODEXP precompile is the one caller here. This is that function in Lean, by squaring and
multiplying over the runtime's own multiplication and remainder; `rt/names.c` gives it the name compiled
Lean asks for. On Lean's own runtime it is linked and never called.

Not constant time, like everything on `Nat`. -/

namespace Evm

/-- `b ^ e % m`, and `b ^ e` when `m = 0`, as `Nat.powMod` has it (`n % 0 = n` does the second case with no
test for it). One round for each bit of `e`. -/
@[export evm_nat_powmod]
def powMod (b e m : Nat) : Nat := Id.run do
  let mut result := 1 % m
  let mut base := b % m
  let mut exp := e
  for _ in [0 : e.log2 + 1] do
    if exp % 2 == 1 then result := result * base % m
    base := base * base % m
    exp := exp / 2
  return result

end Evm
