import SelfTest
import Platform

/-! # The self-test's transcript, printed

Linked once against Lean's own runtime (`rt-test`) and once against the minimal runtime (`rt-test-min`); the
two outputs must be byte for byte the same. -/

def main : IO UInt32 := do
  Platform.write SelfTest.transcript
  return 0
