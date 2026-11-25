import Platform
import Runtime.Big
import Runtime.Utf8

/-! A machine that does nothing but use up its stack: for trying the hole under it (`scripts/stack-check`).

`down` calls itself and has something left to do when the call comes back, so each call keeps a frame.
First it goes a million deep and comes back, which the stack has room for; then it goes down without end.
What the console must show is in `scripts/stack-check`. -/

@[noinline] partial def down (left : UInt64) : IO UInt64 := do
  if left == 0 then return 0
  let below ← down (left - 1)
  return below + 1

def main : IO UInt32 := do
  Platform.write s!"stack-test: a million deep and back: {← down 1000000}\n".toUTF8
  Platform.write "stack-test: now down without end\n".toUTF8
  let never ← down 0xffffffffffffffff
  Platform.write s!"stack-test: it came back, which it must not ({never})\n".toUTF8
  return 1
