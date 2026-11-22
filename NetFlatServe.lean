import Kernel.Net.Flat

/-! The trial TCP (`Kernel/Net/Flat.lean`) as a process that somebody else brings frames to, for trying it
against a real TCP (`scripts/flat-linux-test`). On standard input: two bytes of length, then a frame of
that length; a length of nothing means only that time has passed. On standard output, the same way, the
frames it sends. Its address is 10.0.0.2, its port 80.

    .lake/build/bin/net-flat-serve [request bytes] [answer bytes] [linger ms] -/

open Kernel.Net.Flat

def main (args : List String) : IO UInt32 := do
  let number (i : Nat) (otherwise : Nat) : Nat := (args[i]?.bind String.toNat?).getD otherwise
  let cfg : Tuning := { slotBits := 16, request := (number 0 100).toUInt32, linger := (number 2 0).toUInt32 }
  let answer := ByteArray.mk (Array.range (number 1 128) |>.map fun i => (i % 251).toUInt8)
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  let mut t := table cfg
  let mut tx := outbox (1 <<< 22)
  let began ← IO.monoMsNow
  let mut last : UInt32 := 0
  repeat
    let head ← stdin.read 2
    if head.size < 2 then break
    let n := head[0]!.toNat * 256 + head[1]!.toNat
    let now : UInt32 := ((← IO.monoMsNow) - began).toUInt32 + ((1 : UInt32) <<< 20)
    if n == 0 then
      (t, tx) := tick cfg answer now (if last == 0 then 1 else now - last) t (st64 tx 0 8)
      last := now
    else
      let frame ← stdin.read n.toUSize
      if frame.size < n then break
      let rx := head ++ frame
      (t, tx) := process cfg answer now rx rx.usize t tx
    let stop := (written tx).toNat
    if stop > 8 then
      stdout.write (tx.extract 8 stop)
      stdout.flush
  IO.eprintln s!"net-flat-serve: live {ld64 t 0}, accepted {ld64 t 8}, closed {ld64 t 16}, SYNs {ld64 t 24}, dropped {ld64 t 32}, out of order {ld64 t 40}, resets taken {ld64 t 48}, no room {ld64 t 56}, sent again {ld64 t 72}, timed out {ld64 t 80}, resets sent {ld64 t 88}"
  return 0
