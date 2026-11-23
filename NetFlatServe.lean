import Kernel.Net.Flat

/-! The trial TCP (`Kernel/Net/Flat.lean`) as a process that somebody else brings frames to, for trying it
against a real TCP (`scripts/flat-linux-test`). On standard input: two bytes of length, then a frame of
that length; a length of nothing means only that time has passed. On standard output, the same way, the
frames it sends. Its address is 10.0.0.2, its port 80.

    .lake/build/bin/net-flat-serve [request bytes] [answer bytes] [linger ms]
    .lake/build/bin/net-flat-serve http [bytes of /big] [0 not to measure round trips]

The first answers every connection alike, once so many bytes have come. The second is a small web
server: `GET /` gets a page, `GET /big` so many bytes, anything else is not found. The request's first
line must come in one segment. -/

open Kernel.Net.Flat

def page (status : String) (body : ByteArray) : ByteArray :=
  s!"HTTP/1.1 {status}\r\nContent-Type: text/plain\r\nContent-Length: {body.size}\r\nConnection: close\r\n\r\n".toUTF8 ++ body

/-- Whether the bytes of `rx` from `at_` begin with `text`. -/
def begins (rx : ByteArray) (at_ length : USize) (text : String) : Bool :=
  let want := text.toUTF8
  want.usize ≤ length && (List.range want.size).all fun i => rd8 rx (at_ + i.toUSize) == want[i]!

def main (args : List String) : IO UInt32 := do
  let web := args.head? == some "http"
  let number (i : Nat) (otherwise : Nat) : Nat := (args[i]?.bind String.toNat?).getD otherwise
  let cfg : Tuning := { slotBits := 16, linger := if web then 0 else (number 2 0).toUInt32, measures := !web || number 2 1 != 0 }
  let pattern (n : Nat) : ByteArray := ByteArray.mk (Array.range n |>.map fun i => (i % 251).toUInt8)
  let answers : Array ByteArray :=
    if web then #[page "200 OK" "a TCP written in Lean\n".toUTF8, page "200 OK" (pattern (number 1 1000000)), page "404 Not Found" "nothing here\n".toUTF8]
    else #[pattern (number 1 128)]
  let wanted := (number 0 100).toUInt32
  let respond (rx : ByteArray) (at_ length : USize) (had : UInt32) : UInt64 :=
    if web then
      if begins rx at_ length "GET / " then send 0 0
      else if begins rx at_ length "GET /big " then send 1 0
      else send 2 0
    else
      let got := had + length.toUInt32
      if got ≥ wanted then send 0 got else more got
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
      (t, tx) := tick cfg answers now (if last == 0 then 1 else now - last) t (st64 tx 0 8)
      last := now
    else
      let frame ← stdin.read n.toUSize
      if frame.size < n then break
      let rx := head ++ frame
      (t, tx) := process cfg answers respond now rx rx.usize t tx
    let stop := (written tx).toNat
    if stop > 8 then
      stdout.write (tx.extract 8 stop)
      stdout.flush
  IO.eprintln s!"net-flat-serve: live {ld64 t 0}, accepted {ld64 t 8}, closed {ld64 t 16}, SYNs {ld64 t 24}, dropped {ld64 t 32}, out of order {ld64 t 40}, resets taken {ld64 t 48}, no room {ld64 t 56}, sent again {ld64 t 72}, timed out {ld64 t 80}, resets sent {ld64 t 88}, sent again on repeats {ld64 t 96}, held back {ld64 t 104}, round trips measured {ld64 t 120}"
  return 0
