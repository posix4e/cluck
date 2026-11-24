import Kernel.Efi
import Kernel.Hw

/-! A quote of a report, asked of the host from inside the trust domain.

A report (`Efi.report`) can be checked only on the machine that made it. A quote is that report signed
by the platform's quoting enclave with a key Intel vouches for, and can be checked anywhere. Where the
guest's operator runs the host, the host turns reports into quotes with a service of its own; where it
does not, as on a cloud, the guest asks: it puts the report in memory the host can see and tells the
host where (TDG.VP.VMCALL<GetQuote>, in the Guest-Host Communication Interface), and the host writes the
quote there when it has one.

The memory is a run of the arena shared with the claimed device (`Kernel/Hw.lean`), taken once by
whoever uses this and handed in each time. At its start, least significant byte first: a version (1), a
status the host writes, the length of what is asked (a report: 1,024), the length of what is answered;
then the report, which the answer replaces.

Everything read back is the host's word, and treated as that: the status is read until two readings
agree, the length is cut to the room there is, and the quote is bytes for whoever asked to have checked
by someone else. A host can refuse, be slow, or write nonsense; it cannot make a quote that verifies
for a report this machine did not make, and what it is given, a report, it could be given by anyone
(reports are not secret, and only a trust domain on this machine can have made one that the quoting
enclave will sign).

There are no interrupts here, so the status is looked at until it changes or a time is up. A request
the host never finished leaves the memory the host's to write whenever it likes: `ask` then says so, and
whoever holds that memory must not use it again. -/

namespace Kernel.Quote

/-- How much shared memory a request takes: the header, and room for a quote several times the size
any has been. -/
def room : USize := 32768

private def le (n : UInt64) (bytes : Nat) : ByteArray :=
  ByteArray.mk ((Array.range bytes).map fun i => (n >>> (8 * i).toUInt64).toUInt8)

private def read (b : ByteArray) (at_ bytes : Nat) : UInt64 :=
  (List.range bytes).foldl (fun n i => n ||| (b[at_ + i]!.toUInt64 <<< (8 * i).toUInt64)) 0

inductive Outcome where
  | quote (bytes : ByteArray)
  /-- The host refused or failed, and said so: the memory can be used again. -/
  | refused (why : String)
  /-- The host took the request and never finished it: the memory is its to write from now on. -/
  | lost

/-- The status the host has written, read until two readings agree. -/
private def status (at_ : UInt64) : BaseIO UInt64 := do
  let mut a := read (← Hw.load (at_ + 8) 8) 0 8
  for _ in [0:8] do
    let b := read (← Hw.load (at_ + 8) 8) 0 8
    if a == b then break
    a := b
  return a

/-- A quote of `report`, which must be 1,024 bytes, asked for through the `room` bytes of shared memory
at `at_`, waited for up to `patience` milliseconds of `clock`. -/
def ask (at_ : UInt64) (report : ByteArray) (clock : BaseIO UInt64) (patience : UInt64 := 5000) : BaseIO Outcome := do
  if report.size != 1024 then return .refused "not a report"
  if at_ == 0 then return .refused "no memory the host can see"
  let inFlight : UInt64 := 0xffffffffffffffff
  Hw.store at_ (le 1 8 ++ le 0 8 ++ le 1024 4 ++ le 0 4 ++ report)
  let said ← Efi.quoteAsk at_ room.toUInt64
  if said != 0 then return .refused s!"the host would not take the request ({said})"
  let length : BaseIO USize := do return (read (← Hw.load (at_ + 16) 8) 4 4).toUSize
  let began ← clock
  let mut now := began
  let mut state ← status at_
  let mut size ← length
  -- A host that is at it says so in the status. One that has finished says nothing is wrong and how
  -- long its answer is; nothing wrong and no length is taken for a host that has not begun.
  while (state == inFlight || (state == 0 && size == 0)) && now - began < patience do
    for _ in [0:2000] do Hw.pause
    now ← clock
    state ← status at_
    size ← length
  if state == inFlight || (state == 0 && size == 0) then return .lost
  if state != 0 then return .refused s!"the host could not make the quote ({state})"
  if size > room - 24 then return .refused s!"the host's answer is {size} bytes long"
  return .quote (← Hw.load (at_ + 24) size)

end Kernel.Quote
