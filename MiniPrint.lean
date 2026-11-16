import Mini.Print
import Mini.Alloc
import Mini.Free

/-! Prints the C that the programs in `Mini/` stand for: `mini-print alloc`, `mini-print free` (`scripts/print-runtime` runs both). -/

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["alloc"] => IO.print (Mini.Alloc.program.c "Mini/Alloc.lean"); return 0
  | ["free"] => IO.print (Mini.Free.program.c "Mini/Free.lean"); return 0
  | _ => IO.eprintln "usage: mini-print alloc | free"; return 2
