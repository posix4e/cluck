import Mini.Print
import Mini.Alloc

/-! Prints the C that the programs in `Mini/` stand for: `mini-print alloc > rt/alloc.c`. -/

def main (arguments : List String) : IO UInt32 := do
  match arguments with
  | ["alloc"] => IO.print (Mini.Alloc.program.c "Mini/Alloc.lean"); return 0
  | _ => IO.eprintln "usage: mini-print alloc"; return 2
