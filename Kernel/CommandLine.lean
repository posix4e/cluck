/-! # The boot loader's command line

A line of words separated by spaces, some of them `key=value`. It comes from whoever built the image (in an
enclave it is part of what is measured), not from the parent instance, but it is still read as bytes and
nothing in it is trusted to be well-formed. Pure. -/

namespace Kernel.CommandLine

/-- The words of the line: the runs of bytes between spaces. -/
def words (line : ByteArray) : List ByteArray :=
  let (found, last) := line.foldl
    (fun (found, word) b => if b == 0x20 then (if word.isEmpty then found else word :: found, ByteArray.empty)
      else (found, word.push b))
    (([] : List ByteArray), ByteArray.empty)
  (if last.isEmpty then found else last :: found).reverse

/-- The value of the first word that is `key=value`. -/
def value? (line : ByteArray) (key : String) : Option ByteArray :=
  let prefix_ := (key ++ "=").toUTF8
  (words line).findSome? fun word =>
    if word.size ≥ prefix_.size && word.extract 0 prefix_.size == prefix_ then some (word.extract prefix_.size word.size)
    else none

/-- A number written in decimal digits and nothing else, of at most 19 digits. -/
def decimal? (digits : ByteArray) : Option Nat :=
  if digits.isEmpty || digits.size > 19 || !digits.toList.all (fun b => b ≥ 0x30 && b ≤ 0x39) then none
  else some (digits.foldl (fun n b => n * 10 + (b.toNat - 0x30)) 0)

/-- A socket address written `cid:port`. -/
def address? (text : ByteArray) : Option (UInt64 × UInt32) := do
  let colon ← (List.range text.size).find? (fun i => text[i]! == 0x3A)
  let cid ← decimal? (text.extract 0 colon)
  let port ← decimal? (text.extract (colon + 1) text.size)
  if cid < 2 ^ 64 && port < 2 ^ 32 then some (cid.toUInt64, port.toUInt32) else none

end Kernel.CommandLine
