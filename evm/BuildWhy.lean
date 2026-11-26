import Evm

/-! For whoever is making requests to build: what became of each transaction proposed, in the order they
were tried. One that went in is shown with the gas the block had used once it had run, which is what a
node's own account of the block can be laid beside; one left out, with why. It says how long the block
took, and how long it takes handed who signed each transaction (`Build.Signers`). Never in an image.

    .lake/build/bin/build-why build.req -/

def main (args : List String) : IO UInt32 := do
  let [path] := args | do IO.eprintln "usage: build-why REQUEST"; return 2
  let bytes ← IO.FS.readBinFile path
  let some (request, pos) := (Evm.Build.request bytes).run 0 | do IO.println "not a request to build"; return 1
  if pos != bytes.size then IO.println "bytes after the request"; return 1
  let started ← IO.monoMsNow
  let (response, notes, why) := Evm.Build.runWithNotes request
  IO.println s!"status {response.status}{if why == "" then "" else ": " ++ why}; {(← IO.monoMsNow) - started} ms"
  -- The same again handed who signed each transaction, as a machine that keeps that hands it on.
  let (_, signers) := Id.run (Evm.Build.runKeeping (pure false) request)
  let again ← IO.monoMsNow
  let ((kept, _, _), _) := Id.run (Evm.Build.runKeeping (pure false) { request with signers })
  IO.println s!"with its {signers.size} signers kept: status {kept.status}; {(← IO.monoMsNow) - again} ms"
  if let some built := response.built then
    IO.println s!"hash {built.hash}, {built.included.length} went in, gas used {built.header.gasUsed}, value {built.value}"
  for note in notes do
    IO.println s!"{note.place} {if note.went then "in" else "out"} {note.said}"
  return if response.status == 0 then 0 else 1
