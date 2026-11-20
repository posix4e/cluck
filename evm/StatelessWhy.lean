import Evm

/-! For whoever is making witnesses: the response to a stateless request with its status in words, and
Jaune's own reason when the block was rejected. Never in an image.

    .lake/build/bin/stateless-why block.req -/

def main (args : List String) : IO UInt32 := do
  let [path] := args | do IO.eprintln "usage: stateless-why REQUEST"; return 2
  let bytes ← IO.FS.readBinFile path
  let some (request, pos) := (Evm.Stateless.request bytes).run 0 | do IO.println "not a stateless request"; return 1
  if pos != bytes.size then IO.println "bytes after the request"; return 1
  -- What the witness amounts to, before anything is run on it.
  if let some parent := request.headers.getLast?.bind Evm.Stateless.header then
    let store := Evm.Trie.Store.ofNodes request.nodes
    IO.println s!"{request.nodes.size} nodes, {request.codes.length} codes, {request.keys.length} keys, \
      {request.headers.length} headers; the parent's state root is \
      {if store.contains parent.stateRoot then "among the nodes" else "NOT among the nodes"}"
    match Evm.Stateless.materialise request parent.stateRoot with
    | .ok known => IO.println s!"{known.leaves.size} accounts supplied in full"
    | .error (.lacking hash _) => IO.println s!"the witness lacks {hash}"
    | .error _ => IO.println "the witness does not read"
  let started ← IO.monoMsNow
  let (response, reason) := Evm.Stateless.runWithReason request
  let words := match response.status with
    | 0 => "valid"
    | 3 => "invalid"
    | 4 => "the import failed"
    | 5 => "malformed request"
    | 6 => "the witness falls short"
    | 7 => "the witness is malformed"
    | 8 => "rejected while running, unverified"
    | _ => "unknown"
  IO.println s!"status {response.status}: {words}"
  IO.println s!"hash {response.tip}"
  IO.println s!"root {response.root}"
  if reason != "" then IO.println s!"reason: {reason}"
  IO.println s!"{(← IO.monoMsNow) - started} ms"
  return if response.status == 0 then 0 else 1
