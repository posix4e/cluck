import Evm

/-! For whoever is making requests to build: what became of each transaction proposed, in the order they
were tried. One that went in is shown with the gas the block had used once it had run, which is what a
node's own account of the block can be laid beside; one left out, with why. It says how long the block
took, and how long it takes handed who signed each transaction (`Build.Signers`). Never in an image.

    .lake/build/bin/build-why build.req
    .lake/build/bin/build-why --each DIR

The second is for where a round's time goes. DIR holds requests for a bid as the feeder sent them, one
after another (`builder/shadow` writes them when told to), and they are built in the order of their
names with what the ones before gave kept, as the machine keeps it. For each: the milliseconds of
reading it with what is kept (`Kept.take`), of everything before the first transaction
(`beginKeeping`: the headers, who signed what is proposed, the block opened), of the transactions,
and of ending the block (`FastJob.finish`: the roots and the header). Then parts of those done once
more by themselves: the headers decoded and checked to be a chain, which a request read with what is
kept pays only for the headers it brings, and any other pays whole inside "before the first";
and of the ending, what closes the block, the state root, the receipts' root and bloom, and the
transactions' root. No clock cuts a block short here, and nothing is signed: signing a bid is the same
work every time (`bls-test` times it). -/

open Jaune Evm Evm.Service Evm.Stateless in
/-- Parts of a block's ending, each done by itself on the block as it stood after its last transaction:
milliseconds of closing it, of the state root, of the receipts' root and bloom, of the transactions'
root. -/
def endingParts (job : Evm.Build.FastJob) : IO (Array Nat) := do
  let t0 ← IO.monoMsNow
  let closed ← IO.lazyPure fun _ => Fast.closeBlock job.blk job.host job.body job.out
  let t1 ← IO.monoMsNow
  let .ok out := closed | return #[t1 - t0, 0, 0, 0]
  let root ← IO.lazyPure fun _ => (Evm.Bridge.rootAfter job.witness out.world).toOption
  let t2 ← IO.monoMsNow
  let receipts ← IO.lazyPure fun _ => Evm.Bridge.receiptsRootAndBloom out.receipts
  let t3 ← IO.monoMsNow
  let transactions ← IO.lazyPure fun _ =>
    getTransactionsRoot { BlockOutput.init with
      transactionsTrie := job.taken.toList.zipIdx.foldl (fun trie (tx, index) =>
        trie.insert (Rlp.Item.bytes index.toBytes).toBytes tx) BlockOutput.init.transactionsTrie }
  let t4 ← IO.monoMsNow
  -- Used, so that none of it is left undone.
  if root.isNone || receipts.2.length == 0 || transactions == 0 then IO.print ""
  return #[t1 - t0, t2 - t1, t3 - t2, t4 - t3]

open Jaune Evm Evm.Service Evm.Stateless in
/-- Milliseconds of decoding a request's headers and checking that each names the one before it. -/
def headersAlone (r : Evm.Build.Request) : IO Nat := do
  let t0 ← IO.monoMsNow
  let linked ← IO.lazyPure fun _ =>
    match r.witness.headers.mapM Stateless.header with
    | none => false
    | some ancestors => (ancestors.zip (ancestors.drop 1)).all fun (a, b) => a.hash == b.parentHash
  let t1 ← IO.monoMsNow
  if !linked then IO.print ""
  return t1 - t0

/-- The requests of `dir` built one after another, with the time of each part. -/
def each (dir : String) : IO UInt32 := do
  let paths : Array String := ((← System.FilePath.readDir dir).map fun entry => entry.path.toString).qsort fun a b => a < b
  let mut kept : Evm.Build.Kept := {}
  let mut sums : Array Nat := #[0, 0, 0, 0, 0, 0, 0, 0, 0]
  let mut count := 0
  IO.println "bytes proposed in status | ms: read, before the first, transactions, ending | again: headers; closing, state root, receipts, transactions' root"
  for path in paths do
    let bytes ← IO.FS.readBinFile path
    -- A request for a bid: its kind, the slot, the proposer's key, the fork's version and the time
    -- allowed, 69 bytes, and then the request to build (`Bid.buildWith`).
    let some (request, _) := (Evm.Build.request (bytes.extract 69 bytes.size)).run 0
      | do IO.println s!"{path}: not a request to build"; continue
    let before := kept
    kept := {}
    let t0 ← IO.monoMsNow
    let (request, held) ← IO.lazyPure fun _ => before.take { request with work := Evm.Build.txWork }
    let t1 ← IO.monoMsNow
    let (stage, signers) ← IO.lazyPure fun _ => Evm.Build.beginKeeping request Evm.Build.noOther
    let proposed := stage.left - 1
    let t2 ← IO.monoMsNow
    let mut stage := stage
    while stage.filling do
      stage ← IO.lazyPure fun _ => stage.step
    let ran := (← IO.monoMsNow) - t2
    let parts ← match stage with
      | .goingFast job => endingParts job
      | _ => pure #[0, 0, 0, 0]
    let headers ← headersAlone request
    let t3 ← IO.monoMsNow
    let (response, _, why) ← IO.lazyPure fun _ => stage.step.answer
    let t4 ← IO.monoMsNow
    kept := if request.seen.isSome then { held with signers } else held
    let went := match response.built with
      | some built => built.included.length
      | none => 0
    IO.println s!"{bytes.size} {proposed} {went} {response.status}{if why == "" then "" else " (" ++ why ++ ")"} | {t1 - t0} {t2 - t1} {ran} {t4 - t3} | {headers}; {parts[0]!} {parts[1]!} {parts[2]!} {parts[3]!}"
    if response.status == 0 then
      sums := (#[t1 - t0, t2 - t1, ran, t4 - t3, headers] ++ parts).zipWith (· + ·) sums
      count := count + 1
  if count != 0 then
    let mean := sums.map (· / count)
    IO.println s!"{count} built; on average ms: read {mean[0]!}, before the first {mean[1]!}, transactions {mean[2]!}, ending {mean[3]!}; again: headers {mean[4]!}; closing {mean[5]!}, state root {mean[6]!}, receipts {mean[7]!}, transactions' root {mean[8]!}"
  return 0

def main (args : List String) : IO UInt32 := do
  if let ["--each", dir] := args then return ← each dir
  let [path] := args | do IO.eprintln "usage: build-why REQUEST | build-why --each DIR"; return 2
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
