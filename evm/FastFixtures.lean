import Jaune.T8n
import Jaune.FixtureTransition
import Evm

/-! Ethereum's own tests of chains, put to the fast engine.

    .lake/build/bin/fast-fixtures FILE...        blockchain-test fixtures (execution-spec-tests' JSON)

A fixture is a starting state and a chain of blocks, some of which must be accepted and some refused. For
each block a witness is cut from the whole state as it then stands and the block is put to the engine as
the stateless request the service would be sent (`Evm.Engine`). **The fixture is the judge**: a block it
does not mark must be answered valid, with its hash; a block it marks with `expectException` must not be;
and the last block accepted must be the one the fixture names. Jaune imports each block too, the ordinary
way with the whole state, which is where the state for the next block comes from, and where the two
disagree it is said.

A block of a fork the engine has no rules for (anything before Prague, which the suites of fork changes
begin in) is left to Jaune and counted as such. One line is printed for each file: PASS, or FAIL and what
failed. Runs on Lean's runtime: it reads JSON, and Jaune is beside it. -/
open Jaune Evm

/-- How one file went. -/
structure Tally where
  cases : Nat := 0
  accepted : Nat := 0
  /-- Blocks the fixture says must be refused and the engine did, by the status it gave. -/
  refused : Std.HashMap UInt8 Nat := {}
  /-- Blocks of a fork the engine has no rules for. -/
  notOurs : Nat := 0
  failures : List String := []

def Tally.fail (t : Tally) (what : String) : Tally := { t with failures := what :: t.failures }

/-- Whether a block of a fixture is one that must be refused. -/
def mustBeRefused (block : Lean.Json) : Bool :=
  match block with
  | .obj fields => fields.toArray.any fun (key, _) => key.startsWith "expectException"
  | _ => false

def oneCase (name : String) (case : Lean.Json) (tally : Tally) : IO Tally := do
  let mut tally := { tally with cases := tally.cases + 1 }
  let network ← case.find "network" >>= Lean.Json.toIoString
  let some (.scheduled spec) := FixtureNetwork.ofString? network
    | return tally.fail s!"{name}: a network this runner does not know, {network}"
  let chainId : UInt64 ← match (case.find? "config").bind (·.find? "chainid") with
    | some id => (·.toUInt64) <$> id.toIoHexNat
    | none => pure 1
  let genesisFork := (FixtureNetwork.scheduled spec).genesisFork
  let .ok genesisRules := genesisFork.rules | return tally.fail s!"{name}: no rules for the genesis fork"
  -- The fork a block is of: the suite's, or for a suite of a fork change, the one its time falls in.
  let forkAt (number time : Nat) : Option Fork :=
    match spec with
    | .static fork => some fork
    | .transition change => ((change.chainConfig chainId).forkAt number time).toOption
  let pre ← (← case.find "pre").toWorldAt genesisRules
  let genesisBytes ← case.find "genesisRLP" >>= Lean.Json.toIoBytes
  let .ok (genesis, _) := rlpToBlockEAt genesisRules genesisBytes
    | return tally.fail s!"{name}: the genesis block does not decode"
  let mut chain : BlockChain := { blocks := [genesis], state := pre, chainId }
  let blocks ← case.find "blocks" >>= Lean.Json.toIoList
  let mut index := 0
  for block in blocks do
    index := index + 1
    let bytes ← block.find "rlp" >>= Lean.Json.toIoBytes
    let refuse := mustBeRefused block
    let decoded := (rlpToBlockE bytes).toOption
    let some tip := chain.blocks.getLast? | return tally.fail s!"{name}: an empty chain"
    -- A block that does not decode has no time to choose a fork by: it is put under its parent's.
    let fork := (match decoded with
      | some (b, _) => forkAt b.header.number b.header.timestamp
      | none => forkAt tip.header.number tip.header.timestamp).getD genesisFork
    -- Jaune, with the whole state: the next state, and a second opinion.
    let imported : Except String (BlockChain ⊕ String) :=
      match spec with
      | .static fork => addBlockToChainAt fork chain bytes
      | .transition change =>
        match addBlockToChainUsingE (change.chainConfig chainId) chain bytes with
        | .ok (.inl next) => .ok (.inl next)
        | .ok (.inr _) => .ok (.inr "rejected")
        | .error _ => .error "the import failed"
    let jauneAccepts := match imported with | .ok (.inl _) => true | _ => false
    if jauneAccepts == refuse then
      tally := tally.fail s!"{name}: block {index}: Jaune {if jauneAccepts then "accepts" else "refuses"} it and the \
        fixture says it must be {if refuse then "refused" else "accepted"}"
    if !Bridge.supported fork then
      tally := { tally with notOurs := tally.notOurs + 1 }
    else
      let .ok witness := Cut.witnessOf chain.state
        | return tally.fail s!"{name}: block {index}: no witness could be cut"
      let request : Stateless.Request :=
        { fork := some fork, chainId, block := bytes.toByteArray, headers := chain.blocks.map fun b => Cut.headerBytes b.header,
          nodes := witness.nodes, codes := witness.codes, keys := [] }
      let (answer, reason) := Engine.runWithReason request
      if refuse then
        -- Refused is a verdict that the block is invalid (3) or that it is no block at all (5). A block
        -- that does not follow the chain's last one is turned away before the engine sees it, as too few
        -- or the wrong headers (5 or 6). Anything else is the engine failing to judge.
        let orphan := match decoded with
          | some (b, _) => b.header.parentHash != tip.header.hash || b.header.number != tip.header.number + 1
          | none => false
        if answer.status == 3 || answer.status == 5 || (orphan && answer.status == 6) then
          tally := { tally with refused := tally.refused.insert answer.status (tally.refused.getD answer.status 0 + 1) }
        else
          tally := tally.fail s!"{name}: block {index}: must be refused, and the engine answered status {answer.status} {reason}"
      else
        match decoded with
        | none => tally := tally.fail s!"{name}: block {index}: must be accepted, and does not decode"
        | some (b, hash) =>
          if answer.status == 0 && answer.tip == hash && answer.root == b.header.stateRoot then
            tally := { tally with accepted := tally.accepted + 1 }
          else
            tally := tally.fail s!"{name}: block {index}: must be accepted, and the engine answered status {answer.status} {reason}"
    if let .ok (.inl next) := imported then chain := next
  -- The chain ends where the fixture says.
  let last ← case.find "lastblockhash" >>= Lean.Json.toIoU256
  if (chain.blocks.getLast?.map (·.header.hash)) != some last then
    tally := tally.fail s!"{name}: the chain does not end at the fixture's last block"
  return tally

def oneFile (path : String) : IO Bool := do
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let cases ← json.toIoRBNode
  let mut tally : Tally := {}
  for (name, case) in cases.toArray.toList do
    tally ← try oneCase name case tally catch e => pure (tally.fail s!"{name}: {e}")
  let refused := tally.refused.fold (fun n _ count => n + count) 0
  let how := ", ".intercalate (tally.refused.toList.map fun (status, count) => s!"{count} as {status.toNat}")
  let counts := s!"{tally.cases} cases, {tally.accepted} blocks accepted, {refused} refused{if refused > 0 then s!" ({how})" else ""}\
    {if tally.notOurs > 0 then s!", {tally.notOurs} of a fork the engine has no rules for" else ""}"
  if tally.failures.isEmpty then
    IO.println s!"PASS\t{path}\t{counts}"
    return true
  else
    IO.println s!"FAIL\t{path}\t{counts}, {tally.failures.length} failures"
    for what in tally.failures.reverse.take 5 do IO.println s!"\t{what.take 600}"
    return false

def main (args : List String) : IO UInt32 := do
  if args.isEmpty then
    IO.eprintln "usage: fast-fixtures FILE..."
    return 2
  let mut good := 0
  for path in args do
    if ← oneFile path then good := good + 1
  return if good == args.length then 0 else 1
