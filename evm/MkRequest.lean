import Jaune.T8n
import Evm

/-! Turns one case of a blockchain-test fixture into a request for the service, and into the response the
fixture says is right: its `lastblockhash`, and the root of its `postState`. The fixture is read with Jaune's
own readers, so a request holds exactly the accounts Jaune's fixture runner would start from.

    mkrequest <fixture.json> <Cancun|Prague|Osaka> <request out> <expected response out>

Runs on Lean's own runtime only. The JSON reader is part of Lean's compiler library, which is the reason the
service itself takes bytes. -/
open Jaune

def main (args : List String) : IO UInt32 := do
  let [path, network, requestPath, expectedPath] := args
    | throw (IO.userError "usage: mkrequest <fixture.json> <network> <request out> <expected out>")
  let json ← IO.ofExcept (Lean.Json.parse (← IO.FS.readFile path))
  let cases ← json.toIoRBNode
  let mut found : Option Lean.Json := none
  for (_, case) in cases.toArray.toList do
    if (← case.find "network" >>= Lean.Json.toIoString) == network then found := some case
  let some case := found | throw (IO.userError s!"no case for network {network}")
  let some fork := (match network with
    | "Cancun" => some Fork.cancun | "Prague" => some Fork.prague | "Osaka" => some Fork.osaka
    | _ => none) | throw (IO.userError "network must be Cancun, Prague or Osaka")
  let rules ← IO.ofExcept (fork.rules.mapError SupportError.render)
  let pre ← (← case.find "pre").toWorldAt rules
  let genesis ← case.find "genesisRLP" >>= Lean.Json.toIoBytes
  let blocks ← (← case.find "blocks" >>= Lean.Json.toIoList).mapM
    fun block => block.find "rlp" >>= Lean.Json.toIoBytes
  let request : Evm.Service.Request :=
    { fork, chainId := 1, accounts := pre.toList, genesis, blocks }
  let some bytes := request.encode | throw (IO.userError "fork has no code")
  IO.FS.writeBinFile requestPath bytes
  let tip ← case.find "lastblockhash" >>= Lean.Json.toIoU256
  let root := (← (← case.find "postState").toWorld).root
  IO.FS.writeBinFile expectedPath (Evm.Service.Response.encode ⟨0, blocks.length, tip, root⟩)
  IO.println s!"{network}: {pre.toList.length} accounts, {blocks.length} blocks, request {bytes.size} bytes"
  return 0
