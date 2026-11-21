import Evm.Bid
import JauneConsensus.Crypto.BLSSignature

/-! Checks a signed bid from outside: given a request for a bid and the reply to it, makes the bid out again
from the two and verifies the signature under the key the reply names, with `JauneConsensus`'s own
verification. For the host, which holds no key and trusts no reply. Never in an image.

    .lake/build/bin/bid-verify bid.req bid.reply        prints the builder's key and whether it verifies

Or, as a relay would: given a block and bid as they were posted to a relay, in SSZ (`Evm/Submit.lean`),
verifies the signature over the bid at its front under the builder's key it names, for mainnet's domain.

    .lake/build/bin/bid-verify --submission posted.ssz -/
open Jaune

def hex (bytes : ByteArray) : String :=
  bytes.foldl (fun out b => out ++ String.ofList [Nat.digitChar (b.toNat / 16), Nat.digitChar (b.toNat % 16)]) ""

def number (bytes : ByteArray) : Nat := bytes.foldl (fun n b => n * 256 + b.toNat) 0

def little (bytes : ByteArray) : Nat := bytes.data.foldr (fun b n => n * 256 + b.toNat) 0

/-- The bid at the front of a posted submission, and its signature, checked. -/
def submission (path : String) : IO UInt32 := do
  let posted ← IO.FS.readBinFile path
  if posted.size < 344 then IO.println "too short to be a submission"; return 1
  let part (start stop : Nat) : ByteArray := posted.extract start stop
  let bid : Evm.Bid.Bid :=
    { slot := little (part 0 8), parentHash := part 8 40, blockHash := part 40 72, builderKey := part 72 120,
      proposerKey := part 120 168, feeRecipient := part 168 188, gasLimit := little (part 188 196),
      gasUsed := little (part 196 204), value := little (part 204 236) }
  let message := (Evm.Bid.signingRoot bid.root (Evm.Bid.domain (ByteArray.mk #[0, 0, 0, 0]))).toList
  let ok := JauneConsensus.verify bid.builderKey.toList message (part 248 344).toList
  IO.println s!"builder {hex bid.builderKey}"
  IO.println s!"slot {bid.slot}, block {hex bid.blockHash}, gas used {bid.gasUsed}, value {bid.value}"
  IO.println (if ok then "the signature verifies" else "THE SIGNATURE DOES NOT VERIFY")
  return if ok then 0 else 1

def main (args : List String) : IO UInt32 := do
  if let ["--submission", path] := args then return ← submission path
  let [requestPath, replyPath] := args | do IO.eprintln "usage: bid-verify REQUEST REPLY | --submission POSTED"; return 2
  let request ← IO.FS.readBinFile requestPath
  let reply ← IO.FS.readBinFile replyPath
  if request.extract 0 5 != Evm.Bid.magic || request.size < 69 then IO.println "not a request for a bid"; return 1
  if reply.size < 109 + 144 || reply[0]! != 0 then IO.println s!"no block was built: status {reply[0]?.getD 255}"; return 1
  let slot := number (request.extract 5 13)
  let proposerKey := request.extract 13 61
  let forkVersion := request.extract 61 65
  let count := number (reply.extract 105 109)
  let headerAt := 109 + 4 * count
  let headerSize := number (reply.extract headerAt (headerAt + 4))
  let some header := Evm.Stateless.header (reply.extract (headerAt + 4) (headerAt + 4 + headerSize))
    | do IO.println "the reply's header does not decode"; return 1
  let builderKey := reply.extract (reply.size - 144) (reply.size - 96)
  let signature := reply.extract (reply.size - 96) reply.size
  let bid : Evm.Bid.Bid :=
    { slot, parentHash := Evm.Trie.wordBytes header.parentHash, blockHash := reply.extract 1 33, builderKey,
      proposerKey, feeRecipient := header.coinbase.toBytes.toByteArray, gasLimit := header.gasLimit,
      gasUsed := number (reply.extract 97 105), value := number (reply.extract 65 97) }
  if Evm.Trie.wordBytes header.hash != bid.blockHash then IO.println "the header is not the block the reply names"; return 1
  let message := (Evm.Bid.signingRoot bid.root (Evm.Bid.domain forkVersion)).toList
  let ok := JauneConsensus.verify builderKey.toList message signature.toList
  IO.println s!"builder {hex builderKey}"
  IO.println s!"slot {slot}, block {hex bid.blockHash}, gas used {bid.gasUsed}, value {bid.value}"
  IO.println (if ok then "the signature verifies" else "THE SIGNATURE DOES NOT VERIFY")
  return if ok then 0 else 1
