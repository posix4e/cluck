import Evm.Outbound
import Fast.State

/-! A request to build a block, bid for it, and hand both to relays: the machine that built the block
posts it itself, over TLS, so nobody between it and the relay needs to be shown the block.

    "JSND1"
    1    which relays: a bit for each place in this image's list (`Evm/Relays.lean`), the lowest the first
    8    the time, in seconds since 1970, at which the relays' certificates are to be judged
    4    milliseconds the relays are given to answer, counted from when the block is ready; 0 for 3000
    then a request to build and bid, from its "JBID2" on (`Evm/Bid.lean`)

is answered, once every relay has answered or been given up, with

    4    the length of the answer to the request to build and bid, then that answer, as it would have
         been alone
    1    how many relays the block was sent to: none when no block was built
    then for each, in the order of the list:
         1    its place in the list
         1    0 when it answered, 1 when it did not
         2    its status (200 when it took the block), or zeros
         2    a length, then that many bytes: the start of what it said, or the reason there was no answer
    1    how many things the witness lacked for transactions that were left out because of it, then each:
         1    0 an account, 1 a slot of an account's storage, 2 a code
         32   the account's address as a 32-byte number; or the code's hash
         32   the slot's number; or zeros

What is sent to a relay is the builder API's request to submit a block (`Evm/Submit.lean`), as SSZ.

## Transactions the sender has not seen

A block built for this request also tries the transactions that were sealed to this machine and are
still good for the slot (`Evm/Seal.lean`), when the request asks for the fast engine's builder. The
request's sender proposed its own and supplied the witness, and has never seen these.

If there are none to try, the answer is as above, and the sender has the whole block as with any request
to build. If there is one, whether or not it goes in, the answer to the request to build and bid is, in
place of the usual one, five bytes: 8 and four zeros. The header, the block's hash, what it pays and which
transactions went in are not said: with the state of the chain in hand, as the sender has, any of them
would let a guess at a hidden transaction be checked. Nor is it said whether the sealed transaction went
in: whoever asks for blocks chooses what else is proposed, and could learn what a sealed transaction pays
and how much gas it allows by filling blocks to different levels and being told each time. The relays are
sent the block and say what they say; the sender is told that. (The four zeros were once the number that
went in.)

A block is not sent when a relay has already taken one from this machine for the same slot, built on
the same block, that pays as much or more: a relay keeps a builder's newest, and a block cut short by
the clock would otherwise take the place of a fuller one. The answer then names no relay, as when no
block was built. With sealed transactions tried this tells the request's sender that the block paid no
more than the last, which a relay's public list of bids would have told it too.

Nor is a block sent that pays the proposer nothing: a relay refuses it. The answer names no relay then
either, which with sealed transactions tried says that none that went in paid anything.

Nor is a block sent that was ended more than half a second after the time allowed for its transactions
ran out (`grace`): the allowance is there so that the block reaches the relay before its slot, and one
long transaction can carry a block past it. The answer names no relay then either.

What goes to a relay is made up, inside TLS, to a whole number of 16384 bytes, so that the length of
what the machine sends, which whoever carries it can see, does not say whether a transaction of a few
hundred bytes is in it.

A sealed transaction reads state the sender's witness may not prove, since the sender did not know to
prove it. One that came without proofs of its own is then left out, like any transaction the witness
falls short for, and the last part of the answer says what was lacking, so that the sender can prove
that too and ask again. This is how the sender comes to know which accounts and slots such a transaction
touches, and it is all it comes to know of it.

One that came with its own proofs (`Evm/Seal.lean`, "With proofs") is tried only in a block built on the
newest block this machine has checked for itself (`Evm/Follow.lean`), where its proofs are good. What it
lacks is never said, and if the block cannot be built with it in, the block is built again without it and
that is not said either. The sender of this request then learns of it only that a sealed transaction
went in, or nothing. -/

namespace Evm.Send

def magic : ByteArray := "JSND1".toUTF8

def mine (input : ByteArray) : Bool := input.size ≥ magic.size && input.extract 0 magic.size == magic

structure Request where
  /-- A bit for each relay of the image's list. -/
  relays : Nat
  seconds : Nat
  /-- Milliseconds the relays have to answer. -/
  allowed : Nat
  /-- The request to build and bid. -/
  bid : ByteArray

def request? (input : ByteArray) : Option Request :=
  if !mine input || input.size < magic.size + 13 then none else
  let number (start size : Nat) : Nat := (input.extract (magic.size + start) (magic.size + start + size)).foldl (fun n b => n * 256 + b.toNat) 0
  let allowed := number 9 4
  some { relays := number 0 1, seconds := number 1 8, allowed := if allowed == 0 then 3000 else allowed,
         bid := input.extract (magic.size + 13) input.size }

/-- What is sent to a relay: the block and bid, posted. The connection is left open for the next block if
the relay will have it so (`Evm/Outbound.lean`). -/
def question (host : String) (submission : ByteArray) : ByteArray :=
  Tls.Http.request "POST" host.toUTF8 "/relay/v1/builder/blocks"
    #[("Content-Type", "application/octet-stream"), ("Eth-Consensus-Version", "fulu"), ("User-Agent", "builder"),
      ("Accept", "*/*")] submission

/-- The most that is kept of what a relay said. -/
def kept : Nat := 300

def two (n : Nat) : ByteArray := ByteArray.mk #[(n >>> 8).toUInt8, n.toUInt8]

def four (n : Nat) : ByteArray := ByteArray.mk #[(n >>> 24).toUInt8, (n >>> 16).toUInt8, (n >>> 8).toUInt8, n.toUInt8]

/-- What stands in place of the bid's answer when sealed transactions were tried in the block. -/
def hidden : ByteArray := ByteArray.mk #[8] ++ four 0

/-- What is sent to a relay is made up to a whole number of this many bytes inside TLS. -/
def bucket : Nat := 16384

/-- How long after the time allowed for transactions has run out a block may be ended and still be sent,
in milliseconds. The time is looked at between transactions, so one long transaction, or a long ending,
can carry a block well past it; whoever set the allowance set it to have the block at the relay in time,
and a block this far over would not be. -/
def grace : Nat := 500

/-- The answer: the bid's, then what each relay said, then what the witness lacked. -/
def answer (bid : ByteArray) (told : Array (Nat × Outbound.Outcome)) (wanted : Array Fast.Lack := #[]) : ByteArray :=
  let out := told.foldl (fun out (place, outcome) =>
    let (failed, status, text) : UInt8 × Nat × ByteArray := match outcome with
      | .answered status body => (0, status, body.extract 0 kept)
      | .failed why => (1, 0, why.toUTF8.extract 0 kept)
    out ++ ByteArray.mk #[place.toUInt8, failed] ++ two status ++ two text.size ++ text) ((four bid.size ++ bid).push told.size.toUInt8)
  let wanted := wanted.extract 0 255
  wanted.foldl (fun out lack => (out.push lack.kind) ++ lack.what.bytes ++ lack.key.bytes) (out.push wanted.size.toUInt8)

end Evm.Send
