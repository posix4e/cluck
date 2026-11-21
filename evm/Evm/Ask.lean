import Evm.Relays
import Tls.Http

/-! A request to ask a relay something, and the answer.

    "JASK1"
    1    which relay, by its place in this image's list (`Evm/Relays.lean`)
    8    the time, in seconds since 1970, at which the relay's certificate is to be judged
    then the path to ask for, as in "/relay/v1/builder/validators"

The machine opens a connection to that relay itself, over TLS, asks for the path with GET, and answers
with

    1    0 for an answer from the relay, 1 for none, 2 for a request that cannot be carried out
    2    the relay's status (200 and so on), or zeros
    then the body of the relay's answer; or, with none, the reason in words

What this is for: it is the smallest thing that has the guest talk to a relay with nobody in between, and
wrapped in a request for a report (`Evm/Attest.lean`) it shows that a machine of these measurements got
this answer from the relay it names. It sends nothing of anyone's but the path, and only GET.

The time is the sender's word: the guest has no clock that knows the date. A sender that lies about it
can have a certificate believed that has run out (not one that was never good), and none is judged
earlier than the day this image's roots were written down. `THREAT_MODEL.md` has this. -/

namespace Evm.Ask

def magic : ByteArray := "JASK1".toUTF8

def mine (input : ByteArray) : Bool := input.size ≥ magic.size && input.extract 0 magic.size == magic

structure Request where
  relay : Nat
  seconds : Nat
  path : String

/-- The longest path taken. -/
def maxPath : Nat := 512

/-- A request read. The path must begin with `/` and be plain printing characters, so that it cannot
carry a line end and with it a second request or a header. -/
def request? (input : ByteArray) : Option Request :=
  if !mine input || input.size < magic.size + 9 then none else
  let seconds := (input.extract (magic.size + 1) (magic.size + 9)).foldl (fun n b => n * 256 + b.toNat) 0
  let path := input.extract (magic.size + 9) input.size
  if path.isEmpty || path.size > maxPath || path[0]! != 0x2f || path.data.any (fun c => c ≤ 0x20 || c ≥ 0x7f) then none
  else some { relay := input[magic.size]!.toNat, seconds, path := String.ofList (path.data.toList.map fun c => Char.ofNat c.toNat) }

def answered (status : Nat) (body : ByteArray) : ByteArray :=
  ByteArray.mk #[0, (status >>> 8).toUInt8, status.toUInt8] ++ body

def unanswered (why : String) : ByteArray := ByteArray.mk #[1, 0, 0] ++ why.toUTF8

def refused (why : String) : ByteArray := ByteArray.mk #[2, 0, 0] ++ why.toUTF8

/-- What is sent to the relay. The connection is for this one question. -/
def question (host : String) (path : String) : ByteArray :=
  Tls.Http.request "GET" host.toUTF8 path #[("User-Agent", "builder"), ("Accept", "*/*"), ("Connection", "close")]

end Evm.Ask
