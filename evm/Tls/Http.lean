import Tls.Wire

/-! As much of HTTP/1.1 as asking a relay something takes (RFC 9112): a request written, and an answer
read out of the bytes that came, whether its length was given, or it came in chunks, or it ends when the
connection does. Everything here is bytes; names of headers are compared with their capitals made small. -/

namespace Tls.Http

def line (s : String) : ByteArray := (s ++ "\r\n").toUTF8

/-- A request for `path` at `host`. A body, if there is one, goes with its length. -/
def request (method : String) (host : ByteArray) (path : String) (headers : Array (String × String) := #[])
    (body : ByteArray := .empty) : ByteArray :=
  let head := line s!"{method} {path} HTTP/1.1" ++ "Host: ".toUTF8 ++ host ++ line ""
  let head := headers.foldl (fun out (name, value) => out ++ line s!"{name}: {value}") head
  let head := if body.isEmpty && method == "GET" then head else head ++ line s!"Content-Length: {body.size}"
  head ++ line "" ++ body

structure Response where
  status : Nat
  /-- Names with their capitals made small, and values without the spaces around them. -/
  headers : Array (ByteArray × ByteArray)
  body : ByteArray

def Response.header (r : Response) (name : String) : Option ByteArray :=
  (r.headers.find? (·.1 == name.toUTF8)).map (·.2)

/-- Where `needle` first lies in `hay` at or after `start`. -/
def find (hay needle : @& ByteArray) (start : Nat) : Option Nat :=
  go hay needle start (hay.size + 1 - start)
where
  go (hay needle : @& ByteArray) (i : Nat) : Nat → Option Nat
    | 0 => none
    | fuel + 1 =>
      if i + needle.size > hay.size then none
      else if hay.extract i (i + needle.size) == needle then some i
      else go hay needle (i + 1) fuel

def crlf : ByteArray := ByteArray.mk #[0x0d, 0x0a]

/-- `b` without the spaces and tabs at its ends. -/
def trimmed (b : ByteArray) : ByteArray :=
  let blank (c : UInt8) : Bool := c == 0x20 || c == 0x09
  let front := (b.data.toList.takeWhile blank).length
  let back := (b.data.toList.reverse.takeWhile blank).length
  if front + back ≥ b.size then .empty else b.extract front (b.size - back)

/-- A number written in digits of the given base, with nothing else; none for anything else or for one
too long to be a length. -/
def numberIn (base : Nat) (b : ByteArray) : Option Nat :=
  if b.isEmpty || b.size > 12 then none else
  b.foldl (fun n c => n.bind fun n =>
    let digit : Option Nat :=
      if c ≥ 0x30 && c ≤ 0x39 then some (c.toNat - 0x30)
      else if c ≥ 0x61 && c ≤ 0x66 then some (c.toNat - 0x57)
      else if c ≥ 0x41 && c ≤ 0x46 then some (c.toNat - 0x37)
      else none
    digit.bind fun d => if d < base then some (n * base + d) else none) (some 0)

/-- What has been made of the bytes so far. -/
inductive Read where
  /-- Not all of it is here yet. -/
  | more
  | broken (why : String)
  /-- An answer, and how many bytes it took. -/
  | whole (response : Response) (used : Nat)

/-- A body sent in chunks, from `at_`: each a length in hexadecimal on a line, then that many bytes. -/
def chunks (b : @& ByteArray) (limit : Nat) : Nat → Nat → ByteArray → Option (Option (ByteArray × Nat))
  | 0, _, _ => some none
  | fuel + 1, at_, body =>
    match find b crlf at_ with
    | none => some none
    | some stop =>
      -- A chunk's length may be followed by `;` and things nobody uses.
      let field := b.extract at_ stop
      let field := match find field (ByteArray.mk #[0x3b]) 0 with | some i => field.extract 0 i | none => field
      match numberIn 16 (trimmed field) with
      | none => none
      | some 0 =>
        -- The last chunk; then lines nobody uses, up to an empty one.
        match find b (crlf ++ crlf) stop with
        | some finish => some (some (body, finish + 4))
        | none => some none
      | some size =>
        if body.size + size > limit then none
        else if b.size < stop + 2 + size + 2 then some none
        else if b.extract (stop + 2 + size) (stop + 4 + size) != crlf then none
        else chunks b limit fuel (stop + 4 + size) (body ++ b.extract (stop + 2) (stop + 2 + size))

/-- An answer read from the start of `b`. `ended` says the connection is over, which is how an answer with
no length given ends. A body of more than `limit` bytes is refused. `head` says the request was a HEAD,
whose answer has no body whatever it says. -/
def response (b : @& ByteArray) (ended : Bool) (limit : Nat := 16 * 1024 * 1024) (head : Bool := false) : Read :=
  match find b (crlf ++ crlf) 0 with
  | none => if b.size > 65536 then .broken "headers too long" else if ended then .broken "cut short" else .more
  | some stop =>
    let first := (find b crlf 0).getD stop
    -- "HTTP/1.1 200 ...": the number is the three bytes from the ninth.
    match (if first ≥ 12 && b.extract 0 7 == "HTTP/1.".toUTF8 && Fast.byte b 8 == 0x20 then numberIn 10 (b.extract 9 12) else none) with
    | none => .broken "not an answer in HTTP/1.1"
    | some status =>
      let headers := fields b stop (first + 2) #[] (stop / 4 + 1)
      let value (name : String) : Option ByteArray := (headers.find? (·.1 == name.toUTF8)).map (·.2)
      let start := stop + 4
      let answer (body : ByteArray) (used : Nat) : Read := .whole { status, headers, body } used
      if head || status / 100 == 1 || status == 204 || status == 304 then answer .empty start
      else if (value "transfer-encoding").any (fun v => (find (lower v) "chunked".toUTF8 0).isSome) then
        match chunks b limit (b.size / 5 + 2) start .empty with
        | none => .broken "chunks that cannot be read"
        | some none => if ended then .broken "cut short" else .more
        | some (some (body, used)) => answer body used
      else match value "content-length" with
        | some text =>
          match numberIn 10 text with
          | none => .broken "a length that is not a number"
          | some length =>
            if length > limit then .broken "an answer too long"
            else if b.size < start + length then (if ended then .broken "cut short" else .more)
            else answer (b.extract start (start + length)) (start + length)
        | none =>
          if b.size - start > limit then .broken "an answer too long"
          else if ended then answer (b.extract start b.size) b.size else .more
where
  /-- The header lines between `at_` and `stop`. -/
  fields (b : @& ByteArray) (stop : Nat) : Nat → Array (ByteArray × ByteArray) → Nat → Array (ByteArray × ByteArray)
    | _, found, 0 => found
    | at_, found, fuel + 1 =>
      if at_ ≥ stop then found else
      let finish := match find b crlf at_ with | some i => min i stop | none => stop
      let one := b.extract at_ finish
      let found := match find one (ByteArray.mk #[0x3a]) 0 with
        | some colon => found.push (lower (trimmed (one.extract 0 colon)), trimmed (one.extract (colon + 1) one.size))
        | none => found
      fields b stop (finish + 2) found fuel

end Tls.Http
