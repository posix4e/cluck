/-! # Talking to the Nitro Secure Module

The enclave's second device, after the socket: it signs attestation documents and gives out random bytes.
One request and one response per exchange, each a CBOR value, at most `maxRequest` and `maxResponse` bytes.
This file is the messages, as pure functions: what to send, and what an answer means. The driver underneath
only moves the bytes.

The shapes are the ones AWS publishes in `aws-nitro-enclaves-nsm-api` (requests and responses are Rust enums
written out by serde), and the same ones Linux's `nsm` driver builds by hand for `GetRandom`:

  request   "GetRandom"
  response  {"GetRandom": {"random": bytes}}

  request   {"Attestation": {"user_data": bytes or null, "nonce": bytes or null, "public_key": bytes or null}}
  response  {"Attestation": {"document": bytes}}

  any       {"Error": "InvalidArgument"}, and so on

Only the CBOR these need is here: text, byte strings, maps with a known number of entries, and null, with
lengths in the definite forms. A response is read strictly: exactly the shape above, nothing extra, nothing
left over. The device is on the trusted side (it is the hypervisor), but its answers still arrive as bytes,
and bytes are checked before they are believed. -/

namespace Kernel.Nsm

def maxRequest : Nat := 0x1000
def maxResponse : Nat := 0x3000

/-! ## Writing CBOR -/

/-- The head of a CBOR item: its major type (0 to 7) and its argument, in the shortest form. -/
def head (major argument : Nat) : ByteArray :=
  let first (info : Nat) : UInt8 := (major * 32 + info).toUInt8
  let be (out : ByteArray) (width : Nat) : ByteArray :=
    (List.range width).foldl (fun out i => out.push (argument >>> (8 * (width - 1 - i))).toUInt8) out
  if argument < 24 then ByteArray.empty.push (first argument)
  else if argument < 0x100 then be (ByteArray.empty.push (first 24)) 1
  else if argument < 0x10000 then be (ByteArray.empty.push (first 25)) 2
  else if argument < 0x100000000 then be (ByteArray.empty.push (first 26)) 4
  else be (ByteArray.empty.push (first 27)) 8

def text (s : String) : ByteArray := head 3 s.utf8ByteSize ++ s.toUTF8
def bytes (b : ByteArray) : ByteArray := head 2 b.size ++ b
def null : ByteArray := ByteArray.empty.push 0xF6
def mapHead (entries : Nat) : ByteArray := head 5 entries

def optionalBytes : Option ByteArray → ByteArray
  | some b => bytes b
  | none => null

/-! ## Requests -/

def getRandom : ByteArray := text "GetRandom"

/-- A request for an attestation document carrying these three fields, or `none` if it would be too large
for the device. The device signs whatever is put here, so what goes in `userData` and `publicKey` is what a
verifier will be told this enclave vouches for. -/
def attestation (userData nonce publicKey : Option ByteArray) : Option ByteArray :=
  let request := mapHead 1 ++ text "Attestation" ++ mapHead 3 ++
    text "user_data" ++ optionalBytes userData ++
    text "nonce" ++ optionalBytes nonce ++
    text "public_key" ++ optionalBytes publicKey
  if request.size ≤ maxRequest then some request else none

/-! ## Reading CBOR -/

/-- A position in a response being read. Every step checks the bytes are there before looking at them. -/
structure Cursor where
  input : ByteArray
  pos : Nat

/-- The head at the cursor: major type and argument. Indefinite lengths and reserved forms are refused. -/
def Cursor.head? (c : Cursor) : Option (Nat × Nat × Cursor) :=
  if c.pos ≥ c.input.size then none else
  let first := c.input[c.pos]!.toNat
  let major := first / 32
  let info := first % 32
  let wide (width : Nat) : Option (Nat × Nat × Cursor) :=
    if c.pos + 1 + width > c.input.size then none else
    let argument := (List.range width).foldl (fun acc i => acc * 256 + c.input[c.pos + 1 + i]!.toNat) 0
    some (major, argument, { c with pos := c.pos + 1 + width })
  if info < 24 then some (major, info, { c with pos := c.pos + 1 })
  else if info == 24 then wide 1
  else if info == 25 then wide 2
  else if info == 26 then wide 4
  else if info == 27 then wide 8
  else none

/-- A string of the given major type (2 for bytes, 3 for text) at the cursor: its bytes. -/
def Cursor.string? (c : Cursor) (major : Nat) : Option (ByteArray × Cursor) := do
  let (found, length, c) ← c.head?
  if found != major || length > c.input.size - c.pos then none
  else some (c.input.extract c.pos (c.pos + length), { c with pos := c.pos + length })

/-- Exactly this text at the cursor. -/
def Cursor.expectText? (c : Cursor) (expected : String) : Option Cursor := do
  let (found, c) ← c.string? 3
  if found == expected.toUTF8 then some c else none

/-- A map of exactly this many entries at the cursor. -/
def Cursor.expectMap? (c : Cursor) (entries : Nat) : Option Cursor := do
  let (major, found, c) ← c.head?
  if major == 5 && found == entries then some c else none

def Cursor.done (c : Cursor) : Bool := c.pos == c.input.size

/-! ## Responses -/

inductive Response where
  | random (bytes : ByteArray)
  | attestation (document : ByteArray)
  /-- The device refused; `code` is its name for why (`InvalidArgument`, `InputTooLarge`, …). -/
  | error (code : String)

/-- `{"<outer>": {"<inner>": bytes}}` and nothing else. -/
def wrappedBytes? (raw : ByteArray) (outer inner : String) : Option ByteArray := do
  let c : Cursor := { input := raw, pos := 0 }
  let c ← c.expectMap? 1
  let c ← c.expectText? outer
  let c ← c.expectMap? 1
  let c ← c.expectText? inner
  let (value, c) ← c.string? 2
  if c.done then some value else none

/-- `{"Error": text}` and nothing else. -/
def error? (raw : ByteArray) : Option String := do
  let c : Cursor := { input := raw, pos := 0 }
  let c ← c.expectMap? 1
  let c ← c.expectText? "Error"
  let (code, c) ← c.string? 3
  if !c.done then none else
  -- The codes are plain names; anything else is not one of them.
  if code.size ≤ 64 && code.toList.all (fun b => (b ≥ 65 && b ≤ 90) || (b ≥ 97 && b ≤ 122)) then
    some (String.ofList (code.toList.map fun b => Char.ofNat b.toNat))
  else none

/-- What the device answered, or `none` if it is not an answer this code knows how to read. -/
def Response.parse? (raw : ByteArray) : Option Response :=
  if raw.size > maxResponse then none else
  match wrappedBytes? raw "GetRandom" "random" with
  | some bytes => some (.random bytes)
  | none =>
    match wrappedBytes? raw "Attestation" "document" with
    | some document => some (.attestation document)
    | none => (error? raw).map .error

/-! ## The time in an attestation document

An enclave has no clock of its own. The hypervisor, which is trusted with everything already, writes the
time into each attestation document it signs, so a document asked for now says what time it is. This reads
that one field and nothing else: the document's signature is not checked here, because the document did not
come from the parent but from the device.

The document is a COSE_Sign1 structure, an array of four whose third member is the payload: a map from names
to values, among them `timestamp`, milliseconds since 1970. A real document's payload is a map of indefinite
length, so that form is read here too, and members other than the one wanted are stepped over whatever they
are. -/

/-- Steps over items until none are owed. `owed` is a stack: how many items are still to come at each level,
or `none` inside something of indefinite length, which ends at a break. Each step uses up fuel. -/
def Cursor.skipLoop : (fuel : Nat) → Cursor → (owed : List (Option Nat)) → Option Cursor
  | 0, _, _ => none
  | _ + 1, c, [] => some c
  | fuel + 1, c, some 0 :: rest => skipLoop fuel c rest
  | fuel + 1, c, top :: rest =>
    if c.pos ≥ c.input.size then none else
    let first := c.input[c.pos]!.toNat
    if first == 0xFF then
      match top with
      | none => skipLoop fuel { c with pos := c.pos + 1 } rest
      | some _ => none
    else
      let after := top.map (· - 1) :: rest
      if first % 32 == 31 then
        -- of indefinite length: only arrays and maps are read that way
        if first / 32 == 4 || first / 32 == 5 then skipLoop fuel { c with pos := c.pos + 1 } (none :: after)
        else none
      else
        match c.head? with
        | none => none
        | some (major, argument, c) =>
          if major == 2 || major == 3 then
            if argument > c.input.size - c.pos then none
            else skipLoop fuel { c with pos := c.pos + argument } after
          else if major == 4 then skipLoop fuel c (some argument :: after)
          else if major == 5 then skipLoop fuel c (some (2 * argument) :: after)
          else if major == 6 then skipLoop fuel c (some 1 :: after)
          else skipLoop fuel c after

/-- The cursor after one whole item, whatever it is. -/
def Cursor.skip? (c : Cursor) : Option Cursor := c.skipLoop (4 * c.input.size + 16) [some 1]

/-- Looks through the members of a map for `timestamp`. `left` is how many members remain, or `none` for a
map of indefinite length. -/
def Cursor.findTime : (fuel : Nat) → Cursor → (left : Option Nat) → Option Nat
  | 0, _, _ => none
  | _ + 1, _, some 0 => none
  | fuel + 1, c, left =>
    if c.pos ≥ c.input.size then none else
    if c.input[c.pos]! == 0xFF then none else
    match c.string? 3 with
    | none => none
    | some (name, c) =>
      if name == "timestamp".toUTF8 then
        match c.head? with
        | some (0, milliseconds, _) => some milliseconds
        | _ => none
      else
        match c.skip? with
        | none => none
        | some c => findTime fuel c (left.map (· - 1))

/-- The time an attestation document carries, in milliseconds since 1970, or `none` if it is not a document
or has no time. -/
def documentTime? (document : ByteArray) : Option Nat := do
  if document.size > maxResponse then none
  let c : Cursor := { input := document, pos := 0 }
  -- COSE_Sign1 may come with its tag, 18, in front
  let c := if document.size > 0 && document[0]! == 0xD2 then { c with pos := 1 } else c
  let (major, members, c) ← c.head?
  if major != 4 || members != 4 then none
  let c ← c.skip?
  let c ← c.skip?
  let (payload, _) ← c.string? 2
  let p : Cursor := { input := payload, pos := 0 }
  if payload.size == 0 then none
  if payload[0]! == 0xBF then Cursor.findTime (payload.size + 1) { p with pos := 1 } none
  else
    let (major, entries, p) ← p.head?
    if major != 5 then none
    Cursor.findTime (payload.size + 1) p (some entries)

end Kernel.Nsm
