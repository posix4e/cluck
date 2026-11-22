import Tls.Aead
import Tls.Hkdf
import Tls.X25519
import Tls.X509
import Tls.Wire

/-! A TLS 1.3 client (RFC 8446), as small as the servers it is for allow.

It is a value and functions on it, with no connection of its own: `Client.start` gives the first bytes to
send, `Client.receive` takes whatever bytes arrived and gives back bytes to send and whatever data came
out, `Client.write` seals data to send. Who moves the bytes is somebody else's business, as with
`Kernel/Net/Tcp.lean`.

One of everything: TLS 1.3 and nothing older; X25519 for the key exchange; ChaCha20-Poly1305 with SHA-256;
the server proving its key by RSA-PSS or by ECDSA; HTTP/1.1 named as what follows. No session is resumed,
no data is sent early, no certificate is offered by the client, and a server that asks to begin again with
other parameters is refused, because there are no others. A server that sends anything not provided for
is refused: the connection fails and stays failed.

What is secret here: this side's key for the exchange, what the exchange gives, and every key made from
it. They are byte arrays that go only into `X25519`, `hmac` and the sealing; none becomes a `Nat`, and
nothing branches on one except to refuse. A key is dropped from this value when its use is over, which
does not wipe the memory it lay in. -/

namespace Tls

def zeros32 : ByteArray := ByteArray.mk (Array.replicate 32 0)

/-- The keys for one direction: the secret they were made from, the key, the 12 bytes each record's nonce
is made from, and how many records have gone. -/
structure Keys where
  secret : ByteArray
  key : ByteArray
  iv : ByteArray
  count : UInt64

namespace Keys

def none : Keys := ⟨.empty, .empty, .empty, 0⟩

def of (secret : ByteArray) : Keys :=
  ⟨secret, Hkdf.expandLabel secret "key" .empty 32, Hkdf.expandLabel secret "iv" .empty 12, 0⟩

/-- The nonce of the next record: the count, in the last eight bytes, over the fixed twelve. -/
def nonce (k : Keys) : ByteArray :=
  ByteArray.mk ((List.range 12).map fun i =>
    let c : UInt8 := if i < 4 then 0 else (k.count >>> (8 * (11 - i)).toUInt64).toUInt8
    Fast.byte k.iv i ^^^ c).toArray

/-- The keys that follow these when either side asks for new ones. -/
def next (k : Keys) : Keys := of (Hkdf.expandLabel k.secret "traffic upd" .empty 32)

/-- `content` of the given kind as a sealed record. The kind goes inside; outside every record says it is
application data. At most 16384 bytes. `padding` is how many zeros go in after the kind, which the far
end takes off: they make the record longer and say nothing (RFC 8446, 5.4). -/
def protect (k : Keys) (kind : UInt8) (content : ByteArray) (padding : Nat := 0) : Keys × ByteArray :=
  let header := ByteArray.mk #[0x17, 0x03, 0x03] ++ u16 (content.size + 17 + padding)
  ({ k with count := k.count + 1 },
   header ++ Aead.encrypt k.key k.nonce header (content.push kind ++ ByteArray.mk (Array.replicate padding 0)))

/-- Where `b` ends once the zeros a sender may pad a record with are taken off. -/
def unpadded (b : @& ByteArray) : Nat → Nat
  | 0 => 0
  | n + 1 => if Fast.byte b n != 0 then n + 1 else unpadded b n

/-- A sealed record opened: its kind and its content. Nothing if it does not open. -/
def unprotect (k : Keys) (header body : ByteArray) : Option (Keys × UInt8 × ByteArray) :=
  match Aead.decrypt? k.key k.nonce header body with
  | .none => .none
  | some inner =>
    let size := unpadded inner inner.size
    if size == 0 then .none
    else some ({ k with count := k.count + 1 }, Fast.byte inner (size - 1), inner.extract 0 (size - 1))

end Keys

/-- How far a connection has come. -/
inductive Stage where
  /-- The first message is sent and the server's is awaited. -/
  | hello
  /-- The keys are agreed and the server is proving who it is. -/
  | handshake
  /-- Data may go both ways. -/
  | ready
  /-- Either side said it was done. -/
  | closed
  | failed (why : String)
  deriving BEq

/-- Which message of the server's comes next while it proves who it is. -/
inductive Awaited where
  | extensions | certificate | verify | finished | nothing
  deriving BEq

structure Client where
  stage : Stage
  /-- The name asked for, which the server's certificate must be for. -/
  host : ByteArray
  anchors : Array X509.Anchor
  /-- The time certificates are judged at, in seconds since 1970. -/
  now : Nat
  /-- This side's key for the exchange, until it is used. -/
  key : ByteArray
  /-- Bytes that arrived and are not yet a whole record. -/
  input : ByteArray
  /-- Handshake bytes that are not yet a whole message. -/
  pending : ByteArray
  /-- Every handshake message so far, both ways: what the two sides sign and key by. -/
  transcript : ByteArray
  awaited : Awaited
  /-- What the keys for data will be made from. -/
  master : ByteArray
  reading : Keys
  writing : Keys
  serverKey : Option X509.Key

/-- What came of some bytes arriving: the connection as it now is, bytes to send, and data that came out. -/
structure Step where
  client : Client
  send : ByteArray := .empty
  data : ByteArray := .empty

def handshakeMessage (kind : UInt8) (body : ByteArray) : ByteArray := ByteArray.mk #[kind] ++ framed24 body

/-- A record that is not sealed. -/
def record (kind : UInt8) (body : ByteArray) : ByteArray := ByteArray.mk #[kind, 0x03, 0x03] ++ framed16 body

def extension (kind : Nat) (body : ByteArray) : ByteArray := u16 kind ++ framed16 body

/-- The first message: what this client can do, which is one thing of each kind, and its half of the key
exchange. -/
def clientHello (host random publicKey : ByteArray) : ByteArray :=
  let extensions :=
    -- the name asked for
    extension 0 (framed16 (ByteArray.mk #[0] ++ framed16 host))
    -- the one group: X25519
    ++ extension 10 (framed16 (u16 0x001d))
    -- signatures: RSA-PSS and ECDSA for the server's proof, and what certificates are signed with
    ++ extension 13 (framed16 (u16 0x0804 ++ u16 0x0403 ++ u16 0x0503 ++ u16 0x0401 ++ u16 0x0501))
    -- what follows the handshake: HTTP/1.1
    ++ extension 16 (framed16 (framed8 "http/1.1".toUTF8))
    -- the one version: TLS 1.3
    ++ extension 43 (framed8 (u16 0x0304))
    -- this side's half of the exchange
    ++ extension 51 (framed16 (u16 0x001d ++ framed16 publicKey))
  handshakeMessage 1 (
    u16 0x0303 ++ random
    ++ framed8 .empty                       -- no session to resume
    ++ framed16 (u16 0x1303)                -- the one suite: ChaCha20-Poly1305 with SHA-256
    ++ framed8 (ByteArray.mk #[0])          -- no compression
    ++ framed16 extensions)

/-- A connection begun to `host`: 32 bytes of `random` and a 32-byte `key`, both freshly drawn and the key
never used again, the roots trusted, and the time. With it, the bytes to send. -/
def Client.start (host : ByteArray) (anchors : Array X509.Anchor) (now : Nat) (random key : ByteArray) : Client × ByteArray :=
  let hello := clientHello host random (X25519.publicKey key)
  ({ stage := .hello, host, anchors, now, key, input := .empty, pending := .empty, transcript := hello,
     awaited := .nothing, master := .empty, reading := Keys.none, writing := Keys.none, serverKey := .none },
   record 22 hello)

def need {α : Type} (x : Option α) (why : String) : Except String α :=
  match x with
  | some a => .ok a
  | none => .error why

/-- A list of extensions as their numbers and bodies; nothing if it is not one, or one comes twice. -/
def extensionsOf (b : ByteArray) : Option (Array (Nat × ByteArray)) :=
  go (Cursor.of b) #[] (b.size / 4 + 1)
where
  go (c : Cursor) (found : Array (Nat × ByteArray)) : Nat → Option (Array (Nat × ByteArray))
    | 0 => if c.done then some found else none
    | fuel + 1 =>
      if c.done then some found
      else match c.number 2 with
        | none => none
        | some (kind, c) => match c.framed 2 with
          | none => none
          | some (body, c) => if found.any (·.1 == kind) then none else go c (found.push (kind, body)) fuel

/-- What a server sends in place of its random bytes to ask for a new start (RFC 8446, 4.1.3). -/
def helloRetry : ByteArray := Sha256.hash "HelloRetryRequest".toUTF8

def derive (secret : ByteArray) (label : String) (hash : ByteArray) : ByteArray := Hkdf.expandLabel secret label hash 32

/-- The server's first message: it must choose exactly what was offered. From its half of the exchange and
ours come the keys the rest of the handshake is sealed with. -/
def onServerHello (c : Client) (whole body : ByteArray) : Except String Client := do
  let (version, random, session, suite, compression, extensions) ← need (do
    let cur := Cursor.of body
    let (version, cur) ← cur.number 2
    let (random, cur) ← cur.take 32
    let (session, cur) ← cur.framed 1
    let (suite, cur) ← cur.number 2
    let (compression, cur) ← cur.number 1
    let (extensions, cur) ← cur.framed 2
    if !cur.done then none
    pure (version, random, session, suite, compression, ← extensionsOf extensions)) "a first message from the server that cannot be read"
  if random == helloRetry then throw "the server asked to begin again with other parameters, and there are no others"
  if version != 0x0303 || compression != 0 || !session.isEmpty then throw "a first message from the server that is not TLS 1.3's"
  if suite != 0x1303 then throw "the server chose a cipher that was not offered"
  if extensions.size != 2 then throw "the server's first message carries what it may not"
  let chosen ← need (extensions.find? (·.1 == 43)) "the server did not choose TLS 1.3"
  if chosen.2 != u16 0x0304 then throw "the server did not choose TLS 1.3"
  let share ← need (extensions.find? (·.1 == 51)) "the server sent no half of the key exchange"
  let peer ← need (do
    let cur := Cursor.of share.2
    let (group, cur) ← cur.number 2
    let (peer, cur) ← cur.framed 2
    if group != 0x001d || peer.size != 32 || !cur.done then none
    pure peer) "the server's half of the key exchange is not X25519's"
  let shared := X25519.x25519 c.key peer
  -- A point of small order gives nothing, whatever the key: nobody honest sends one.
  if Secret.equal shared zeros32 then throw "a key exchange that came to nothing"
  let transcript := c.transcript ++ whole
  let hash := Sha256.hash transcript
  let nothing := Sha256.hash .empty
  let handshake := Hkdf.extract (derive (Hkdf.extract zeros32 zeros32) "derived" nothing) shared
  pure { c with
    stage := .handshake, key := .empty, transcript, awaited := .extensions
    master := Hkdf.extract (derive handshake "derived" nothing) zeros32
    reading := Keys.of (derive handshake "s hs traffic" hash)
    writing := Keys.of (derive handshake "c hs traffic" hash) }

/-- The certificates in the server's Certificate message, its own first. -/
def certificatesOf (body : ByteArray) : Option (Array ByteArray) := do
  let cur := Cursor.of body
  let (context, cur) ← cur.framed 1
  let (list, cur) ← cur.framed 3
  if !context.isEmpty || !cur.done then none
  go (Cursor.of list) #[] (list.size / 5 + 1)
where
  go (c : Cursor) (found : Array ByteArray) : Nat → Option (Array ByteArray)
    | 0 => if c.done then some found else none
    | fuel + 1 =>
      if c.done then some found
      else match c.framed 3 with
        | none => none
        | some (certificate, c) => match c.framed 2 with
          -- Nothing was asked for with a certificate, so nothing may come with one.
          | some (extras, c) => if extras.isEmpty then go c (found.push certificate) fuel else none
          | none => none

/-- What the server signs to prove it holds its certificate's key: a fixed opening and the hash of every
message so far (RFC 8446, 4.4.3). -/
def proofOf (transcript : ByteArray) : ByteArray :=
  (ByteArray.mk (Array.replicate 64 0x20) ++ "TLS 1.3, server CertificateVerify".toUTF8).push 0 ++ Sha256.hash transcript

/-- One whole handshake message, in its turn: the connection after it and anything to send. -/
def onMessage (c : Client) (kind : UInt8) (whole body : ByteArray) : Except String (Client × ByteArray) :=
  match c.stage, c.awaited, kind with
  | .hello, _, 2 => do pure (← onServerHello c whole body, .empty)
  | .handshake, .extensions, 8 => do
    let extensions ← need (do
      let cur := Cursor.of body
      let (list, cur) ← cur.framed 2
      if !cur.done then none
      extensionsOf list) "the server's extensions cannot be read"
    for (number, value) in extensions do
      -- Only an answer to something offered may come: the name, the groups, what follows the handshake.
      if number == 16 then
        if value != framed16 (framed8 "http/1.1".toUTF8) then throw "the server chose something other than HTTP/1.1"
      else if number != 0 && number != 10 then throw "the server sent an extension that was not offered"
    pure ({ c with awaited := .certificate, transcript := c.transcript ++ whole }, .empty)
  | .handshake, .certificate, 11 => do
    let chain ← need (certificatesOf body) "the server's certificates cannot be read"
    let key ← X509.validate c.anchors chain c.host c.now
    pure ({ c with awaited := .verify, serverKey := some key, transcript := c.transcript ++ whole }, .empty)
  | .handshake, .verify, 15 => do
    let (algorithm, signature) ← need (do
      let cur := Cursor.of body
      let (algorithm, cur) ← cur.number 2
      let (signature, cur) ← cur.framed 2
      if !cur.done then none
      pure (algorithm, signature)) "the server's proof of its key cannot be read"
    let said := proofOf c.transcript
    let holds := match algorithm, c.serverKey with
      | 0x0804, some (.rsa key) => Rsa.verifyPss key (Sha256.hash said) signature
      | 0x0403, some (.p256 x y) => X509.ecdsaHolds Ecdsa.p256 x y (Sha256.hash said) signature
      | 0x0503, some (.p384 x y) => X509.ecdsaHolds Ecdsa.p384 x y (Sha512.hash384 said) signature
      | _, _ => false
    if !holds then throw "the server did not prove it holds its certificate's key"
    pure ({ c with awaited := .finished, transcript := c.transcript ++ whole }, .empty)
  | .handshake, .finished, 20 => do
    -- The server's last word: a keyed hash of everything so far, which only the holder of the agreed
    -- keys can make. Then ours of everything including that, and the keys for data.
    let expected := hmac (Hkdf.expandLabel c.reading.secret "finished" .empty 32) (Sha256.hash c.transcript)
    if !Secret.equal expected body then throw "the server's finishing word is wrong"
    let hash := Sha256.hash (c.transcript ++ whole)
    let mine := handshakeMessage 20 (hmac (Hkdf.expandLabel c.writing.secret "finished" .empty 32) hash)
    let (_, sealed) := c.writing.protect 22 mine
    pure ({ c with
      stage := .ready, awaited := .nothing, transcript := .empty, master := .empty
      reading := Keys.of (derive c.master "s ap traffic" hash)
      writing := Keys.of (derive c.master "c ap traffic" hash) }, sealed)
  -- After the handshake: a ticket for coming back later, which is never used.
  | .ready, _, 4 => pure (c, .empty)
  -- New keys asked for: the server's change now, and ours too if it wants that.
  | .ready, _, 24 =>
    if body == ByteArray.mk #[0] then pure ({ c with reading := c.reading.next }, .empty)
    else if body == ByteArray.mk #[1] then
      let (writing, sealed) := c.writing.protect 22 (handshakeMessage 24 (ByteArray.mk #[0]))
      pure ({ c with reading := c.reading.next, writing := writing.next }, sealed)
    else throw "a request for new keys that cannot be read"
  | _, _, 13 => throw "the server asks this side for a certificate, and it has none"
  | _, _, _ => throw s!"a handshake message out of its turn ({kind.toNat})"

/-- Every whole handshake message that has arrived, in order. -/
def onMessages (c : Client) : Except String (Client × ByteArray) :=
  go c .empty (c.pending.size / 4 + 1)
where
  go (c : Client) (send : ByteArray) : Nat → Except String (Client × ByteArray)
    | 0 => pure (c, send)
    | fuel + 1 =>
      if c.pending.size < 4 then pure (c, send) else
      let kind := Fast.byte c.pending 0
      let length := (Fast.byte c.pending 1).toNat * 65536 + (Fast.byte c.pending 2).toNat * 256 + (Fast.byte c.pending 3).toNat
      if length > 65536 then throw "a handshake message too long to be honest"
      else if c.pending.size < 4 + length then pure (c, send)
      else do
        let whole := c.pending.extract 0 (4 + length)
        let (c, out) ← onMessage { c with pending := c.pending.extract (4 + length) c.pending.size } kind whole (whole.extract 4 whole.size)
        -- Keys change after these, so nothing may follow them in the same record (RFC 8446, 5.1).
        if (kind == 2 || kind == 20 || kind == 24) && !c.pending.isEmpty then throw "a change of keys in the middle of a record"
        go c (send ++ out) fuel

/-- One whole record: the connection after it, anything to send, any data that came out. -/
def onRecord (c : Client) (kind : UInt8) (header body : ByteArray) : Except String (Client × ByteArray × ByteArray) :=
  match c.stage with
  | .closed | .failed _ => pure (c, .empty, .empty)
  | .hello =>
    if kind == 22 && !body.isEmpty && body.size ≤ 16384 then do
      let (c, send) ← onMessages { c with pending := c.pending ++ body }
      pure (c, send, .empty)
    else if kind == 21 then throw s!"the server refused: alert {(Fast.byte body 1).toNat}"
    else throw "something other than the server's first message"
  | .handshake | .ready =>
    -- Servers send one record that means nothing, for the sake of old equipment on the way.
    if kind == 20 then
      if c.stage == .handshake && body == ByteArray.mk #[1] then pure (c, .empty, .empty)
      else throw "a record that means nothing where none is allowed"
    else if kind != 23 then throw "a record in the clear after the keys were agreed"
    else match c.reading.unprotect header body with
      | none => throw "a record that does not open"
      | some (reading, inner, content) =>
        let c := { c with reading }
        if content.size > 16384 then throw "a record too long"
        else if inner == 22 then
          if content.isEmpty then throw "an empty handshake record" else do
          let (c, send) ← onMessages { c with pending := c.pending ++ content }
          pure (c, send, .empty)
        else if !c.pending.isEmpty then throw "a handshake message broken off by something else"
        else if inner == 21 then
          if content.size == 2 && Fast.byte content 1 == 0 then pure ({ c with stage := .closed }, .empty, .empty)
          else throw s!"the server's alert {(Fast.byte content 1).toNat}"
        else if inner == 23 then
          if c.stage == .ready then pure (c, .empty, content) else throw "data before the server proved who it is"
        else throw "a record of no known kind"

/-- A connection that failed: it stays so, and holds no keys. -/
def Client.fail (c : Client) (why : String) : Client :=
  { c with stage := .failed why, key := .empty, master := .empty, reading := Keys.none, writing := Keys.none,
           input := .empty, pending := .empty, transcript := .empty }

/-- Bytes arrived, any number, cut anywhere. -/
def Client.receive (c : Client) (bytes : ByteArray) : Step :=
  let input := c.input ++ bytes
  go { c with input := .empty } input 0 .empty .empty (input.size / 5 + 1)
where
  go (c : Client) (input : ByteArray) (pos : Nat) (send data : ByteArray) : Nat → Step
    | 0 => { client := { c with input := input.extract pos input.size }, send, data }
    | fuel + 1 =>
      let stopped := match c.stage with | .closed | .failed _ => true | _ => false
      if stopped then { client := c, send, data }
      else if input.size < pos + 5 then { client := { c with input := input.extract pos input.size }, send, data }
      else
        let length := (Fast.byte input (pos + 3)).toNat * 256 + (Fast.byte input (pos + 4)).toNat
        if length > 16384 + 256 then { client := c.fail "a record too long", send, data }
        else if input.size < pos + 5 + length then { client := { c with input := input.extract pos input.size }, send, data }
        else
          match onRecord c (Fast.byte input pos) (input.extract pos (pos + 5)) (input.extract (pos + 5) (pos + 5 + length)) with
          | .error why => { client := c.fail why, send, data }
          | .ok (c, out, got) => go c input (pos + 5 + length) (send ++ out) (data ++ got) fuel

/-- Data sealed for sending, in records of at most 16384 bytes. Nothing unless the connection is ready. -/
def Client.write (c : Client) (data : ByteArray) : Client × ByteArray :=
  if c.stage != .ready then (c, .empty) else go c data 0 .empty (data.size / 16384 + 1)
where
  go (c : Client) (data : ByteArray) (pos : Nat) (out : ByteArray) : Nat → Client × ByteArray
    | 0 => (c, out)
    | fuel + 1 =>
      if pos ≥ data.size then (c, out)
      else
        let stop := min data.size (pos + 16384)
        let (writing, sealed) := c.writing.protect 23 (data.extract pos stop)
        go { c with writing } data stop (out ++ sealed) fuel

/-- Data sealed for sending and made up with padding to a whole number of `bucket` bytes, so that whoever
carries the records learns the length only to the nearest bucket. The padding goes in the last record of
data as far as it has room, and then in records with no data in them, never more than three: a far end
may tire of many records that carry nothing. With a bucket of 0, or one over 32768, nothing is added. -/
def Client.writePadded (c : Client) (data : ByteArray) (bucket : Nat) : Client × ByteArray :=
  if c.stage != .ready || bucket == 0 || bucket > 32768 then c.write data else
  let padding := (bucket - data.size % bucket) % bucket
  -- All but the last piece as they are; the last with what padding it has room for.
  let whole := if data.isEmpty then 0 else (data.size - 1) / 16384 * 16384
  let (c, out) := c.write (data.extract 0 whole)
  let last := data.extract whole data.size
  let here := min padding (16384 - last.size)
  let (writing, sealed) := c.writing.protect 23 last here
  go { c with writing } (padding - here) (out ++ sealed) 3
where
  go (c : Client) (left : Nat) (out : ByteArray) : Nat → Client × ByteArray
    | 0 => (c, out)
    | fuel + 1 =>
      if left == 0 then (c, out)
      else
        let here := min left 16384
        let (writing, sealed) := c.writing.protect 23 .empty here
        go { c with writing } (left - here) (out ++ sealed) fuel

/-- This side says it is done: the record that says so, and a connection that holds no keys. -/
def Client.close (c : Client) : Client × ByteArray :=
  if c.stage != .ready then (c, .empty)
  else
    let (_, sealed) := c.writing.protect 21 (ByteArray.mk #[1, 0])
    ({ c with stage := .closed, reading := Keys.none, writing := Keys.none }, sealed)

end Tls
