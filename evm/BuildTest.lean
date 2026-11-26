import Evm
import Evm.Seal

/-! Tests of `Evm.Build` against `Evm.Stateless`, which checks blocks, and against blocks that exist.

A stateless request is a block and a witness for it. Its block is used as the makings of a block: the
header as the template and the transactions as what is proposed.

- **Built again as given.** With the transactions kept in their order, the block built has to be the block
  the request holds: the same hash, which is every field of the header. That is the test that the header
  is put together as the chain puts it together.
- **A transaction that cannot go in.** The first transaction proposed a second time has a nonce already
  used. It has to be left out and the block come out as before.
- **Built by the rule.** With the transactions ordered by what they pay, whatever is built has to be a
  block `Evm.Stateless` accepts with the same witness.
- **A witness that falls short.** Each node, key and code of the witness is left out in turn. The answer
  has to be that nothing was built (4 when what is missing is needed before or after the transactions, by
  a system call; 6 or 7 otherwise), or a block that `Evm.Stateless` accepts with the whole witness: with
  less to go on it may build a smaller block, never a wrong one.

    .lake/build/bin/build-test             (from evm/: the three fixtures in fixtures/stateless/)
    .lake/build/bin/build-test write       (the same, and fixtures/build/ made again from them: a request
                                            to build by the rule and the response it must get)
    .lake/build/bin/build-test DIR         (every NAME.req in DIR as well, built again as given and by
                                            the rule; for blocks of mainnet made by witness/fetch)
    .lake/build/bin/build-test real DIR [STEP]
                                           (every NAME.req in DIR built by the rule with every STEPth
                                            address, by default every tenth, left out of its witness)

Run on Lean's own runtime. -/
open Jaune Evm

structure Tally where
  failures : Nat := 0
  checks : Nat := 0

def Tally.expect (t : Tally) (what : String) (ok : Bool) : IO Tally := do
  if !ok then IO.println s!"FAILED: {what}"
  pure { failures := t.failures + (if ok then 0 else 1), checks := t.checks + 1 }

/-- The block a response describes, as bytes: its header, the proposed transactions it names, and the
withdrawals proposed. -/
def blockOf (template : Block) (built : Build.Built) : ByteArray :=
  let proposed := template.transactions.toArray
  let block : Block :=
    { header := built.header, transactions := built.included.filterMap (proposed[·]?), ommers := [],
      withdrawals := template.withdrawals }
  block.toRlpItem.toBytes.toByteArray

/-- Whether `Evm.Stateless` accepts the block a response describes, with this witness, as the block the
response says it is. -/
def accepted (witness : Stateless.Request) (template : Block) (built : Build.Built) : Bool :=
  let answer := Stateless.run { witness with block := blockOf template built }
  answer.status == 0 && answer.tip == built.hash && answer.root == built.header.stateRoot

def one (engine : Bool) (name : String) (bytes : ByteArray) (shorten : Bool) (tally : Tally) (write : Bool := false) :
    IO Tally := do
  let mut tally := tally
  let name := (if engine then "the engine: " else "") ++ name
  let some (witness, _) := (Stateless.request bytes).run 0
    | tally.expect s!"{name}: not a stateless request" false
  let .ok (template, hash) := rlpToBlockE witness.block.toList
    | tally.expect s!"{name}: the block does not decode" false
  let count := template.transactions.length
  let limit := template.header.gasLimit
  -- Built again as given.
  let started ← IO.monoMsNow
  let again := Build.run { witness, rule := 0, gasCap := limit, engine }
  let took := (← IO.monoMsNow) - started
  match again.built with
  | some b =>
    tally ← tally.expect s!"{name}: built again as given, {b.included.length} of {count} went in and the \
      hash is {b.hash}, not {hash}" (b.hash == hash && b.included.length == count)
    -- The request survives being written and read, and the response says the same as bytes.
    match (Build.Request.encode { witness, rule := 0, gasCap := limit, engine }) with
    | some encoded =>
      let reply := Build.serve encoded
      tally ← tally.expect s!"{name}: the request as bytes is answered differently"
        (reply == again.encode && reply.size > 100 && reply.extract 1 33 == Trie.wordBytes hash)
    | none => tally ← tally.expect s!"{name}: the request has no encoding" false
    -- Read with what was sent before (`Build.Kept`). The same answer when everything is given and
    -- nothing was kept; when nothing is given and everything was kept; and with only the newest header
    -- given. No block once what was kept is forgotten, or has passed its limit.
    if engine then
      let asked : Build.Request := { witness, rule := 0, gasCap := limit, engine, seen := some false }
      let (whole, kept) := ({} : Build.Kept).take asked
      let bare : Build.Request := { asked with witness := { witness with headers := [], nodes := #[], codes := [] } }
      let (second, keptStill) := kept.take bare
      let newest : Build.Request :=
        { bare with witness := { bare.witness with headers := witness.headers.drop (witness.headers.length - 1) } }
      let (third, _) := kept.take newest
      tally ← tally.expect s!"{name}: read with what was sent before, the answer is another"
        ((Build.run whole).encode == again.encode && (Build.run second).encode == again.encode
          && (Build.run third).encode == again.encode)
      let size := witness.codes.foldl (fun n code => n + code.size) (witness.nodes.foldl (fun n node => n + node.size) 0)
      tally ← tally.expect s!"{name}: what was given is not counted as {size} bytes, or the kept headers are not the request's"
        (kept.given == size && keptStill.given == size && (kept.take asked).2.given == 2 * size
          && kept.chain.map (·.bytes) == witness.headers.toArray && keptStill.chain.map (·.bytes) == witness.headers.toArray)
      let (forgotten, nothing) := kept.take { bare with seen := some true }
      let (_, past) := ({} : Build.Kept).take asked (limit := size - 1)
      tally ← tally.expect s!"{name}: a block was built on what had been forgotten"
        ((Build.run forgotten).built.isNone && nothing.given == 0 && nothing.chain.isEmpty
          && (size == 0 || (past.given == 0 && (Build.run (past.take bare).1).built.isNone)))
      -- The headers are decoded and checked when they are given and handed on as checked
      -- (`Request.ancestry`): every one of them, to each of the three requests above, and never to one
      -- as it comes off the wire. Headers given that do not follow one another, or one that is not a
      -- header, join nothing: no block, and what is kept stays as it was, so the next request is
      -- still answered from it.
      let count255 := witness.headers.length
      let handed (r : Build.Request) : Bool := match r.ancestry with
        | some known => known.length == count255
        | none => false
      let backwards : Build.Request := { bare with witness := { bare.witness with headers := witness.headers.reverse } }
      let (turned, keptTurned) := kept.take backwards
      let noHeader : Build.Request := { bare with witness := { bare.witness with headers := [⟨#[0xc0]⟩] } }
      let (broken, keptBroken) := kept.take noHeader
      tally ← tally.expect s!"{name}: the kept headers are not handed on as checked, or headers that are no chain were joined"
        (handed whole && handed second && handed third && asked.ancestry.isNone
          && (match Build.Request.encode asked with
              | some encoded => (match (Build.request encoded).run 0 with
                | some (read, _) => read.ancestry.isNone
                | none => false)
              | none => false)
          && (count255 < 2 || (turned.ancestry.isNone && (Build.run turned).built.isNone
                && keptTurned.chain.map (·.bytes) == witness.headers.toArray
                && (Build.run (keptTurned.take bare).1).encode == again.encode))
          && broken.ancestry.isNone && (Build.run broken).built.isNone
          && keptBroken.chain.map (·.bytes) == witness.headers.toArray
          && (Build.run (keptBroken.take bare).1).encode == again.encode)
      -- Who signed each transaction, kept from one request for the next (`Build.Signers`): one for each
      -- transaction, and the same answer with them handed in. One kept under another signature or
      -- another chain is not taken, whoever it names; one kept under the transaction's own is, which
      -- shows when it names somebody else (nothing outside can put one there: `Evm/Bid.lean`).
      let ((first, _, _), signers) := Id.run (Build.runKeeping (pure false) whole)
      let ((withThem, _, _), signersAgain) := Id.run (Build.runKeeping (pure false) { whole with signers })
      let nobody : Address := Address.max
      let made (change : Build.Signer → Build.Signer) : Build.Signers :=
        signers.foldl (fun out hash signer => out.insert hash (change signer)) {}
      tally ← tally.expect s!"{name}: with the signers kept the answer is another, or there are not {count} of them"
        (first.encode == again.encode && withThem.encode == again.encode
          && signers.size == count && signersAgain.size == count
          && (Build.run { whole with signers := made fun s => { s with v := s.v + 1, sender := nobody } }).encode == again.encode
          && (Build.run { whole with signers := made fun s => { s with chain := s.chain + 1, sender := nobody } }).encode == again.encode
          && (Build.run { whole with signers := made fun s => { s with r := 1 :: s.r, sender := nobody } }).encode == again.encode
          && (count == 0 || (Build.run { whole with signers := made fun s => { s with sender := nobody } }).encode != again.encode))
      -- Going on from the block before (`Build.runGoingOn`). The block's transactions proposed in two
      -- parts, the first half and then all of them, as given: the second request's block goes on from
      -- the first's and is the very block built at once; asked again, it goes on from itself and is
      -- that block still. (A first half that used more than half the gas is not gone on from, and the
      -- answer is then the same, built from nothing.)
      let going : Build.Request := { asked with goesOn := true }
      let goingBare : Build.Request := { bare with goesOn := true }
      let part (transactions : List (Bytes ⊕ Transaction)) (header : Header := template.header) : ByteArray :=
        ({ template with header, transactions } : Block).toRlpItem.toBytes.toByteArray
      let half := count / 2
      let run (r : Build.Request) (before : Option Build.Before) := Id.run (Build.runGoingOn (pure false) r before)
      let fuller (before : Option Build.Before) : Bool := match before with
        | some b => b.job.out.gasUsed.toNat * 2 > b.job.gasCap
        | none => true
      let wentFrom (went : Option Nat) (had : Nat) (before : Option Build.Before) : Bool :=
        if fuller before then went.isNone else went == some had
      let (firstWhole, keptFirst) := ({} : Build.Kept).take
        { going with witness := { witness with block := part (template.transactions.take half) } }
      let ((_, _, _), _, before, wentFirst) := run firstWhole none
      let (secondWhole, _) := keptFirst.take goingBare
      let ((second, _, _), _, beforeAll, wentSecond) := run secondWhole before
      let ((third, _, _), _, _, wentThird) := run secondWhole beforeAll
      tally ← tally.expect s!"{name}: proposed in two parts, the block that went on is not the block built at once"
        (wentFirst.isNone && before.isSome && beforeAll.isSome && second.encode == again.encode && third.encode == again.encode
          && wentFrom wentSecond half before && wentFrom wentThird count beforeAll)
      -- Out of time while going on, before the first of the new transactions and half way through
      -- them: a whole block that the checker accepts, holding the block before and what went in by
      -- then; and the request after it goes on from that to the block built at once.
      for k in [0, (count - half) / 2] do
        let over : StateM Nat Bool := modifyGet fun asked => (asked ≥ k, asked + 1)
        let (((cut, _, _), _, beforeCut, wentCut), _) := (Build.runGoingOn over secondWhole before).run 0
        let ((rest, _, _), _, _, _) := run secondWhole beforeCut
        let had := if wentCut.isSome then half else 0
        match cut.built with
        | some b =>
          tally ← tally.expect s!"{name}: going on and out of time after {k} more, {b.included.length} are in, the             checker does not accept the block, or the next request does not finish it"
            (b.included == List.range (had + k) && accepted witness template b && wentFrom wentCut half before
              && rest.encode == again.encode)
        | none =>
          tally ← tally.expect s!"{name}: going on and out of time after {k} more, status {cut.status}"
            (cut.status == 6 && rest.encode == again.encode)
      -- What is not the same block is built from nothing, as the same request without the word would
      -- be: another gas allowed, another rule, another fee recipient, a transaction of the block before
      -- no longer proposed, transactions the machine added. And what is kept to go on from goes when
      -- everything kept goes: on being told to forget, and past the limit.
      let startsOver (r : Build.Request) : Bool :=
        let ((answer, _, _), _, _, went) := run r before
        went.isNone && answer.encode == (Build.run { r with goesOn := false }).encode
      let proposing (block : ByteArray) : Build.Request := { secondWhole with witness := { secondWhole.witness with block } }
      let holding : Build.Kept := { keptFirst with before }
      let (overRequest, overKept) := holding.take going (limit := size - 1)
      tally ← tally.expect s!"{name}: a block went on from one that was not for the same place, or one forgotten was kept"
        (startsOver { secondWhole with gasCap := limit - 1 } && startsOver { secondWhole with rule := 1 }
          && startsOver (proposing (part template.transactions { template.header with coinbase := nobody }))
          && (half == 0 || startsOver (proposing (part (template.transactions.drop 1))))
          && (count == 0 || startsOver { secondWhole with fromSender := count - 1 })
          && (holding.take goingBare).1.goesOn && (holding.take goingBare).2.before.isSome
          && (holding.take { goingBare with seen := some true, goesOn := false }).2.before.isNone
          && (size == 0 || (!overRequest.goesOn && overKept.before.isNone)))
      -- By the rule: the block that went on is one the checker accepts, with the block before in it.
      let ((ruledFirst, _, _), _, beforeRuled, _) := run { firstWhole with rule := 1 } none
      let ((ruledSecond, _, _), _, _, wentRuled) := run { secondWhole with rule := 1 } beforeRuled
      let hadRuled := (ruledFirst.built.map (·.included.length)).getD 0
      match ruledSecond.built with
      | some b =>
        tally ← tally.expect s!"{name}: by the rule, the block that went on is not one the checker accepts, or lost what it had"
          (accepted witness template b && b.included.length ≥ hadRuled
            && (ruledFirst.built.isNone || wentFrom wentRuled hadRuled beforeRuled))
      | none => tally ← tally.expect s!"{name}: by the rule and going on, status {ruledSecond.status}" (ruledSecond.status == 6)
      -- A node the first request lacked, given with the second: what was left out for want of it is
      -- tried again, and the block is one the checker accepts with no less in it.
      if witness.nodes.size > 0 then
        let lacked := witness.nodes.size / 2
        let (shortWhole, keptShort) := ({} : Build.Kept).take
          { going with witness := { witness with nodes := witness.nodes.eraseIdx! lacked } }
        let ((short, _, _), _, beforeShort, _) := run shortWhole none
        let (mended, _) := keptShort.take { goingBare with witness := { goingBare.witness with nodes := #[witness.nodes[lacked]!] } }
        let ((whole, _, _), _, _, _) := run mended beforeShort
        match whole.built with
        | some b =>
          tally ← tally.expect s!"{name}: with the node it lacked given, the block that went on is not accepted, or has less"
            (accepted witness template b && b.included.length ≥ (short.built.map (·.included.length)).getD 0
              && (beforeShort.isSome || whole.encode == again.encode))
        | none => tally ← tally.expect s!"{name}: with the node it lacked given, status {whole.status}" (whole.status == 6)
      match Build.Request.encode asked, Build.Request.encode { asked with seen := some true }, Build.Request.encode going with
      | some encoded, some forgetting, some goingOn =>
        let read (bytes : ByteArray) : Option Build.Request := ((Build.request bytes).run 0).map (·.1)
        tally ← tally.expect s!"{name}: read with what was sent before, the request as bytes is answered differently"
          (Build.serve encoded == again.encode && Build.serve forgetting == again.encode && Build.serve goingOn == again.encode
            && encoded.extract 0 6 == "JBLF2".toUTF8 ++ ⟨#[0]⟩ && forgetting.extract 0 6 == "JBLF2".toUTF8 ++ ⟨#[1]⟩
            && goingOn.extract 0 6 == "JBLF2".toUTF8 ++ ⟨#[2]⟩ && goingOn.extract 6 goingOn.size == encoded.extract 6 encoded.size
            && (read goingOn).map (fun r => (r.goesOn, r.seen)) == some (true, some false)
            && (read encoded).map (·.goesOn) == some false && (read forgetting).map (·.goesOn) == some false
            && Build.serve ("JBLF2".toUTF8 ++ ⟨#[3]⟩ ++ encoded.extract 6 encoded.size) == ({ status := 5 } : Build.Response).encode)
      | _, _, _ => tally ← tally.expect s!"{name}: the request has no encoding" false
  | none => tally ← tally.expect s!"{name}: nothing built from the block's own transactions, status {again.status}" false
  -- What the parent fixes is worked out here, whatever the sender put.
  let h := template.header
  let wrongHeader : Header :=
    { h with
      baseFeePerGas := h.baseFeePerGas.map fun fee => fee + 7
      excessBlobGas := h.excessBlobGas.map fun excess => excess + 131072
      stateRoot := 5
      gasUsed := 9 }
  let wrong : Block := { template with header := wrongHeader }
  let righted := Build.run
    { witness := { witness with block := wrong.toRlpItem.toBytes.toByteArray }, rule := 0, gasCap := limit, engine }
  tally ← tally.expect s!"{name}: a wrong base fee and excess blob gas in the template were not put right"
    ((righted.built.map fun b => b.hash == hash) == some true)
  -- A transaction that cannot go in.
  if let first :: _ := template.transactions then
    let doubled := { template with transactions := template.transactions ++ [first] }
    let twice := Build.run
      { witness := { witness with block := doubled.toRlpItem.toBytes.toByteArray }, rule := 0, gasCap := limit, engine }
    tally ← tally.expect s!"{name}: a transaction proposed twice was not left out the second time"
      ((twice.built.map fun b => b.hash == hash && b.included.length == count) == some true)
  -- Built by the rule.
  let started ← IO.monoMsNow
  let ruled := Build.run { witness, rule := 1, gasCap := limit, engine }
  let ruledTook := (← IO.monoMsNow) - started
  let mut went := 0
  match ruled.built with
  | some b =>
    went := b.included.length
    tally ← tally.expect s!"{name}: the block built by the rule is not one the checker accepts"
      (accepted witness template b)
  | none =>
    -- With the order changed the witness may not reach: that is an answer, and it is said.
    tally ← tally.expect s!"{name}: by the rule, status {ruled.status}" (ruled.status == 6)
  -- Out of time before the first transaction, and half way through: what was in by then is a whole block,
  -- one the checker accepts, and nothing after it went in. (`over` is asked before each transaction; here
  -- it counts how often.) Ending early can need a node of the witness that the whole block did not, and
  -- then the answer is that, said.
  for k in [0, count / 2] do
    let over : StateM Nat Bool := modifyGet fun asked => (asked ≥ k, asked + 1)
    let ((cut, _, _), _) := (Build.runWith over { witness, rule := 0, gasCap := limit, engine }).run 0
    match cut.built with
    | some b =>
      tally ← tally.expect s!"{name}: out of time after {k} transactions, {b.included.length} went in, or the \
        checker does not accept the block" (b.included == List.range k && accepted witness template b)
    | none => tally ← tally.expect s!"{name}: out of time after {k} transactions, status {cut.status}" (cut.status == 6)
  if write && !engine then
    if let some encoded := Build.Request.encode { witness, rule := 1, gasCap := limit, engine } then
      IO.FS.createDirAll "fixtures/build"
      IO.FS.writeBinFile s!"fixtures/build/{name}.req" encoded
      IO.FS.writeBinFile s!"fixtures/build/{name}.expected" ruled.encode
  IO.println s!"{name}: {count} transactions; as given {took} ms; by the rule {went} went in \
    (status {ruled.status}), {ruledTook} ms"
  -- The engine, with a node of the witness left out, for a block too big to try every node of: eight
  -- of them, spread over the witness, each under both rules. What the engine could not read it must
  -- not remember as anything: a transaction after the one left out, reading the same slot or
  -- account, is then left out too, and the block is one the checker accepts with the whole witness.
  if engine && !shorten && witness.nodes.size ≥ 8 then
    let mut smaller := 0
    let mut nothing := 0
    for turn in [0:8] do
      let lacked := turn * (witness.nodes.size / 8) + witness.nodes.size / 16
      for rule in [0, 1] do
        let answer := Build.run { witness := { witness with nodes := witness.nodes.eraseIdx! lacked }, rule, gasCap := limit, engine }
        match answer.built with
        | some b =>
          if b.included.length < count then smaller := smaller + 1
          tally ← tally.expect s!"{name}: without node {lacked}, rule {rule}, a block was built that the checker \
            does not accept" (accepted witness template b)
        | none =>
          nothing := nothing + 1
          tally ← tally.expect s!"{name}: without node {lacked}, rule {rule}, status {answer.status}"
            (answer.status == 4 || answer.status == 6 || answer.status == 7)
    IO.println s!"{name}: 16 witnesses with a node left out; {nothing} built nothing, {smaller} built a smaller block"
  -- A witness that falls short.
  if shorten then
    let mut variants : List (String × Stateless.Request) := []
    for i in [0 : witness.nodes.size] do
      variants := (s!"node {i}", { witness with nodes := witness.nodes.eraseIdx! i }) :: variants
    for i in [0 : witness.keys.length] do
      variants := (s!"key {i}", { witness with keys := witness.keys.eraseIdx i }) :: variants
    for i in [0 : witness.codes.length] do
      variants := (s!"code {i}", { witness with codes := witness.codes.eraseIdx i }) :: variants
    let mut smaller := 0
    let mut nothing := 0
    for (left, short) in variants do
      for rule in [0, 1] do
        let answer := Build.run { witness := short, rule, gasCap := limit, engine }
        match answer.built with
        | some b =>
          if b.included.length < count then smaller := smaller + 1
          tally ← tally.expect s!"{name}: without {left}, rule {rule}, a block was built that the checker \
            does not accept" (accepted witness template b)
        | none =>
          nothing := nothing + 1
          tally ← tally.expect s!"{name}: without {left}, rule {rule}, status {answer.status}"
            (answer.status == 4 || answer.status == 6 || answer.status == 7)
    IO.println s!"{name}: {2 * variants.length} shortened witnesses; {nothing} built nothing, {smaller} built a \
      smaller block"
  pure tally

/-- A block of the real chain built by the rule with every `step`th address left out of the witness in
turn: nothing built, or a block the checker accepts with the whole witness. -/
def real (engine : Bool) (name : String) (bytes : ByteArray) (step : Nat) (tally : Tally) : IO Tally := do
  let mut tally := tally
  let name := (if engine then "the engine: " else "") ++ name
  let some (witness, _) := (Stateless.request bytes).run 0
    | tally.expect s!"{name}: not a stateless request" false
  let .ok (template, _) := rlpToBlockE witness.block.toList
    | tally.expect s!"{name}: the block does not decode" false
  let addresses := (witness.keys.filter (·.size == 20)).toArray
  let whole := (Build.run { witness, rule := 1, gasCap := template.header.gasLimit, engine }).built.map (·.included.length)
  let mut smaller := 0
  let mut nothing := 0
  let mut tried := 0
  for turn in [0 : (addresses.size + step) / (step + 1)] do
    let left := addresses[turn * (step + 1)]!
    let short := { witness with keys := witness.keys.filter (· != left) }
    let answer := Build.run { witness := short, rule := 1, gasCap := template.header.gasLimit, engine }
    tried := tried + 1
    match answer.built with
    | some b =>
      if some b.included.length != whole then smaller := smaller + 1
      tally ← tally.expect s!"{name}: without the address {Stateless.hexOf left.toList} a block was built \
        that the checker does not accept" (accepted witness template b)
    | none =>
      nothing := nothing + 1
      tally ← tally.expect s!"{name}: without the address {Stateless.hexOf left.toList}, status {answer.status}"
        (answer.status == 4 || answer.status == 6 || answer.status == 7)
  IO.println s!"{name}: {tried} of {addresses.size} addresses left out in turn; {nothing} built nothing, \
    {smaller} built a different block, each one the checker accepts"
  pure tally

/-- How long a sealed transaction is kept (`Evm/Seal.lean`): to its last slot, and never when that slot is
more than an hour on from the slot a block is asked for. -/
def sealedFor (tally : Tally) : IO Tally := do
  let kept (last : Nat) : Evm.Seal.Kept := { last, wire := ByteArray.mk #[2, 0] }
  let pool : Evm.Seal.Pool := { kept := #[kept 99, kept 100, kept 250, kept 400, kept 401, kept 100000] }
  let (after, tried) := pool.forSlot 100
  let mut tally := tally
  tally ← tally.expect "a sealed transaction is tried up to its last slot and not past it"
    ((kept 100).good 100 && (kept 100).good 99 && !(kept 100).good 101)
  tally ← tally.expect "one whose last slot is an hour on is tried, and one a slot further is not"
    ((kept 400).good 100 && !(kept 401).good 100 && (kept 401).good 101)
  tally ← tally.expect "a pool asked for a slot keeps those and drops the rest"
    (after.kept.map (·.last) == #[100, 250, 400] && tried.size == 3)
  return tally

/-- The order of rule 1 as it was first written: the fronts of the signers' queues found anew from every
pair of waiting transactions, for each transaction taken. Slow, and plainly what the rule says; kept here
as what `Build.byTip` must agree with. -/
partial def byTipByPairs (waiting : List Build.Candidate) (out : Array Build.Candidate := #[]) : Array Build.Candidate :=
  let front := waiting.filter fun c => waiting.all fun d =>
    d.sender != c.sender || d.tx.nonce > c.tx.nonce || (d.tx.nonce == c.tx.nonce && d.place ≥ c.place)
  match front with
  | [] => out
  | first :: rest =>
    let best := rest.foldl (fun b c => if c.tip > b.tip || (c.tip == b.tip && c.place < b.place) then c else b) first
    byTipByPairs (waiting.filter (·.place != best.place)) (out.push best)

/-- `Build.byTip` against that, on lists made up so that signers, nonces and tips each repeat: many signers
with one transaction, one signer with many, the same nonce twice from one signer, everything paying the
same. -/
def ordered (tally : Tally) : IO Tally := do
  let mut tally := tally
  let mut seed := 20261125
  for (count, signers, nonces, tips) in
      [(0, 1, 1, 1), (1, 1, 1, 1), (40, 1, 40, 5), (40, 1, 3, 1), (60, 7, 4, 3), (120, 30, 6, 1000), (200, 200, 1, 2),
       (150, 3, 2, 2), (400, 150, 5, 50)] do
    let mut list : List Build.Candidate := []
    for place in [0:count] do
      seed := (seed * 1103515245 + 12345) % 2147483648
      let drawn := seed / 4096
      let tx : Transaction :=
        { nonce := ((drawn / 7) % nonces).toUInt64, gasLimit := 21000, value := 0, data := [], v := 0, r := [], s := [],
          type := .legacy 1 none }
      list := { place, tx, sender := ((drawn % signers).toUInt32, (0, 0)), tip := (drawn / 1000) % tips } :: list
    let waiting := list.reverse
    let got := (Build.byTip waiting).map (·.place)
    tally ← tally.expect s!"the order by tip of {count} transactions from {signers} signers is the rule's"
      (got == (byTipByPairs waiting).map (·.place) && got.size == count)
  return tally

/-- What the engine's world could not be told it does not remember as anything (`Fast/State.lean`). A
transaction that asks for a slot or an account nothing can answer for is undone, and after the undoing
the world must hold of that slot and that account what it held before: nothing. (Until 2026-11-26 it
held a slot of nothing, and an account that was not there, and the next transaction to ask was told
so.) What was written before the question is undone as ever, and what was fetched and answered stays. -/
def worldChecks (tally : Tally) : IO Tally := do
  let known : Fast.Word := Fast.Word.ofNat 0x1111
  let other : Fast.Word := Fast.Word.ofNat 0x2222
  let key : Fast.Word := Fast.Word.ofNat 7
  let proven : Fast.Word := Fast.Word.ofNat 8
  let backing : Fast.Backing :=
    { account := fun a =>
        if a == known then .found { nonce := 3, balance := Fast.Word.ofNat 100, codeHash := Fast.emptyCodeHash,
                                    storageEmpty := false, storage := Fast.Word.ofNat 1 }
        else .missing
      slot := fun _ slot => if slot == proven then .found (Fast.Word.ofNat 9) else .missing
      code := fun _ => none }
  let world := Fast.World.new backing
  let mark := world.checkpoint
  -- Written before anything went unanswered: undone by the journal.
  let (world, held) := world.slot known proven
  let world := world.setSlot known proven held (Fast.Word.ofNat 10)
  -- A slot nothing answers for, read and then written; an account nothing answers for, paid.
  let (world, lacked) := world.slot known key
  let world := world.setSlot known key lacked (Fast.Word.ofNat 5)
  let world := world.credit other (Fast.Word.ofNat 1)
  let marked := world.missing
  let world := world.revert mark
  let (again, slot) := ({ world with missing := false, lacks := #[] }).slot known key
  let (again, account) := again.account other
  let (_, kept) := again.slot known proven
  tally.expect "the engine's world remembers a slot or an account it could not be told"
    (marked && !world.slots.contains ⟨known, key⟩ && !world.accounts.contains other && again.missing
      && slot.value.isZero && !account.present
      && world.accounts.contains known && kept.value == Fast.Word.ofNat 9)

def main (args : List String) : IO UInt32 := do
  let mut tally : Tally := {}
  tally ← worldChecks tally
  tally ← sealedFor tally
  tally ← ordered tally
  -- Every case is put to Jaune's builder and then to the fast engine's.
  for engine in [false, true] do
    for name in ["highGasUsage-11", "wallet2outOf3txsRevokeAndConfirmAgain-8", "DelegateCallSpam-1"] do
      tally ← one engine name (← IO.FS.readBinFile s!"fixtures/stateless/{name}.req") true tally (args == ["write"])
  -- `build-test real DIR [STEP]`: only the blocks of the real chain in DIR, with addresses left out.
  if let "real" :: dir :: rest := args then
    let step := (rest.head?.bind String.toNat?).getD 10 - 1
    let entries := (← System.FilePath.readDir dir).filter (·.fileName.endsWith ".req")
    for engine in [false, true] do
      for entry in entries.qsort (·.fileName < ·.fileName) do
        tally ← real engine ((entry.fileName.splitOn ".req").headD entry.fileName) (← IO.FS.readBinFile entry.path) step tally
    if tally.failures == 0 then IO.println s!"build-test: all {tally.checks} checks passed"
    else IO.println s!"build-test: {tally.failures} of {tally.checks} FAILED"
    return if tally.failures == 0 then 0 else 1
  if let [dir] := args.filter (· != "write") then
    let entries := (← System.FilePath.readDir dir).filter (·.fileName.endsWith ".req")
    for engine in [false, true] do
      for entry in entries.qsort (·.fileName < ·.fileName) do
        tally ← one engine ((entry.fileName.splitOn ".req").headD entry.fileName) (← IO.FS.readBinFile entry.path) false tally
  if tally.failures == 0 then IO.println s!"build-test: all {tally.checks} checks passed"
  else IO.println s!"build-test: {tally.failures} of {tally.checks} FAILED"
  return if tally.failures == 0 then 0 else 1
