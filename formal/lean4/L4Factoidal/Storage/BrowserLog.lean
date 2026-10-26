/-
L4Factoidal.Storage.BrowserLog — the durable update log of a browser host
(hub post 18, https://github.com/danbri/factoidal/issues/728).

A page keeps its SPARQL Update history in IndexedDB: one record for each
committed update request. The host stores bytes and loads bytes, and does
nothing else. This module makes every decision about the bytes. It does no
I/O.

* `encodeBatch?` gives the bytes of one record: the DLB1 frame of one
  `DeltaBatch` (`Storage.DeltaLog.serializeDeltaBatch?`, the format of the F*
  `RDF.Store.Columnar.DeltaLog.serialize_delta_batch`), little-endian:

      magic u32 'DLB1' | version u32 = 1 | body length u32 | body | checksum u32

  The body is seq u64, epoch u64, entry count u32, then the entries. Each
  entry is a DLE1 frame of the same shape (magic 'DLE1') around one
  `DeltaEntry` payload. Each checksum is the sum of the bytes it covers,
  modulo 2^32 (`simpleChecksum`).
* A log is the records in commit order, concatenated. These are the bytes that
  a Shardborough `deltas.dlog` holds after its eight-byte DLOG header
  (`BrowserLogTheorems.parseLog_header_append`).
* `decode` reads one record after the other until a record does not verify.
  It answers the batches it read and the bytes from the first record that
  failed (`LogRead.rest`). The decoder does not apply any entry of a torn or
  corrupted record, and it does not read past that record: a later batch can
  depend on an earlier one, so a log is replayed as a prefix only.
* `LogRead.tail` says what those bytes are (`Storage.classifyTail`,
  https://github.com/danbri/factoidal/issues/843): a torn final record (an
  append that did not complete) is a crash artifact, and the records before it
  are the log; a damaged record, or a record whose checksum verifies and whose
  entries do not decode, is an error (`LogRead.error?`), because the records
  after it would be lost without a message.
* `mergeChecked` applies the decoded batches over a base dataset, in log
  order, entry by entry (`applyEntry`, the replay step of
  `SPARQL.StoreEndpoint`), or gives that error. `merge` is the same without
  the check.

The decoders are loops. `decodeGo` reads one record in each iteration and
`entriesLoop` one entry, each with an accumulator, so the depth of the C stack
does not grow with the number of records or entries (CLAUDE.md, decoders over
input-proportional data). `BrowserLogTheorems` proves them equal to the
store's `parseDeltaBatch` and `replayDeltaBatches`, and proves the three
properties the host relies on: decode inverts encode, a log whose last record
does not verify decodes to exactly the earlier batches, and a merge equals
applying the batches one by one.
-/
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.SPARQL.Update

namespace L4Factoidal.Storage.BrowserLog

open L4Factoidal.RDF
open L4Factoidal.Storage

/-! ## Encoding -/

/-- The bytes of one record: the DLB1 frame of `b`. `none` when the batch does
not fit the wire format: a seq or epoch of 2^64 or more, 2^32 entries or
more, a string of 2^32 bytes or more, an RDF 1.2 triple term, or a literal
with a base direction (`serializeDeltaBatch?`). -/
def encodeBatch? (b : DeltaBatch) : Option (List UInt8) := serializeDeltaBatch? b

/-- The bytes of a log of `bs`: the records of the batches, concatenated in
order. `none` when one batch does not fit the wire format. -/
def encodeLog? (bs : List DeltaBatch) : Option (List UInt8) :=
  (bs.mapM encodeBatch?).map List.flatten

/-! ## Decoding, as loops -/

/-- `parseNFramedDeltaEntries` as a loop: `acc` holds the entries read so far,
the last one first. -/
def entriesLoop : Nat → List UInt8 → List DeltaEntry → Option (List DeltaEntry × List UInt8)
  | 0, bs, acc => some (acc.reverse, bs)
  | n + 1, bs, acc =>
    match parseFramedDeltaEntry bs with
    | none => none
    | some (e, rest) => entriesLoop n rest (e :: acc)

/-- `parseDeltaBatchBody`, with the entries read by `entriesLoop`. -/
def parseBody (bs : List UInt8) : Option DeltaBatch := do
  let seq ← readU64LE bs 0
  let epoch ← readU64LE bs 8
  let count ← readU32LE bs 16
  let (ops, tail) ← entriesLoop count.toNat (bs.drop 20) []
  if tail.isEmpty then some { seq := seq.toNat, epoch := epoch.toNat, ops } else none

/-- `parseDeltaBatch`, with the body read by `parseBody`: one record and the
bytes after it, or `none` when the record does not verify (a wrong magic or
version, fewer bytes than the length field says, a checksum that is not the
sum of the body, or a body that is not exactly its entries). -/
def parseBatch (bs : List UInt8) : Option (DeltaBatch × List UInt8) := do
  let magic ← readU32LE bs 0
  if magic != deltaBatchMagic then none else
  let version ← readU32LE bs 4
  if version != deltaBatchVersion then none else
  let bodyLen ← readU32LE bs 8
  let afterHeader := bs.drop 12
  let body := afterHeader.take bodyLen.toNat
  if body.length != bodyLen.toNat then none else
  let checksum ← readU32LE afterHeader bodyLen.toNat
  if checksum != simpleChecksum body then none else
  let batch ← parseBody body
  some (batch, (afterHeader.drop bodyLen.toNat).drop 4)

/-- What a decode found: the batches of the records that verified, in log
order, and the bytes from the first record that did not verify. `rest` is
empty exactly when every record verified. -/
structure LogRead where
  batches : List DeltaBatch
  rest : List UInt8
  deriving Repr, DecidableEq

/-- What the bytes from the first record that did not verify are
(`Storage.classifyTail`, https://github.com/danbri/factoidal/issues/843). -/
def LogRead.tail (r : LogRead) : LogTail := classifyTail r.rest

/-- The log ends with a torn final record: an append that did not complete
(the record is cut short, or it is complete and fails its checksum). -/
def LogRead.torn (r : LogRead) : Bool := r.tail == .torn

/-- Why a reader must stop, when the bytes after the records that verified are
not a torn final record: a damaged record (a wrong magic or version, or a
checksum that fails in a record that is not the last one), or a record whose
checksum verifies and whose entries do not decode. `logLength` is the byte
length of the decoded log. -/
def LogRead.error? (r : LogRead) (logLength : Nat) : Option String :=
  if r.tail.recoverable then none
  else some (r.tail.text (logLength - r.rest.length) r.rest.length)

/-- The decode loop: one record in each iteration, `acc` holding the batches
read so far, the last one first. The fuel is the byte length of the log; each
record that verifies is at least 16 bytes long, so the fuel never runs out
first (`decodeGo_fuel`). -/
def decodeGo : Nat → List UInt8 → List DeltaBatch → LogRead
  | 0, bs, acc => { batches := acc.reverse, rest := bs }
  | fuel + 1, bs, acc =>
    match bs with
    | [] => { batches := acc.reverse, rest := [] }
    | b :: bs' =>
      match parseBatch (b :: bs') with
      | none => { batches := acc.reverse, rest := b :: bs' }
      | some (batch, rest) => decodeGo fuel rest (batch :: acc)

/-- Decode a log: the batches of the records that verify, read from the
start, and the bytes from the first record that does not. -/
def decode (bs : List UInt8) : LogRead := decodeGo bs.length bs []

/-! ## Merge -/

/-- Replay one entry over a dataset. This is the definition of
`SPARQL.StoreEndpoint.applyDeltaEntry`, the replay step of the served store;
`BrowserLogTests` proves the two equal. A graph name that is not an IRI names
nothing, so its entry changes nothing. A graph named by a blank node is in no
entry of this log: its version 1 codec refuses one (`serializeGraphOpt?`), and
only a DLOG of version 3 holds one. -/
def applyEntry (ds : Dataset) (e : DeltaEntry) : Dataset :=
  let withIri (g : DeltaGraphName) (k : WfIri → Dataset) : Dataset :=
    match g with
    | .iri i => if h : isIri i then k ⟨i, h⟩ else ds
    | .bnode _ => ds
  match e with
  | .add t none => L4Factoidal.RDF.Dataset.insertQuad ds (none, t)
  | .add t (some g) => withIri g fun i => L4Factoidal.RDF.Dataset.insertQuad ds (some i, t)
  | .remove t none => L4Factoidal.RDF.Dataset.deleteQuad ds (none, t)
  | .remove t (some g) => withIri g fun i => L4Factoidal.RDF.Dataset.deleteQuad ds (some i, t)
  | .clear none => { ds with default := [] }
  | .clear (some g) => withIri g fun i =>
      if L4Factoidal.RDF.Dataset.hasGraph i ds then L4Factoidal.RDF.Dataset.setGraph i [] ds else ds
  | .drop g => withIri g fun i => L4Factoidal.RDF.Dataset.dropGraph i ds
  | .create g => withIri g fun i => L4Factoidal.RDF.Dataset.ensureGraph i ds

/-- Apply the entries of one batch, in order. -/
def applyBatch (ds : Dataset) (b : DeltaBatch) : Dataset := b.ops.foldl applyEntry ds

/-- Apply batches one by one, in order. -/
def applyBatches (ds : Dataset) (bs : List DeltaBatch) : Dataset := bs.foldl applyBatch ds

/-! ## Merge through graph indexes

`applyEntry` adds a triple with `Dataset.insertQuad`, which scans and copies
the graph, so merging a log of n distinct triples took time in n²
(https://github.com/danbri/factoidal/issues/822). `applyBatchesFast` carries a
`DatasetIx` (`SPARQL/Update.lean`) through all the batches: an add is
`DatasetIx.insertQuad`, which makes a hash set of the graph on its second add;
any other entry is `applyEntry` on the dataset the index holds. It gives the
dataset `applyBatches` gives (`applyBatches_eq_fast`, `csimp`), so `merge`
runs it and the theorems of `BrowserLogTheorems.lean` hold for it. -/

/-- `applyEntry` on the index. -/
def applyEntryIx (d : DatasetIx) (e : DeltaEntry) : DatasetIx :=
  match e with
  | .add t none => d.insertQuad (none, t)
  | .add t (some (.iri g)) => if h : isIri g then d.insertQuad (some ⟨g, h⟩, t) else d
  | e => DatasetIx.ofDataset (applyEntry d.toDataset e)

theorem toDataset_applyEntryIx (d : DatasetIx) (e : DeltaEntry) :
    (applyEntryIx d e).toDataset = applyEntry d.toDataset e := by
  unfold applyEntryIx
  split
  · simp [DatasetIx.toDataset_insertQuad, applyEntry]
  · split <;> simp_all [DatasetIx.toDataset_insertQuad, applyEntry]
  · simp

theorem toDataset_foldl_applyEntryIx (es : List DeltaEntry) (d : DatasetIx) :
    (es.foldl applyEntryIx d).toDataset = es.foldl applyEntry d.toDataset := by
  induction es generalizing d with
  | nil => rfl
  | cons e es ih => simp only [List.foldl_cons, ih, toDataset_applyEntryIx]

theorem toDataset_foldl_batchIx (bs : List DeltaBatch) (d : DatasetIx) :
    (bs.foldl (fun d b => b.ops.foldl applyEntryIx d) d).toDataset =
      bs.foldl applyBatch d.toDataset := by
  induction bs generalizing d with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.foldl_cons, ih, toDataset_foldl_applyEntryIx, applyBatch]

/-- What runs in place of `applyBatches`. -/
def applyBatchesFast (ds : Dataset) (bs : List DeltaBatch) : Dataset :=
  (bs.foldl (fun d b => b.ops.foldl applyEntryIx d) (DatasetIx.ofDataset ds)).toDataset

@[csimp] theorem applyBatches_eq_fast : @applyBatches = @applyBatchesFast := by
  funext ds bs
  simp [applyBatches, applyBatchesFast, toDataset_foldl_batchIx]

#print axioms applyBatches_eq_fast

/-- Apply the batches of the records that verify over `base`. A record that
does not verify, and every byte after it, changes nothing. This does not check
what those bytes are: a reader calls `mergeChecked`. -/
def merge (base : Dataset) (log : List UInt8) : Dataset :=
  applyBatches base (decode log).batches

/-- Merge on read, with the rule of https://github.com/danbri/factoidal/issues/843:
the merge of the records that verify when the log is clean or ends with a torn
final record; an error when a record is damaged or a committed record does not
decode, because the records after it would be lost without a message. -/
def mergeChecked (base : Dataset) (log : List UInt8) : Except String Dataset :=
  match (decode log).error? log.length with
  | some e => .error e
  | none => .ok (merge base log)

/-! ## Build-time checks

Each round trip is checked with bytes after the log, so that a decoder that
reads too far fails the check. -/

private def exS : WfIri := ⟨"http://example.org/eve", by decide⟩
private def exP : WfIri := ⟨"http://xmlns.com/foaf/0.1/name", by decide⟩
private def exG : WfIri := ⟨"http://example.org/g", by decide⟩

private def eve : Triple := ⟨.iri exS, exP, .literal (Literal.string "Eve")⟩
private def frank : Triple := ⟨.iri exS, exP, .literal (Literal.langString "Frank" "en")⟩

private def b0 : DeltaBatch := { seq := 0, epoch := 0, ops := [.add eve none] }
private def b1 : DeltaBatch :=
  { seq := 1, epoch := 0, ops := [.add frank (some (.iri exG.val)), .remove eve none, .create (.iri exG.val)] }
private def b2 : DeltaBatch := { seq := 2, epoch := 3, ops := [.clear none, .drop (.iri exG.val)] }

private def log3 : List UInt8 := (encodeLog? [b0, b1, b2]).getD []

-- The encoder admits the three batches, and the log decodes back to them.
#guard (encodeLog? [b0, b1, b2]).isSome
#guard decode log3 == { batches := [b0, b1, b2], rest := [] }
#guard !(decode log3).torn
-- The loop decoder and the store's replay answer the same.
#guard (decode log3).batches == (replayDeltaBatches log3).1
#guard parseBatch log3 == parseDeltaBatch log3
-- An empty log has no batches and is not torn.
#guard decode [] == { batches := [], rest := [] }

-- The last record loses its checksum (the four bytes post 18's test hook cuts):
-- the first two batches survive and the torn bytes are reported.
private def frame2 : List UInt8 := (encodeBatch? b2).getD []
private def cut : List UInt8 := log3.take (log3.length - 4)
#guard (decode cut).batches == [b0, b1]
#guard (decode cut).torn
#guard (decode cut).rest == frame2.take (frame2.length - 4)
-- One body byte of the last record changed: its checksum rejects it.
private def flipped : List UInt8 :=
  log3.set (log3.length - 8) (log3.getD (log3.length - 8) 0 + 1)
#guard (decode flipped).batches == [b0, b1]
#guard (decode flipped).torn
-- A wrong magic in the first record: nothing is read, and the record is
-- damaged, not torn (issue 843).
#guard (decode (0 :: log3.drop 1)).batches == []
#guard (decode (0 :: log3.drop 1)).tail == .damaged
#guard !(decode (0 :: log3.drop 1)).torn

-- The start of a record (an append cut after three bytes): torn.
#guard decode [0x44, 0x4C, 0x42] == { batches := [], rest := [0x44, 0x4C, 0x42] }
#guard (decode [0x44, 0x4C, 0x42]).torn

-- One body byte of the FIRST record changed: the checksum rejects it, and two
-- committed records follow it, so the log is damaged (issue 843).
private def frame0 : List UInt8 := (encodeBatch? b0).getD []
private def damagedFirst : List UInt8 :=
  log3.set (frame0.length - 8) (log3.getD (frame0.length - 8) 0 + 1)
#guard (decode damagedFirst).batches == []
#guard (decode damagedFirst).tail == .damaged
#guard ((decode damagedFirst).error? damagedFirst.length).isSome
#guard ((decode cut).error? cut.length).isNone
#guard ((decode flipped).error? flipped.length).isNone
#guard ((decode log3).error? log3.length).isNone

-- A committed record whose checksum verifies and whose one entry has the
-- unknown entry tag 9: undecodable, also when it is the last record.
private def unknownRecord : List UInt8 :=
  let body := writeU64LE 3 ++ writeU64LE 0 ++ writeU32LE 1 ++ frameEntry [9]
  batchFrameStart ++ writeU32LE (UInt32.ofNat body.length) ++ body ++
    writeU32LE (simpleChecksum body)
#guard (decode (log3 ++ unknownRecord)).batches == [b0, b1, b2]
#guard (decode (log3 ++ unknownRecord)).tail == .undecodable
#guard (decode (unknownRecord ++ log3)).tail == .undecodable

-- The encoder refuses a triple term rather than write a record it cannot read.
private def withTripleTerm : DeltaBatch :=
  { seq := 0, epoch := 0, ops := [.add ⟨.iri exS, exP, .tripleTerm (.iri exS) exP (.iri exS)⟩ none] }
#guard (encodeBatch? withTripleTerm).isNone

-- Merge: Eve is added in batch 0, then removed in batch 1, which also adds
-- Frank to graph g; batch 2 clears the default graph and drops g.
private def base : Dataset := Dataset.empty
#guard (merge base ((encodeLog? [b0]).getD [])).default == [eve]
#guard (merge base ((encodeLog? [b0, b1]).getD [])).default == []
#guard (merge base ((encodeLog? [b0, b1]).getD [])).named ==
  [{ name := .iri exG, graph := [frank] }]
#guard merge base log3 == { default := [], named := [] }
-- The torn last record changes nothing: the merge is that of the first two.
#guard merge base cut == merge base ((encodeLog? [b0, b1]).getD [])
#guard merge base cut != merge base log3

-- The checked merge (issue 843): the same answers for a clean log and for a
-- torn final record; an error for a damaged record or an undecodable one.
private def mergedIs (log : List UInt8) (want : Option Dataset) : Bool :=
  match mergeChecked base log, want with
  | .ok got, some w => got == w
  | .error _, none => true
  | _, _ => false
#guard mergedIs log3 (some (merge base log3))
#guard mergedIs cut (some (merge base ((encodeLog? [b0, b1]).getD [])))
#guard mergedIs flipped (some (merge base ((encodeLog? [b0, b1]).getD [])))
#guard mergedIs damagedFirst none
#guard mergedIs (log3 ++ unknownRecord) none
#guard mergedIs (log3 ++ unknownRecord ++ (encodeBatch? b0).getD []) none

end L4Factoidal.Storage.BrowserLog
