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
* `merge` applies the decoded batches over a base dataset, in log order, entry
  by entry (`applyEntry`, the replay step of `SPARQL.StoreEndpoint`).

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

/-- The log ended with a record that did not verify (a torn write, or bytes
that changed after the write). -/
def LogRead.torn (r : LogRead) : Bool := !r.rest.isEmpty

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
nothing, so its entry changes nothing. -/
def applyEntry (ds : Dataset) (e : DeltaEntry) : Dataset :=
  let withIri (g : Iri) (k : WfIri → Dataset) : Dataset :=
    if h : isIri g then k ⟨g, h⟩ else ds
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

/-- Merge on read: decode the log and apply the batches of the records that
verify over `base`. A torn or corrupted record, and every byte after it,
changes nothing. -/
def merge (base : Dataset) (log : List UInt8) : Dataset :=
  applyBatches base (decode log).batches

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
  { seq := 1, epoch := 0, ops := [.add frank (some exG.val), .remove eve none, .create exG.val] }
private def b2 : DeltaBatch := { seq := 2, epoch := 3, ops := [.clear none, .drop exG.val] }

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
-- A wrong magic in the first record: nothing is read.
#guard (decode (0 :: log3.drop 1)).batches == []
#guard (decode (0 :: log3.drop 1)).torn

-- Bytes that are not a record at all.
#guard decode [0x44, 0x4C, 0x42] == { batches := [], rest := [0x44, 0x4C, 0x42] }

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

end L4Factoidal.Storage.BrowserLog
