/-
L4Factoidal.Storage.DeltaLogBytes — the delta log (DLOG, DLB1, DLE1) read and
written on a `ByteArray`, without a `List UInt8` for the log
(https://github.com/danbri/factoidal/issues/857 and
https://github.com/danbri/factoidal/issues/851).

`Storage/DeltaLog.lean` is the specification: every codec function there works
on a `List UInt8`, a list cell for each byte of the log. That costs 24 bytes of
memory for each byte of the list, and the encoder and the decoder made several
copies of it: a batch of 35,919,852 bytes (the 101,632-solution update of the
olympics generation) took 12.6 s and 2,310,880 kB to encode (64 bytes of memory
for each byte of log), and opening a generation with that log took 3,152,224 kB
(88 bytes for each byte). The functions below do the same work on a
`ByteArray`, and `DeltaLogBytesTheorems.lean` proves each of them equal to its
specification.

## The decoder

The decoder reads the log by position. A window `[pos, stop)` of a byte array is
the list `win b pos stop` of the specification (`Windows` below), and every read
checks its position against `stop`. The framing (the DLOG header, the DLB1
frame, the DLE1 frame) is read in place. The payload of one entry, a hundred
bytes, is cut out as a list (`listOfRange`) and read by the specification's
payload decoder (`parseDeltaEntryPayloadWith`), so the term codecs of the two
DLOG versions are not repeated: the list that exists at any time is one payload,
not the log.

* `entryAt`, `entriesAt`, `bodyAt`, `batchAt`: a DLE1 frame, the entries of a DLB1
  body, the body, a DLB1 frame (`parseFramedDeltaEntryWith`,
  `parseNFramedDeltaEntriesWith`, `parseDeltaBatchBodyWith`, `parseDeltaBatchWith`).
* `replayBatchesAt`: the batches up to the first frame that does not verify, and
  the position of that frame (`replayDeltaBatchesWith`). `parseLogAt` is `parseLog`,
  `classifyAt` is `classifyTail`, `parseLogCheckedBA` is `parseLogChecked` and
  `parseLogCheckedV1BA` is `parseLogCheckedV1`.

## The encoder

`pushEntry?`, `pushEntries?` and `bodyBA?` append the DLE1 frames of the entries
to one buffer; `batchBA?` frames the body (DLB1) after a prefix (the DLOG header
of a new log); `appendPlanBA?` is `appendPlan?`. The only lists are the payload
of one entry. The checksums are loops over the buffer (`sumRange`).

## Loops

Every function that walks the log is a loop with an accumulator or a fuel, and
a tail call: the `tests/stack` case `sbm11-update-where` writes and reads a
batch of 48,000 entries under a 512 KB stack.
-/
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.NatBounds

namespace L4Factoidal.Storage.DeltaLogBytes

open L4Factoidal
open L4Factoidal.RDF
open L4Factoidal.Storage

/-! ## Windows and reads -/

/-- The bytes `[pos, stop)` of `b` as a list: the list the specification
    decodes. Used in statements only; no code builds it for a whole log. -/
def win (b : ByteArray) (pos stop : Nat) : List UInt8 :=
  (b.data.toList.drop pos).take (stop - pos)

/-- The little-endian `UInt32` at `pos`, when its four bytes lie below `stop`
    (`stop ≤ b.size`). `readU32LE` on the window. -/
def u32At? (b : ByteArray) (pos stop : Nat) : Option UInt32 :=
  if h : pos + 4 ≤ stop ∧ stop ≤ b.size then
    some ((b[pos]'(by omega)).toUInt32 ||| ((b[pos + 1]'(by omega)).toUInt32 <<< 8) |||
          ((b[pos + 2]'(by omega)).toUInt32 <<< 16) ||| ((b[pos + 3]'(by omega)).toUInt32 <<< 24))
  else none

/-- `readU64LE` on the window. -/
def u64At? (b : ByteArray) (pos stop : Nat) : Option UInt64 := do
  let lo ← u32At? b pos stop
  let hi ← u32At? b (pos + 4) stop
  pure (lo.toUInt64 ||| (hi.toUInt64 <<< 32))

/-- The bytes `[s, e)` as a list, built from the end (a loop; `e ≤ b.size`). -/
def listOfRangeGo (b : ByteArray) (s : Nat) : Nat → List UInt8 → List UInt8
  | 0, acc => acc
  | i + 1, acc => listOfRangeGo b s i (b.get! (s + i) :: acc)

def listOfRange (b : ByteArray) (s e : Nat) : List UInt8 := listOfRangeGo b s (e - s) []

/-- The additive checksum of `[i, e)`, added to `acc`: `simpleChecksum` of the
    window (a loop over the buffer). -/
def sumGo (b : ByteArray) (e : Nat) (i : Nat) (acc : UInt32) : UInt32 :=
  if h : i < e ∧ e ≤ b.size then
    sumGo b e (i + 1) (acc + (b[i]'(by omega)).toUInt32)
  else acc
termination_by e - i

def sumRange (b : ByteArray) (s e : Nat) : UInt32 := sumGo b e s 0

/-! ## The decoder -/

/-- One DLE1 frame at `pos` in the window ending at `stop`: the end of its
    payload and the position after the frame. `parseEntry` on the window. -/
def entryFrameAt? (b : ByteArray) (pos stop : Nat) : Option (Nat × Nat) :=
  match u32At? b pos stop with
  | none => none
  | some magic =>
    if magic != deltaEntryMagic then none
    else match u32At? b (pos + 4) stop with
      | none => none
      | some ver =>
        if ver != deltaEntryVersion then none
        else match u32At? b (pos + 8) stop with
          | none => none
          | some payloadLen =>
            let e := pos + 12 + payloadLen.toNat
            if e ≤ stop then
              match u32At? b e stop with
              | none => none
              | some stored => if stored != sumRange b (pos + 12) e then none else some (e, e + 4)
            else none

/-- One entry and the position after its frame. `parseFramedDeltaEntryWith` on
    the window. -/
def entryAt (tc : DeltaTermCodec) (b : ByteArray) (pos stop : Nat) : Option (DeltaEntry × Nat) :=
  match entryFrameAt? b pos stop with
  | none => none
  | some (e, next) =>
    match parseDeltaEntryPayloadWith tc (listOfRange b (pos + 12) e) with
    | none => none
    | some (entry, payloadRest) => if payloadRest.isEmpty then some (entry, next) else none

/-- `n` entries from `pos`, the last one read first in `acc`; the entries in
    order and the position after them. `parseNFramedDeltaEntriesWith`. -/
def entriesAt (tc : DeltaTermCodec) (b : ByteArray) (stop : Nat) :
    Nat → Nat → List DeltaEntry → Option (List DeltaEntry × Nat)
  | 0, pos, acc => some (acc.reverse, pos)
  | n + 1, pos, acc =>
    match entryAt tc b pos stop with
    | none => none
    | some (e, next) => entriesAt tc b stop n next (e :: acc)

/-- The body of a DLB1 frame, the window `[pos, stop)`. `parseDeltaBatchBodyWith`. -/
def bodyAt (tc : DeltaTermCodec) (b : ByteArray) (pos stop : Nat) : Option DeltaBatch :=
  match u64At? b pos stop with
  | none => none
  | some seq =>
    match u64At? b (pos + 8) stop with
    | none => none
    | some epoch =>
      match u32At? b (pos + 16) stop with
      | none => none
      | some count =>
        match entriesAt tc b stop count.toNat (pos + 20) [] with
        | none => none
        | some (ops, p) =>
          if stop ≤ p then some { seq := seq.toNat, epoch := epoch.toNat, ops } else none

/-- One DLB1 frame at `pos`: the end of its body and the position after the
    frame. -/
def batchFrameAt? (b : ByteArray) (pos stop : Nat) : Option (Nat × Nat) :=
  match u32At? b pos stop with
  | none => none
  | some magic =>
    if magic != deltaBatchMagic then none
    else match u32At? b (pos + 4) stop with
      | none => none
      | some version =>
        if version != deltaBatchVersion then none
        else match u32At? b (pos + 8) stop with
          | none => none
          | some bodyLen =>
            let e := pos + 12 + bodyLen.toNat
            if e ≤ stop then
              match u32At? b e stop with
              | none => none
              | some checksum =>
                if checksum != sumRange b (pos + 12) e then none else some (e, e + 4)
            else none

/-- One batch and the position after its frame. `parseDeltaBatchWith` on the
    window. -/
def batchAt (tc : DeltaTermCodec) (b : ByteArray) (pos stop : Nat) : Option (DeltaBatch × Nat) :=
  match batchFrameAt? b pos stop with
  | none => none
  | some (e, next) =>
    match bodyAt tc b (pos + 12) e with
    | none => none
    | some batch => some (batch, next)

/-- The batches from `pos` until a frame does not verify (the most recent
    first in `acc`), and the position of that frame. -/
def replayGo (tc : DeltaTermCodec) (b : ByteArray) (stop : Nat) :
    Nat → Nat → List DeltaBatch → List DeltaBatch × Nat
  | 0, pos, acc => (acc, pos)
  | fuel + 1, pos, acc =>
    if stop ≤ pos then (acc, pos)
    else match batchAt tc b pos stop with
      | none => (acc, pos)
      | some (batch, next) => replayGo tc b stop fuel next (batch :: acc)

/-- `replayDeltaBatchesWith` on the window: the batches in order and the
    position of the first frame that does not verify. -/
def replayBatchesAt (tc : DeltaTermCodec) (b : ByteArray) (pos stop : Nat) :
    List DeltaBatch × Nat :=
  let r := replayGo tc b stop (stop - pos) pos []
  (r.1.reverse, r.2)

/-- `parseLog` on the whole array: the batches and the position of the first
    frame that does not verify. -/
def parseLogAt (b : ByteArray) : Option (List DeltaBatch × Nat) :=
  match u32At? b 0 b.size with
  | none => none
  | some magic =>
    if magic != deltaLogMagic then none
    else match u32At? b 4 b.size with
      | none => none
      | some version =>
        if version == deltaLogVersion then some (replayBatchesAt .v1 b 8 b.size)
        else if version == deltaLogVersion2 then some (replayBatchesAt .v2 b 8 b.size)
        else none

/-- `logHeaderVersion?` on the whole array. -/
def logHeaderVersionAt? (b : ByteArray) : Option UInt32 :=
  match u32At? b 0 b.size with
  | none => none
  | some magic => if magic != deltaLogMagic then none else u32At? b 4 b.size

/-- `classifyTail` on the bytes from `p` to the end of `b`. -/
def classifyAt (b : ByteArray) (p : Nat) : LogTail :=
  if b.size ≤ p then .clean
  else
    match u32At? b (p + 8) b.size with
    | none =>
      if (listOfRange b p (min b.size (p + 8))).isPrefixOf batchFrameStart then .torn else .damaged
    | some len =>
      if listOfRange b p (p + 8) != batchFrameStart then .damaged
      else if b.size - p < 16 + len.toNat then .torn
      else if u32At? b (p + 12 + len.toNat) b.size == some (sumRange b (p + 12) (p + 12 + len.toNat))
        then .undecodable
      else if b.size - p == 16 + len.toNat then .torn
      else .damaged

/-- `parseLogChecked` on the whole array. -/
def parseLogCheckedBA (b : ByteArray) : Except String (List DeltaBatch × Bool) :=
  match parseLogAt b with
  | none => .error "the DLOG header is malformed or unsupported"
  | some (batches, p) =>
    match classifyAt b p with
    | .clean => .ok (batches, false)
    | .torn => .ok (batches, true)
    | k => .error (k.text (b.size - (b.size - p)) (b.size - p) ++
        "; the log is not replayed (https://github.com/danbri/factoidal/issues/843)")

/-- `parseLogCheckedV1` on the whole array. -/
def parseLogCheckedV1BA (b : ByteArray) : Except String (List DeltaBatch × Bool) :=
  if logHeaderVersionAt? b == some deltaLogVersion2 then
    .error ("the DLOG has header version 2 (its entries may hold RDF 1.2 terms); " ++
      "the SBM11 tools (l4sbm11) read it, and this reader of IBK3, IBK4 and IBK5 " ++
      "collections does not (https://github.com/danbri/factoidal/issues/792)")
  else parseLogCheckedBA b

/-! ## The encoder -/

/-- A little-endian `UInt32` appended to `out`. -/
def pushU32 (out : ByteArray) (n : UInt32) : ByteArray :=
  (((out.push n.toUInt8).push (n >>> 8).toUInt8).push (n >>> 16).toUInt8).push (n >>> 24).toUInt8

/-- A little-endian `UInt64` appended to `out`. -/
def pushU64 (out : ByteArray) (n : UInt64) : ByteArray :=
  pushU32 (pushU32 out n.toUInt32) (n >>> 32).toUInt32

/-- A list appended to `out`. -/
def pushList (out : ByteArray) : List UInt8 → ByteArray
  | [] => out
  | x :: xs => pushList (out.push x) xs

/-- The DLE1 frame of `payload` appended to `out`: `frameEntry payload`. -/
def pushEntryFrame (out : ByteArray) (payload : List UInt8) : ByteArray :=
  pushU32 (pushList (pushU32 (pushU32 (pushU32 out deltaEntryMagic) deltaEntryVersion)
    (UInt32.ofNat payload.length)) payload) (simpleChecksum payload)

/-- The frame of one entry appended to `out`: `serializeFramedDeltaEntryWith?`. -/
def pushEntry? (tc : DeltaTermCodec) (out : ByteArray) (e : DeltaEntry) : Option ByteArray :=
  match serializeDeltaEntryPayloadWith? tc e with
  | none => none
  | some payload => if payload.length < UInt32.size then some (pushEntryFrame out payload) else none

/-- The frames of the entries appended to `out`, in order. -/
def pushEntries? (tc : DeltaTermCodec) : ByteArray → List DeltaEntry → Option ByteArray
  | out, [] => some out
  | out, e :: es =>
    match pushEntry? tc out e with
    | none => none
    | some out' => pushEntries? tc out' es

/-- The body of a DLB1 frame: `serializeDeltaBatchBodyWith?`. The buffer starts
    with room for the 160 bytes that an entry takes, a guess that only sets the
    first allocation. -/
def bodyBA? (tc : DeltaTermCodec) (b : DeltaBatch) : Option ByteArray :=
  if !natFitsU64 b.seq || !natFitsU64 b.epoch || b.ops.length >= two32 then none
  else
    pushEntries? tc
      (pushU32 (pushU64 (pushU64 (ByteArray.emptyWithCapacity (b.ops.length * 160 + 32))
        b.seq.toUInt64) b.epoch.toUInt64) (UInt32.ofNat b.ops.length)) b.ops

/-- The DLB1 frame of `body` appended to `pre`. -/
def pushBatchFrame (pre body : ByteArray) : ByteArray :=
  pushU32 (pushU32 (pushU32 (pushU32 pre deltaBatchMagic) deltaBatchVersion)
    (UInt32.ofNat body.size) ++ body) (sumRange body 0 body.size)

/-- `pre` followed by the DLB1 frame of the batch: `pre.toList ++ frame` for
    `serializeDeltaBatchWith?`. -/
def batchBA? (tc : DeltaTermCodec) (pre : ByteArray) (b : DeltaBatch) : Option ByteArray :=
  match bodyBA? tc b with
  | none => none
  | some body => if body.size >= two32 then none else some (pushBatchFrame pre body)

/-- The DLOG header of version `version`. -/
def logHeaderBA (version : UInt32) : ByteArray := pushU32 (pushU32 ByteArray.empty deltaLogMagic) version

/-- `AppendPlan` with the bytes in a byte array. -/
structure AppendPlanBA where
  version : UInt32
  setVersion2 : Bool
  bytes : ByteArray

/-- `appendPlan?` with the bytes in a byte array. -/
def appendPlanBA? (logVersion : Option UInt32) (batch : DeltaBatch) : Option AppendPlanBA :=
  let version :=
    if batch.ops.any entryNeedsV2 || logVersion == some deltaLogVersion2 then deltaLogVersion2
    else deltaLogVersion
  match DeltaTermCodec.ofVersion version with
  | none => none
  | some tc =>
    match logVersion with
    | none =>
      match batchBA? tc (logHeaderBA version) batch with
      | none => none
      | some bytes => some { version, setVersion2 := false, bytes }
    | some v =>
      match batchBA? tc ByteArray.empty batch with
      | none => none
      | some bytes => some { version, setVersion2 := v != version, bytes }

/-! ## Build-time checks

Each check compares the byte-array function with the specification on the same
input, with a non-empty tail where a tail exists. -/

private def ba (l : List UInt8) : ByteArray := ⟨l.toArray⟩

private def exIri : WfIri := ⟨"http://example.org/s", by decide⟩
private def exP : WfIri := ⟨"http://example.org/p", by decide⟩
private def ttNested : Term :=
  .tripleTerm (.bnode "b0") exP
    (.tripleTerm (.iri exIri) exP (.literal (Literal.dirLangString "salaam" "ar" .rtl)))
private def plainBatch : DeltaBatch :=
  { seq := 1, epoch := 1, ops := [.add ⟨.iri exIri, exP, .literal (Literal.string "v")⟩ none,
      .remove ⟨.bnode "x", exP, .literal (Literal.langString "hi" "en")⟩ (some "http://example.org/g"),
      .clear none, .drop "http://example.org/g", .create "http://example.org/h"] }
private def ttBatch : DeltaBatch :=
  { seq := 2, epoch := 1, ops := [.add ⟨.iri exIri, exP, ttNested⟩ (some "http://example.org/g")] }

#guard (appendPlanBA? none plainBatch).map (fun p => (p.version, p.setVersion2, p.bytes.data.toList)) ==
  (appendPlan? none plainBatch).map (fun p => (p.version, p.setVersion2, p.bytes))
#guard (appendPlanBA? (some 1) plainBatch).map (fun p => (p.version, p.setVersion2, p.bytes.data.toList)) ==
  (appendPlan? (some 1) plainBatch).map (fun p => (p.version, p.setVersion2, p.bytes))
#guard (appendPlanBA? (some 1) ttBatch).map (fun p => (p.version, p.setVersion2, p.bytes.data.toList)) ==
  (appendPlan? (some 1) ttBatch).map (fun p => (p.version, p.setVersion2, p.bytes))
#guard (appendPlanBA? none ttBatch).map (fun p => (p.version, p.setVersion2, p.bytes.data.toList)) ==
  (appendPlan? none ttBatch).map (fun p => (p.version, p.setVersion2, p.bytes))
#guard (appendPlanBA? (some 2) plainBatch).map (fun p => (p.version, p.setVersion2, p.bytes.data.toList)) ==
  (appendPlan? (some 2) plainBatch).map (fun p => (p.version, p.setVersion2, p.bytes))
-- a batch the format cannot hold: a sequence number of 2 ^ 64
#guard (appendPlanBA? none { plainBatch with seq := 18446744073709551616 }).isNone

private def v1log : List UInt8 :=
  ((appendPlan? none plainBatch).map (·.bytes)).getD [] ++
    ((appendPlan? (some 1) { plainBatch with seq := 2 }).map (·.bytes)).getD []
private def v2log : List UInt8 :=
  ((appendPlan? none plainBatch).map (·.bytes)).getD [] ++
    ((appendPlan? (some 2) ttBatch).map (·.bytes)).getD []

private def viewChecked (r : Except String (List DeltaBatch × Bool)) :
    Except String (List DeltaBatch × Bool) := r

private def sameChecked (bs : List UInt8) : Bool :=
  match parseLogChecked bs, parseLogCheckedBA (ba bs) with
  | .ok x, .ok y => x == y
  | .error x, .error y => x == y
  | _, _ => false

private def sameCheckedV1 (bs : List UInt8) : Bool :=
  match parseLogCheckedV1 bs, parseLogCheckedV1BA (ba bs) with
  | .ok x, .ok y => x == y
  | .error x, .error y => x == y
  | _, _ => false

#guard (match parseLogCheckedBA (ba v1log) with | .ok (bs, false) => bs.length == 2 | _ => false)
#guard (match parseLogCheckedBA (ba (logHeader 2 ++ v2log.drop 8)) with
  | .ok (bs, false) => bs == [plainBatch, ttBatch] | _ => false)
#guard sameChecked v1log
#guard sameChecked (logHeader 2 ++ v2log.drop 8)
#guard sameChecked (logHeader 1 ++ v2log.drop 8)
#guard sameChecked (logHeader 3 ++ v2log.drop 8)
#guard sameChecked []
#guard sameChecked [0x44, 0x4C, 0x4F]
#guard sameChecked (logHeader 1)
#guard sameCheckedV1 (logHeader 2 ++ v2log.drop 8)
#guard sameCheckedV1 v1log
#guard sameCheckedV1 []
-- every cut of a log (a torn final frame at every length) and every changed byte
#guard (List.range (v1log.length + 1)).all fun n => sameChecked (v1log.take n)
#guard (List.range v1log.length).all fun i =>
  sameChecked (v1log.set i (v1log.getD i 0 + 1)) && sameChecked (v1log.set i (v1log.getD i 0 ^^^ 0xFF))
#guard (List.range (v2log.length + 1)).all fun n => sameChecked (v2log.take n)
#guard (List.range v2log.length).all fun i =>
  sameChecked (v2log.set i (v2log.getD i 0 + 1)) && sameChecked (v2log.set i (v2log.getD i 0 ^^^ 0xFF))

end L4Factoidal.Storage.DeltaLogBytes
