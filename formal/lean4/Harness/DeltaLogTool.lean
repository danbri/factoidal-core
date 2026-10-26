/-
Small native edge for the DLOG sidecar used by a Shardborough collection.

It deliberately owns only filesystem effects.  Parsing, translating an UPDATE,
and serialising the batch are Lean definitions.  This first host refuses
INSERT DATA blank nodes because allocating their fresh request scope requires
the composed base-plus-delta dataset; it will be admitted when that reader is
wired.  Existing logs with a torn suffix are also refused for mutation: replay
may safely query their committed prefix, but a repair/compaction tool must make
the recovery decision before a writer appends after it.
-/
import L4Factoidal.SPARQL.UpdateParser
import L4Factoidal.SPARQL.UpdateDelta
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.Storage.DeltaLogBytesTheorems
import L4Factoidal.Storage.ShardManifest
import Harness.PosixRangeIO
import Harness.GenerationPointer
import Harness.CompactedEpoch

namespace Harness.DeltaLogTool

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage
open Harness.PosixRangeIO
open Harness.GenerationPointer
open Harness.CompactedEpoch

private def logPath (directory : System.FilePath) : System.FilePath := directory / "deltas.dlog"

private def asBytes (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray

private def readExisting (path : System.FilePath) : IO (List DeltaBatch × Nat) := do
  try
    let bytes ← IO.FS.readBinFile path
    match DeltaLogBytes.parseLogCheckedV1BA bytes with
    | .error e => throw <| IO.userError s!"DLOG: {e}"
    | .ok (batches, false) =>
        if validBatchHistory batches then pure (batches, bytes.size)
        else throw <| IO.userError "DLOG batch sequence or epoch order is invalid"
    | .ok (_, true) => throw <| IO.userError "DLOG has a torn or uncommitted suffix; recover it before appending"
  catch e =>
    if (← path.pathExists) then throw e else pure ([], 0)

private def nextSeq : List DeltaBatch → Nat
  | [] => 1
  | batch :: rest =>
      let last := rest.foldl (fun _ next => next) batch
      last.seq + 1

private def hasInsertBnode : List UpdateOp → Bool
  | [] => false
  | .insertData quads :: rest =>
      (collectQuads none quads).any (fun q => q.2.hasBnode) || hasInsertBnode rest
  | _ :: rest => hasInsertBnode rest

/-- The operations IBK4 and IBK5 refuse: CREATE GRAPH adds a named graph with no
    triple, and CLEAR of a named graph leaves one. The store has no graph list,
    so the graph would vanish from `GRAPH ?g { }` after the log was applied
    (https://github.com/danbri/factoidal/issues/880, owner decision of
    2026-10-22: refuse). A DELETE that removes the last triple of a graph is
    not detected here: that needs the composed base-plus-delta view. -/
private def emptiesNamedGraph : UpdateOp → Bool
  | .create _ _ => true
  | .clear _ (.graph _) => true
  | _ => false

private def graphRefusal : String :=
  "l4block-delta-log refused: IBK4 and IBK5 store no named graph without a triple (https://github.com/danbri/factoidal/issues/880); CREATE GRAPH and CLEAR of a named graph are refused; use SBM11"

/-- Whether the generation directory holds an IBK4 or IBK5 collection (quad
    blocks). Their query path, `l4block-quad-query`, does not replay the log, so a
    committed update would be silently invisible
    (https://github.com/danbri/factoidal/issues/935, owner decision of
    2026-10-22: refuse). IBK3 replays the log and keeps taking updates. -/
private def isQuadIbk (directory : System.FilePath) : IO Bool := do
  let path := directory / "manifest.sbm2"
  if !(← path.pathExists) then return false
  match L4Factoidal.Storage.ShardManifest.decode? (← IO.FS.readBinFile path) with
  | some manifest =>
      return L4Factoidal.Storage.ShardManifest.isIbk4Layout manifest.layout ||
        L4Factoidal.Storage.ShardManifest.isIbk5Layout manifest.layout
  | none => return false

private def quadIbkRefusal : String :=
  "l4block-delta-log refused: the IBK4 and IBK5 query paths do not replay the delta log, so no update is accepted on these stores (https://github.com/danbri/factoidal/issues/935); use SBM11 or IBK3"

private def commitUpdate (path : System.FilePath) (epoch : Nat) (update : Update) : Nat → IO UInt32
  | 0 => do
      IO.eprintln "l4block-delta-log failed: concurrent writers prevented a stable append after 3 retries"
      pure 1
  | retries + 1 => do
      let (batches, expectedSize) ← readExisting path
      match deltaBatchForUpdate? (nextSeq batches) epoch id update with
      | none =>
          IO.eprintln "l4block-delta-log rejected: update needs WHERE evaluation or unsupported graph-wide operation"
          pure 1
      | some batch =>
          match serializeDeltaBatch? batch, if expectedSize == 0 then serializeLog? [] else some [] with
          | some frame, some initial =>
              let bytes := initial ++ frame
              if ← appendSyncAtSizeRaw path.toString (UInt64.ofNat expectedSize) (asBytes bytes) then
                IO.println s!"l4block-delta-log committed path={path} seq={batch.seq} epoch={batch.epoch} ops={batch.ops.length} bytes={frame.length} sync=file retries={3 - retries}"
                pure 0
              else commitUpdate path epoch update retries
          | _, _ =>
              IO.eprintln "l4block-delta-log rejected: batch exceeds the DLOG wire-format limits"
              pure 1

private def appendUpdate (directory : System.FilePath) (updateText : String) : IO UInt32 := do
  let directory ← resolveStoreDirectory directory
  if ← isQuadIbk directory then
    IO.eprintln quadIbkRefusal
    return 1
  let baseEpoch ← CompactedEpoch.read? directory
  let epoch := nextWriteEpoch baseEpoch
  let path := logPath directory
  match parseSparqlUpdate updateText with
  | .error error => IO.eprintln s!"l4block-delta-log update parse error at {error.pos}: {error.msg}"; pure 1
  | .ok update =>
      if update.ops.any emptiesNamedGraph then
        IO.eprintln graphRefusal
        pure 1
      else if hasInsertBnode update.ops then
        IO.eprintln "l4block-delta-log rejected: INSERT DATA blank nodes await composed-store freshness allocation"
        pure 1
      else commitUpdate path epoch update 3

private def inspect (directory : System.FilePath) : IO UInt32 := do
  let directory ← resolveStoreDirectory directory
  let path := logPath directory
  try
    let bytes ← IO.FS.readBinFile path
    match DeltaLogBytes.parseLogAt bytes with
    | none => IO.eprintln "l4block-delta-log rejected: DLOG header is malformed or unsupported"; pure 1
    | some (batches, offset) =>
        -- the bytes from `offset` are the tail after the committed batches
        let kind := DeltaLogBytes.classifyAt bytes offset
        let clean : Bool := decide (bytes.size ≤ offset)
        let version := (DeltaLogBytes.logHeaderVersionAt? bytes).getD 0
        IO.println s!"l4block-delta-log path={path} version={version} committed-batches={batches.length} committed-ops={(batches.flatMap (·.ops)).length} clean-tail={clean} tail={kind.name}"
        if !clean then
          IO.eprintln s!"l4block-delta-log: {path}: {kind.text offset (bytes.size - offset)}"
        pure (if clean then 0 else 1)
  catch _ => IO.eprintln s!"l4block-delta-log no log at {path}"; pure 1

/-! ### `--nest-check N`

One DLB1 batch whose entry holds an RDF 1.2 triple term nested `N` deep in
the object position, the innermost object a directional literal, through the
DLOG version 2 codec (https://github.com/danbri/factoidal/issues/792 item 1):
the append plan of a new log, `parseLogChecked`, and the append plan of the
decoded batch again. The second bytes must be the first, the decoded depth
`N`, and the innermost literal the one built. The checks walk the chain with
loops; nothing compares two deep terms with the derived equality, which
recurses. `tests/stack/run.sh` runs it 300,000 deep (above the wasm module's
stack) under a 512 KB native stack. -/

private def nestGo (s : Subject) (p : WfIri) : Nat → Term → Term
  | 0, t => t
  | n + 1, t => nestGo s p n (.tripleTerm s p t)

private def innermostGo : Nat → Term → Nat × Term
  | d, .tripleTerm _ _ o => innermostGo (d + 1) o
  | d, t => (d, t)

private def nestCheck (n : Nat) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let s : Subject := .iri ⟨"a:s", rfl⟩
  let p : WfIri := ⟨"a:p", rfl⟩
  let leaf : Term := .literal (Literal.dirLangString "deep" "ar" .rtl)
  let g : Option DeltaGraphName := some (.iri "http://example.org/g")
  let batch : DeltaBatch := { seq := 1, epoch := 1, ops := [.add ⟨s, p, nestGo s p n leaf⟩ g] }
  let some plan := appendPlan? none batch
    | IO.eprintln "FAIL: the batch has no append plan"; return 1
  let t1 ← IO.monoNanosNow
  match parseLogChecked plan.bytes with
  | .error e => IO.eprintln s!"FAIL: the log does not read back: {e}"; return 1
  | .ok (batches, torn) =>
    let t2 ← IO.monoNanosNow
    let mut fails := 0
    if torn then
      fails := fails + 1; IO.eprintln "FAIL: the log reads as torn"
    match batches with
    | [b] =>
      match b.ops with
      | [.add tr g'] =>
        let (depth, inner) := innermostGo 0 tr.o
        if depth != n then
          fails := fails + 1; IO.eprintln s!"FAIL: decoded depth {depth}, built {n}"
        if inner != leaf then
          fails := fails + 1; IO.eprintln "FAIL: the innermost literal is not \"deep\"@ar--rtl"
        if tr.s != s || tr.p != p || g' != g then
          fails := fails + 1; IO.eprintln "FAIL: the subject, predicate or graph differs"
        match appendPlan? none b with
        | some plan2 =>
          if plan2.bytes != plan.bytes then
            fails := fails + 1; IO.eprintln "FAIL: the decoded batch encodes to other bytes"
        | none => fails := fails + 1; IO.eprintln "FAIL: the decoded batch has no append plan"
      | _ => fails := fails + 1; IO.eprintln "FAIL: the decoded batch does not hold one add entry"
    | _ => fails := fails + 1; IO.eprintln s!"FAIL: {batches.length} batches decoded, 1 written"
    let t3 ← IO.monoNanosNow
    IO.println s!"l4block-delta-log nest-check: depth={n} log-bytes={plan.bytes.length} version={plan.version} encode-ms={(t1 - t0) / 1000000} decode-ms={(t2 - t1) / 1000000} check-ms={(t3 - t2) / 1000000} failures={fails}"
    pure (if fails == 0 then 0 else 1)

def main (args : List String) : IO UInt32 :=
  match args with
  | ["--nest-check", n] => nestCheck n.toNat!
  | directory :: "--update" :: updateParts =>
      if updateParts.isEmpty then do
        IO.eprintln "l4block-delta-log requires SPARQL UPDATE text after --update"
        pure 2
      else appendUpdate (System.FilePath.mk directory) (String.intercalate " " updateParts)
  | directory :: "--inspect" :: [] => inspect (System.FilePath.mk directory)
  | _ => do
      IO.eprintln "usage: l4block-delta-log STORE-DIR --update SPARQL-UPDATE | --inspect | --nest-check N"
      pure 2

end Harness.DeltaLogTool

def main (args : List String) : IO UInt32 := Harness.DeltaLogTool.main args
