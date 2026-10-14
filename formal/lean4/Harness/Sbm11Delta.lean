/-
Harness/Sbm11Delta — the delta log of an SBM11 generation (stage 5,
https://github.com/danbri/factoidal/issues/791): read the committed DLOG
batches, append one batch for a SPARQL Update.

The log is the DLOG file `deltas.dlog` of the generation directory, the same
format and the same Lean definitions as `l4block-delta-log`
(`Storage/DeltaLog.lean`: DLB1 batches of DLE1 entries over RDF terms;
`SPARQL/UpdateDelta.lean`: an update to entries). The `compacted.epoch`
marker (CEP1) of a compacted generation says which batches its base already
holds (`replayBatchesSinceEpoch?`).

Admitted updates: INSERT DATA, DELETE DATA, CLEAR, DROP, CREATE, as for
`l4block-delta-log` (`deltaEntriesForOp?`). Refused: an update with a WHERE
clause (it needs the overlaid generation's answer at write time), and
INSERT DATA with blank nodes, also inside a triple term (a fresh blank node
needs the base's labels).

`--sparql12` reads the update with the SPARQL 1.2 grammar: triple terms and
directional literals (https://github.com/danbri/factoidal/issues/792 item 1).
A batch that holds one needs a DLOG of version 2 (`appendPlan?`): a new log
gets that header, and an existing version 1 log gets its header version set
to 2 in place (four bytes, under the append lock, synced) before the batch is
appended. A log that holds no RDF 1.2 term keeps version 1 and its bytes.

This is a HARNESS: it does file I/O. The replay semantics is
`L4Factoidal.Storage.Sbm11.Overlay` (proved: `OverlayTheorems.step_add`,
`step_remove`, `step_clear`).
-/
import L4Factoidal.SPARQL.UpdateParser
import L4Factoidal.SPARQL.UpdateDelta
import L4Factoidal.Storage.DeltaLog
import Harness.PosixRangeIO
import Harness.GenerationPointer
import Harness.CompactedEpoch

namespace Harness.Sbm11Delta

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage

def logName : String := "deltas.dlog"

/-- The committed batches of `dir`'s log that its base does not hold, the
    log's bytes (empty when there is no log), and `true` when no torn final
    frame follows them. A torn final frame (an append that did not complete) is
    left out (`classifyTail`, https://github.com/danbri/factoidal/issues/843).
    A damaged frame, a committed frame that does not decode, a malformed
    header, a batch order that `validBatchHistory` refuses, or epochs that are
    not a compacted prefix and a replay suffix are errors: the batches after a
    frame that this reader cannot read are not dropped without a message. -/
def readBatches (dir : String) : IO (List DeltaBatch × ByteArray × Bool) := do
  let path : System.FilePath := s!"{dir}/{logName}"
  if !(← path.pathExists) then return ([], .empty, true)
  let bytes ← IO.FS.readBinFile path
  match parseLogChecked bytes.toList with
  | .error e => throw (IO.userError s!"{path}: {e}")
  | .ok (batches, torn) =>
    if !validBatchHistory batches then
      throw (IO.userError s!"{path}: DLOG batch sequence or epoch order is invalid")
    let baseEpoch ← Harness.CompactedEpoch.read? (System.FilePath.mk dir)
    match replayBatchesSinceEpoch? baseEpoch batches with
    | some replay => return (replay, bytes, !torn)
    | none => throw (IO.userError s!"{path}: DLOG epochs do not form a compacted-prefix/replay-suffix history")

private def asBytes (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray

private def nextSeq (batches : List DeltaBatch) : Nat :=
  batches.foldl (fun a b => max a b.seq) 0 + 1

private def hasInsertBnode : List UpdateOp → Bool
  | [] => false
  | .insertData quads :: rest =>
      (collectQuads none quads).any (fun q => tripleMentionsBnode q.2) || hasInsertBnode rest
  | _ :: rest => hasInsertBnode rest

/-- Append one batch for `text` to the log of the generation `dir0` names
    (through `CURRENT` when `dir0` is a collection root). The append is
    positioned at the size read (`appendSyncAtSizeRaw`, file synced); a
    concurrent writer makes it retry, three times at most. -/
def appendUpdate (dir0 text : String) (sparql : SparqlVersion := .v11) : IO UInt32 := do
  let dir := (← Harness.GenerationPointer.resolveStoreDirectory dir0).toString
  let baseEpoch ← Harness.CompactedEpoch.read? (System.FilePath.mk dir)
  let epoch := Harness.CompactedEpoch.nextWriteEpoch baseEpoch
  let path := s!"{dir}/{logName}"
  match parseSparqlUpdate text none sparql with
  | .error e =>
    IO.eprintln s!"l4sbm11 update: parse error at {e.pos}: {e.msg}"
    return 1
  | .ok update =>
    if hasInsertBnode update.ops then
      IO.eprintln "l4sbm11 update: refused: INSERT DATA with blank nodes"
      return 1
    for _ in [0:3] do
      let exists_ ← System.FilePath.pathExists path
      let bytes ← if exists_ then IO.FS.readBinFile path else pure ByteArray.empty
      let (logVersion, batches) ← if bytes.isEmpty then pure (none, []) else
        match parseLogChecked bytes.toList, logHeaderVersion? bytes.toList with
        | .ok (bs, false), some v =>
          if validBatchHistory bs then pure (some v, bs)
          else throw (IO.userError s!"{path}: DLOG batch sequence or epoch order is invalid")
        | .ok (_, true), _ => throw (IO.userError s!"{path}: DLOG has an uncommitted suffix; recover it before appending")
        | .error e, _ => throw (IO.userError s!"{path}: {e}")
        | .ok _, none => throw (IO.userError s!"{path}: DLOG header is malformed or unsupported")
      match deltaBatchForUpdate? (nextSeq batches) epoch id update with
      | none =>
        IO.eprintln "l4sbm11 update: refused: the update needs WHERE evaluation or is an unsupported graph-wide operation"
        return 1
      | some batch =>
        match appendPlan? logVersion batch with
        | none =>
          IO.eprintln "l4sbm11 update: refused: the batch exceeds the DLOG wire-format limits"
          return 1
        | some plan =>
          let size := UInt64.ofNat bytes.size
          -- a version 1 log gets version 2 before the first RDF 1.2 batch; a
          -- concurrent append changes the size, and the loop reads again
          let headerOk ← if plan.setVersion2 then
              Harness.PosixRangeIO.writeAtSizeSyncRaw path size 4 (asBytes (writeU32LE deltaLogVersion2))
            else pure true
          if headerOk then
            if ← Harness.PosixRangeIO.appendSyncAtSizeRaw path size (asBytes plan.bytes) then
              let frameBytes := if bytes.isEmpty then plan.bytes.length - 8 else plan.bytes.length
              IO.println s!"l4sbm11 update: committed path={path} seq={batch.seq} epoch={batch.epoch} ops={batch.ops.length} bytes={frameBytes} log-version={plan.version}{if plan.setVersion2 then " (set from 1)" else ""}"
              return 0
    IO.eprintln "l4sbm11 update: concurrent writers prevented a stable append after 3 tries"
    return 1

end Harness.Sbm11Delta
