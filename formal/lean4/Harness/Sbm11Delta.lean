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
INSERT DATA with blank nodes (a fresh blank node needs the base's labels).

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

/-- The committed batches of `dir`'s log that its base does not hold, and the
    log's bytes (empty when there is no log). A torn suffix (a batch not
    committed) is left out, as the DLOG reader does; a malformed header, a
    batch order that `validBatchHistory` refuses, or epochs that are not a
    compacted prefix and a replay suffix are errors. -/
def readBatches (dir : String) : IO (List DeltaBatch × ByteArray × Bool) := do
  let path : System.FilePath := s!"{dir}/{logName}"
  if !(← path.pathExists) then return ([], .empty, true)
  let bytes ← IO.FS.readBinFile path
  match parseLog bytes.toList with
  | none => throw (IO.userError s!"{path}: DLOG header is malformed or unsupported")
  | some (batches, tail) =>
    if !validBatchHistory batches then
      throw (IO.userError s!"{path}: DLOG batch sequence or epoch order is invalid")
    let baseEpoch ← Harness.CompactedEpoch.read? (System.FilePath.mk dir)
    match replayBatchesSinceEpoch? baseEpoch batches with
    | some replay => return (replay, bytes, tail.isEmpty)
    | none => throw (IO.userError s!"{path}: DLOG epochs do not form a compacted-prefix/replay-suffix history")

private def asBytes (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray

private def nextSeq (batches : List DeltaBatch) : Nat :=
  batches.foldl (fun a b => max a b.seq) 0 + 1

private def hasInsertBnode : List UpdateOp → Bool
  | [] => false
  | .insertData quads :: rest =>
      (collectQuads none quads).any (fun q => q.2.hasBnode) || hasInsertBnode rest
  | _ :: rest => hasInsertBnode rest

/-- Append one batch for `text` to the log of the generation `dir0` names
    (through `CURRENT` when `dir0` is a collection root). The append is
    positioned at the size read (`appendSyncAtSizeRaw`, file synced); a
    concurrent writer makes it retry, three times at most. -/
def appendUpdate (dir0 text : String) : IO UInt32 := do
  let dir := (← Harness.GenerationPointer.resolveStoreDirectory dir0).toString
  let baseEpoch ← Harness.CompactedEpoch.read? (System.FilePath.mk dir)
  let epoch := Harness.CompactedEpoch.nextWriteEpoch baseEpoch
  let path := s!"{dir}/{logName}"
  match parseSparqlUpdate text with
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
      let batches ← if bytes.isEmpty then pure [] else
        match parseLog bytes.toList with
        | some (bs, []) =>
          if validBatchHistory bs then pure bs
          else throw (IO.userError s!"{path}: DLOG batch sequence or epoch order is invalid")
        | some _ => throw (IO.userError s!"{path}: DLOG has an uncommitted suffix; recover it before appending")
        | none => throw (IO.userError s!"{path}: DLOG header is malformed or unsupported")
      match deltaBatchForUpdate? (nextSeq batches) epoch id update with
      | none =>
        IO.eprintln "l4sbm11 update: refused: the update needs WHERE evaluation or is an unsupported graph-wide operation"
        return 1
      | some batch =>
        match serializeDeltaBatch? batch, (if bytes.isEmpty then serializeLog? [] else some []) with
        | some frame, some initial =>
          if ← Harness.PosixRangeIO.appendSyncAtSizeRaw path (UInt64.ofNat bytes.size) (asBytes (initial ++ frame)) then
            IO.println s!"l4sbm11 update: committed path={path} seq={batch.seq} epoch={batch.epoch} ops={batch.ops.length} bytes={frame.length}"
            return 0
        | _, _ =>
          IO.eprintln "l4sbm11 update: refused: the batch exceeds the DLOG wire-format limits"
          return 1
    IO.eprintln "l4sbm11 update: concurrent writers prevented a stable append after 3 tries"
    return 1

end Harness.Sbm11Delta
