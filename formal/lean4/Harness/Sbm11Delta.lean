/-
Harness/Sbm11Delta — the delta log of an SBM11 generation (stage 5,
https://github.com/danbri/factoidal/issues/791): read the committed DLOG
batches. The append of one batch for a SPARQL Update is `Sbm11Update.appendUpdate`.

The log is the DLOG file `deltas.dlog` of the generation directory, the same
format and the same Lean definitions as `l4block-delta-log`
(`Storage/DeltaLog.lean`: DLB1 batches of DLE1 entries over RDF terms;
`SPARQL/UpdateDelta.lean`: an update to entries). The `compacted.epoch`
marker (CEP1) of a compacted generation says which batches its base already
holds (`replayBatchesSinceEpoch?`).

The update itself (INSERT DATA with blank nodes, DELETE/INSERT and DELETE
WHERE with a WHERE clause, the graph management operations) is
`Harness/Sbm11Update.lean`: it evaluates what the request reads on the
overlaid generation and appends ONE batch with the entries of the whole
request. This module reads the log.

`l4sbm11 update --sparql12` reads the update with the SPARQL 1.2 grammar: triple
terms and directional literals (https://github.com/danbri/factoidal/issues/792
item 1). A batch that holds one needs a DLOG of version 2 (`appendPlan?`): a new
log gets that header, and an existing version 1 log gets its header version set
to 2 in place (four bytes, under the append lock, synced) before the batch is
appended. A log that holds no RDF 1.2 term keeps version 1 and its bytes.

This is a HARNESS: it does file I/O. The replay semantics is
`L4Factoidal.Storage.Sbm11.Overlay` (proved: `OverlayTheorems.step_add`,
`step_remove`, `step_clear`).
-/
import L4Factoidal.SPARQL.UpdateParser
import L4Factoidal.SPARQL.UpdateDelta
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.Storage.DeltaLogBytesTheorems
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
  match DeltaLogBytes.parseLogCheckedBA bytes with
  | .error e => throw (IO.userError s!"{path}: {e}")
  | .ok (batches, torn) =>
    if !validBatchHistory batches then
      throw (IO.userError s!"{path}: DLOG batch sequence or epoch order is invalid")
    let baseEpoch ← Harness.CompactedEpoch.read? (System.FilePath.mk dir)
    match replayBatchesSinceEpoch? baseEpoch batches with
    | some replay => return (replay, bytes, !torn)
    | none => throw (IO.userError s!"{path}: DLOG epochs do not form a compacted-prefix/replay-suffix history")

def asBytes (xs : List UInt8) : ByteArray := ByteArray.mk xs.toArray

/-- The sequence number the next batch gets. -/
def nextSeq (batches : List DeltaBatch) : Nat :=
  batches.foldl (fun a b => max a b.seq) 0 + 1

end Harness.Sbm11Delta
