import L4Factoidal.SPARQL.StoreEndpoint

namespace L4Factoidal.SPARQL.StoreEndpoint

open L4Factoidal.RDF (Triple WfIri)
open L4Factoidal.Storage (DeltaBatch DeltaEntry)

private def witnessIri : WfIri := ⟨"http://e/p", by decide⟩

private def witnessTriple : Triple := ⟨.iri witnessIri, witnessIri, .iri witnessIri⟩

private def previousBatch : DeltaBatch :=
  { seq := 1, epoch := 2, ops := [.add witnessTriple none] }

private def appendedBatch : DeltaBatch :=
  { seq := 2, epoch := 1, ops := [.clear none] }

private def previousRaw : List UInt8 :=
  (Storage.serializeLog? [previousBatch]).getD []

private def previousBytes : ByteArray :=
  ByteArray.mk previousRaw.toArray

private def appendedBytes : ByteArray :=
  ByteArray.mk ((Storage.serializeDeltaBatch? appendedBatch).getD []).toArray

private def previousState : LogState :=
  { size := previousBytes.size, nextSeq := 2, writeEpoch := 1 }

private def appendedState : LogState :=
  { previousState with size := previousState.size + appendedBytes.size, nextSeq := 3 }

private theorem eq_ok_of_toOption {ε α : Type} {result : Except ε α} {value : α}
    (h : result.toOption = some value) : result = .ok value := by
  cases result with
  | error _ => cases h
  | ok _ => exact congrArg Except.ok (Option.some.inj h)

private def errorOption {ε α : Type} : Except ε α → Option ε
  | .error error => some error
  | .ok _ => none

private theorem eq_error_of_errorOption {ε α : Type} {result : Except ε α} {error : ε}
    (h : errorOption result = some error) : result = .error error := by
  cases result with
  | ok _ => cases h
  | error _ => exact congrArg Except.error (Option.some.inj h)

/-- Kind: executable counterexample (factoidal-core issue 622).
Says: opening a valid version 1 log without a compacted marker, then appending
a frame accepted by the writer, can produce a cleanly decoded log that the
opener refuses because the epochs decrease.
Does not say: that a fixed generation with coherent metadata produces the
starting log, or that a host append or reopen was observed. -/
theorem acceptedLogAppend_can_fail_reopen :
    ∃ (first : DeltaBatch) (raw : List UInt8) (st st' : LogState) (chunk : ByteArray),
      first.seq = 1 ∧ first.epoch = 2 ∧
      Storage.serializeLog? [first] = some raw ∧
      openLog (some (ByteArray.mk raw.toArray)) none = .ok (st, [first]) ∧
      st.nextSeq = 2 ∧ st.writeEpoch = 1 ∧
      appendBytes st [.clear none] = some (chunk, st') ∧
      Storage.DeltaLogBytes.parseLogCheckedV1BA (ByteArray.mk raw.toArray ++ chunk) =
        .ok ([first, { seq := 2, epoch := 1, ops := [.clear none] }], false) ∧
      openLog (some (ByteArray.mk raw.toArray ++ chunk)) none =
        .error "deltas.dlog: the batch sequence or epoch order is invalid" := by
  refine ⟨previousBatch, previousRaw, previousState, appendedState, appendedBytes,
    rfl, rfl, ?_, ?_, rfl, rfl, ?_, ?_, ?_⟩
  · decide +kernel
  · apply eq_ok_of_toOption
    decide +kernel
  · decide +kernel
  · apply eq_ok_of_toOption
    decide +kernel
  · apply eq_error_of_errorOption
    decide +kernel

#print axioms acceptedLogAppend_can_fail_reopen

end L4Factoidal.SPARQL.StoreEndpoint
