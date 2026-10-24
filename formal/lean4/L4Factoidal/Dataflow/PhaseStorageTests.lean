/-
L4Factoidal.Dataflow.PhaseStorageTests — build-time checks of the storage
stages of `Dataflow/PhaseStorage.lean`
(https://github.com/danbri/factoidal/issues/975).

* The block round-trip stages run on small blocks and return the rows written
  (the folded spellings; `Storage/DictFoldTests.lean` states the fold).
* A block that the wire format does not support stops the stage with an error.
* The search stage of the index returns the matching triples of the default
  graph.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Dataflow.PhaseStorage

namespace L4Factoidal.Dataflow.PhaseStorageTests

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Dataflow

private def exI (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def litEN : Term := .literal (Literal.langString "x" "EN")
private def liten : Term := .literal (Literal.langString "x" "en")
private def sA : Subject := .iri (exI "http://ex.org/a")
private def sB : Subject := .iri (exI "http://ex.org/b")
private def pP : WfIri := exI "http://ex.org/p"
private def pQ : WfIri := exI "http://ex.org/q"
private def gG : Subject := .iri (exI "http://ex.org/g")

private def okOr {α : Type} (r : Except String α) : Option α :=
  match r with
  | .ok a => some a
  | .error _ => none

/-! ## IBK3 -/

private def g3 : Graph := [⟨sA, pP, litEN⟩, ⟨sB, pP, liten⟩]
#guard (okOr (ibk3RoundTripStage.run (IndexedBlock.fromGraph g3))).map (·.denotes) ==
  some [⟨sA, pP, liten⟩, ⟨sB, pP, liten⟩]

/-! ## IBK4 -/

private def q4 : List IndexedBlockWireV4.QuadRow :=
  [(none, ⟨sA, pP, litEN⟩), (some gG, ⟨sB, pP, liten⟩)]
#guard (okOr (ibk4RoundTripStage.run (IndexedBlockWireV4.fromQuads q4))).map (·.denotes) ==
  some [(none, ⟨sA, pP, liten⟩), (some gG, ⟨sB, pP, liten⟩)]

-- a block with a repeated dictionary entry is refused by `encode?`: the stage stops
private def badBlock4 : IndexedBlockWireV4.QuadBlock :=
  { dict := #[.iri (exI "http://ex.org/a"), .iri pP, litEN, liten], idByTerm := ∅,
    rows := #[{ g := none, s := 0, p := 1, o := 2 }, { g := none, s := 0, p := 1, o := 3 }],
    byPredicate := ∅ }
#guard (okOr (ibk4RoundTripStage.run badBlock4)).isNone

/-! ## StoreCaps search of the index -/

private def ds : Dataset :=
  { default := [⟨sA, pP, liten⟩, ⟨sB, pQ, liten⟩, ⟨sB, pP, .iri (exI "http://ex.org/c")⟩], named := [] }

private def searchP : SPARQL.PatternBound := { p := some pP }

-- the stage needs `ds.IsSet`; the run is `backendSearch` of the index arm
#guard (SPARQL.StoreBackend.backendSearch (.indexed (OWL.RL.Index.ofGraph ds.default)) searchP).length == 2
#guard (SPARQL.StoreBackend.backendSearch (.indexed (OWL.RL.Index.ofGraph ds.default)) searchP).all
  (fun t => t.p == pP)

end L4Factoidal.Dataflow.PhaseStorageTests
