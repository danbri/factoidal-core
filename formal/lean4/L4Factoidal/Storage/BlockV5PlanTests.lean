/-
L4Factoidal.Storage.BlockV5PlanTests -- the build-time checks of `L4Factoidal.Storage.BlockV5Plan`.

These checks were the last section of `L4Factoidal.Storage.BlockV5Plan`. They were moved
here on 2026-10-10 because their fixtures (70,000-byte literals, blobs
hashed with SHA-256, encoded blocks) are top-level constants, and Lean
evaluates a top-level constant when its module is initialised, in every
executable that links the module. Five modules (`TermWireV2`,
`IndexedBlockWireV5`, `PagedTermDictionaryV2`, `BlockV5Plan`, `Codec.Inflate`)
held such fixtures. `l4factoidal version` executed 304,962,107 instructions
(43 ms of CPU time; the F* binary needs 6 ms) before the move and 25,590,678
(7 ms) after it, measured with callgrind and with the minimum of 15 runs. The
same initialisation runs when the wasm module is instantiated. This module is
imported by the umbrella `L4Factoidal`, so `lake build` still runs every
`#guard`, and by no executable.
-/
import L4Factoidal.Storage.BlockV5Plan

namespace L4Factoidal.Storage.BlockV5Plan

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.TermWireV2
open L4Factoidal.Storage.IndexedBlockWireV5
open L4Factoidal.Storage.IndexedBlockWireV4 (IdQuad)
open L4Factoidal.Storage.ShardManifest (zoneBytes lexLe)

/-! ## Build-time checks -/

private def pName : WfIri := ⟨"http://example.org/name", by simp [isIri]⟩
private def alice : Subject := .iri ⟨"http://example.org/alice", by simp [isIri]⟩
private def bob : Subject := .iri ⟨"http://example.org/bob", by simp [isIri]⟩

private def bigLexical : String := String.ofList (List.replicate 70000 'a')

private def sampleQuads : List (Option GraphRef × Triple) :=
  [(none, { s := alice, p := pName, o := .literal (Literal.string "hello") }),
   (none, { s := bob, p := pName, o := .literal (Literal.string bigLexical) })]

private def sample : QuadBlock := fromRdfQuads specHash sampleQuads

-- The out-of-line literal is one opaque position and is not grammed.
#guard (opaquePositions sample.dict).length == 1
#guard (literalIndexOf sample).opaqueIds == opaquePositions sample.dict
#guard (literalIndexOf sample).literalCount == 1
#guard (literalIndexOf sample).dictCount == sample.dict.size
#guard (geoIndexOf sample).dictCount == sample.dict.size

-- Both zone maps exist, are ordered, and are inside the bound.
#guard (subjectZone? sample).isSome
#guard (objectZone? sample).isSome
#guard (zones? sample).map Prod.fst == subjectZone? sample
#guard (zones? sample).map Prod.snd == objectZone? sample
#guard ((subjectZone? sample).map ShardManifest.zoneAdmitted) == some true
#guard ((objectZone? sample).map ShardManifest.zoneAdmitted) == some true

-- Every row's own key is inside the block's bounds.
#guard ((subjectZone? sample).map fun zone =>
  (subjectKeys sample).map fun keys =>
    keys.all fun key => ShardManifest.zoneMayContain zone key) == some (some true)
#guard ((objectZone? sample).map fun zone =>
  (objectKeys sample).map fun keys =>
    keys.all fun key => ShardManifest.zoneMayContain zone key) == some (some true)

-- The out-of-line literal is a candidate of every needle the LGI4 index can
-- serve, including one no inline literal of the block carries.
#guard (literalCandidates? (literalIndexOf sample) "zzz").isSome
#guard ((literalCandidates? (literalIndexOf sample) "zzz").map fun ids =>
  (opaquePositions sample.dict).all fun i => ids.contains i) == some true
#guard ((literalCandidates? (literalIndexOf sample) "hel").map fun ids =>
  (opaquePositions sample.dict).all fun i => ids.contains i) == some true

end L4Factoidal.Storage.BlockV5Plan
