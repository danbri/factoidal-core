/-
L4Factoidal.Dataflow.InstancesTests — checks of `Dataflow/Instances.lean`,
evaluated during `lake build` (https://github.com/danbri/factoidal/issues/975,
phase A3).

* Decode then parse: an N-Quads document that states one quad two times gives
  a dataset with one quad; the SBM11 pack stage accepts it and the generation
  passes its check.
* Hand-over finding 1: a document with media type `text/turtle` is refused by
  the decode stage (no media-type table in the RDF layer); the label `turtle`
  is accepted. Bytes that are not UTF-8 are refused.
* Hand-over finding 3: a document with `"x"@EN` parses, and its dataset is not
  in SBM11 form (`Sbm11Folded` fails), so the end-to-end answer over the
  parsed dataset needs that premise.
* The RDFS closure stage adds the `rdf:type` triple of a domain rule.
* The identity read-back realises `ReadsWritten` (a model of the IO stage).

No executable imports this module.
-/
import L4Factoidal.Dataflow.Instances

namespace L4Factoidal.Dataflow.InstancesTests

open L4Factoidal.RDF
open L4Factoidal.Dataflow
open L4Factoidal.Storage.Sbm11.MemGen
open L4Factoidal.Storage.Sbm11.PackSpec

private def okVal? {ε β : Type} : Except ε β → Option β
  | .ok b => some b
  | .error _ => none

private def doc (mt text : String) : Document :=
  { bytes := text.toUTF8, mediaType := mt, source := "test:doc" }

private def nq : String :=
  "<http://ex.org/a> <http://ex.org/p> <http://ex.org/b> <http://ex.org/g> .\n" ++
  "<http://ex.org/a> <http://ex.org/p> <http://ex.org/b> <http://ex.org/g> .\n" ++
  "<http://ex.org/a> <http://ex.org/p> \"x\"@en .\n"

private def toDataset : Stage String Document Dataset :=
  decodeStage.comp (parseStage {} .rdf12 none)

private def parsed? (d : Document) : Option Dataset := okVal? (toDataset.run d)

-- the repeated quad is one quad
#guard ((parsed? (doc "nquads" nq)).map (·.listQuads.length)) == some 2
-- the SBM11 pack stage accepts the parsed dataset; the generation passes its check
#guard match parsed? (doc "nquads" nq) with
  | some ds => match okVal? ((sbm11PackStage 4096).run ds) with
    | some (G, _) => G.check
    | none => false
  | none => false

-- finding 1: a media type is not a format label
#guard (parsed? (doc "text/turtle" "<http://ex.org/a> <http://ex.org/p> <http://ex.org/b> .")).isNone
#guard (parsed? (doc "turtle" "<http://ex.org/a> <http://ex.org/p> <http://ex.org/b> .")).isSome
-- bytes that are not UTF-8
#guard (okVal? (decodeStage.run { bytes := ⟨#[0xff, 0xfe]⟩, mediaType := "nquads", source := "x" })).isNone

/-- The Bool form of `Sbm11Folded` on the list quads. -/
private def foldedB (ds : Dataset) : Bool :=
  ds.listQuads.all fun q => normTriple q.2 == q.2 && q.2.key == q.2

-- finding 3: `"x"@EN` is not in SBM11 form; `"x"@en` is
#guard (parsed? (doc "nquads" "<http://ex.org/a> <http://ex.org/p> \"x\"@EN .\n")).map foldedB == some false
#guard (parsed? (doc "nquads" nq)).map foldedB == some true

-- the RDFS closure stage: `p rdfs:domain C`, `a p b` gives `a rdf:type C`
private def iri (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩
private def gIn : Graph :=
  [⟨.iri (iri "http://ex.org/p"), iri "http://www.w3.org/2000/01/rdf-schema#domain", .iri (iri "http://ex.org/C")⟩,
   ⟨.iri (iri "http://ex.org/a"), iri "http://ex.org/p", .iri (iri "http://ex.org/b")⟩]
private def tType : Triple :=
  ⟨.iri (iri "http://ex.org/a"), iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#type", .iri (iri "http://ex.org/C")⟩

#guard match (rdfsClosureStage [] [] (fun _ h => absurd h List.not_mem_nil)).run gIn with
  | .ok g => g.contains tType
  | .error _ => false

/-- A model of the disk that returns the bytes it was given realises the named
assumption. -/
example : sbm11Disk.Realised (fun F => .ok F) := by
  intro F F' h
  injection h with h
  exact h.symm

end L4Factoidal.Dataflow.InstancesTests
