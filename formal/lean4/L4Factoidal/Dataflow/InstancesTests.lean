/-
L4Factoidal.Dataflow.InstancesTests — checks of `Dataflow/Instances.lean`,
evaluated during `lake build` (https://github.com/danbri/factoidal/issues/975,
phase A3).

* Decode then parse: an N-Quads document that states one quad two times gives
  a dataset with one quad; the SBM11 pack stage accepts it and the generation
  passes its check.
* Hand-over finding 1 (closed): the decode stage reads the media type
  (`RDF.formatOfDocument`): `text/turtle` with a `charset` parameter is
  accepted; a format label (`turtle`) is not a media type and is refused; with
  no media type the extension of the source names the format. Bytes that are
  not UTF-8 are refused.
* Hand-over finding 4 (closed): `documentToSolutions` ends at `SolutionSeq`.
  A default-graph `SELECT *` over the N-Quads document gives one solution
  mapping, the literal `"x"@en`; a repeated triple gives one; no match gives
  none.
* Hand-over finding 6: the reference fallback of `l4sbm11 query` reads a
  dataset from the generation and runs the planner SELECT stage on it
  (`sbm11PlannerSelect`); with the read model that returns the whole
  generation, the planner answer has one solution.
* Hand-over finding 3: a document with `"x"@EN` parses, and its dataset is not
  in SBM11 form (`Sbm11Folded` fails), so the end-to-end answer over the
  parsed dataset needs that premise.
* The RDFS closure stage adds the `rdf:type` triple of a domain rule.
* The identity read-back realises `ReadsWritten` (a model of the IO stage).

No executable imports this module.
-/
import L4Factoidal.Dataflow.Instances
import L4Factoidal.SPARQL.Parser

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
#guard ((parsed? (doc "application/n-quads" nq)).map (·.listQuads.length)) == some 2
-- the SBM11 pack stage accepts the parsed dataset; the generation passes its check
#guard match parsed? (doc "application/n-quads" nq) with
  | some ds => match okVal? ((sbm11PackStage 4096).run ds) with
    | some (G, _) => G.check
    | none => false
  | none => false

-- finding 1: the media type names the format; a format label is not a media type
#guard (parsed? (doc "text/turtle; charset=utf-8" "<http://ex.org/a> <http://ex.org/p> <http://ex.org/b> .")).isSome
#guard (parsed? (doc "turtle" "<http://ex.org/a> <http://ex.org/p> <http://ex.org/b> .")).isNone
#guard ((okVal? (decodeStage.run (doc "application/trig" "{}"))).map (·.1)) == some .trig
-- no media type: the extension of the source
#guard ((okVal? (decodeStage.run { bytes := nq.toUTF8, mediaType := "", source := "data/d.nq" })).map (·.1)) == some .nquads
#guard (okVal? (decodeStage.run { bytes := nq.toUTF8, mediaType := "", source := "data/d" })).isNone
-- bytes that are not UTF-8
#guard (okVal? (decodeStage.run { bytes := ⟨#[0xff, 0xfe]⟩, mediaType := "application/n-quads", source := "x" })).isNone

/-- The Bool form of `Sbm11Folded` on the list quads. -/
private def foldedB (ds : Dataset) : Bool :=
  ds.listQuads.all fun q => normTriple q.2 == q.2 && q.2.key == q.2

-- finding 3: `"x"@EN` is not in SBM11 form; `"x"@en` is
#guard (parsed? (doc "application/n-quads" "<http://ex.org/a> <http://ex.org/p> \"x\"@EN .\n")).map foldedB == some false
#guard (parsed? (doc "application/n-quads" nq)).map foldedB == some true

/-! ### Finding 4: document bytes to a solution sequence -/

/-- The WHERE pattern of a SELECT query, as `IdQuery.translate` puts it in a
nested plan. -/
private def patOf (text : String) : SPARQL.QueryPattern :=
  match L4Factoidal.SPARQL.parseSparql text with
  | .ok q => q.pattern.rewriteBnodes
  | .error _ => .empty

private def planOf (p : SPARQL.QueryPattern) : L4Factoidal.Storage.Sbm11.IdQuery.Plan :=
  { (default : L4Factoidal.Storage.Sbm11.IdQuery.Plan) with nested := some p, dataset := none }

private def idRead : FileGen → Except String FileGen := fun F => .ok F
private theorem idRead_realised : sbm11Disk.Realised idRead := by
  intro F F' h
  injection h with h
  exact h.symm

private def solutionsOf (d : Document) (q : String) : Option SPARQL.SolutionSeq :=
  let p := patOf q
  okVal? ((documentToSolutions {} .rdf12 none 4096 idRead idRead_realised {} none (planOf p) p
    rfl rfl).run d)

private def spo : String := "SELECT * WHERE { ?s ?p ?o }"

-- the default graph of `nq` holds one triple (the other quad is in a named graph)
#guard ((solutionsOf (doc "application/n-quads" nq) spo).map List.length) == some 1
#guard match solutionsOf (doc "application/n-quads" nq) spo with
  | some [mu] => match mu.lookup "o" with
    | some (.literal l) => l.val.lexicalForm == "x" && l.val.langTag == some "en"
    | _ => false
  | _ => false
-- a repeated triple is one solution mapping; a pattern with no match gives none.
-- (`#guard` runs in the interpreter, which has no native `Prim.Bytes`; a table
-- of two or more rows needs it, so answers with several rows are checked by the
-- SBM11 gate and census, `tests/sbm11/`, not here.)
#guard ((solutionsOf (doc "text/turtle"
  "<http://ex.org/a> <http://ex.org/p> <http://ex.org/b> . <http://ex.org/a> <http://ex.org/p> <http://ex.org/b> .")
  spo).map List.length) == some 1
#guard ((solutionsOf (doc "application/n-quads" nq) "SELECT * WHERE { ?s <http://ex.org/q> ?o }").map List.length) == some 0

/-! ### Finding 6: SBM11 generation to the planner SELECT stage -/

/-- The model of the read of the reference fallback that returns the whole
generation. -/
private def readAll : MemGen × FileGen → Except String Dataset := fun gf => .ok gf.1.denote
private theorem readAll_realised (keep : Triple → Bool) : (sbm11SelectedRead keep).Realised readAll := by
  intro gf dS h
  injection h with h
  subst h
  rfl

private def plannerOf (d : Document) (q : String) : Option SPARQL.SolutionSeq :=
  match L4Factoidal.SPARQL.parseSparql q, parsed? d with
  | .ok query, some ds =>
    match okVal? ((sbm11PackStage 4096).run ds) with
    | some gf => okVal? ((sbm11PlannerSelect (fun _ => true) readAll (readAll_realised _) {} query).run gf)
    | none => none
  | _, _ => none

#guard ((plannerOf (doc "application/n-quads" nq) spo).map List.length) == some 1

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
