/-
L4Factoidal.Dataflow.PhaseDTests — checks of `Dataflow/PhaseD.lean`, evaluated
during `lake build` (https://github.com/danbri/factoidal/issues/975, phase D).

The document is the example of `docs/factoidal-corpus-coherence-975.md`
("First connected demonstration"): a TriG document with an observation named
graph (`ex:alice ex:worksFor ex:organisation`), a schema named graph
(`ex:worksFor rdfs:subPropertyOf ex:affiliatedWith`) and an empty named graph.

* The parsed dataset keeps the empty named graph.
* Selection is a parameter: with both graphs selected, the RDFS stage derives
  `ex:alice ex:affiliatedWith ex:organisation` (rdfs7) and the composed path
  answers `?x ex:affiliatedWith ?y` with `ex:alice`; with the observation graph
  only, or the default graph only, or the empty graph only, there is no
  answer.
* The ρdf stage and the OWL 2 RL stage derive the same triple; simple
  entailment does not (no RDFS rule), and it accepts a pattern with a blank
  node in place of `ex:alice`.
* The RIF stage keeps the input facts.
* SHACL: `sh:minCount 1` on `ex:worksFor` conforms; `sh:minCount 2` does not.
* Update through the stage: `CLEAR` keeps the empty named graph, `DROP` removes
  it; the input dataset value does not change.
* The empty-input RDFS axiom example: from the empty graph the RDFS closure
  holds `rdfs:subPropertyOf rdfs:subPropertyOf rdfs:subPropertyOf`.

No executable imports this module.
-/
import L4Factoidal.Dataflow.PhaseD
import L4Factoidal.SPARQL.UpdateParser

namespace L4Factoidal.Dataflow.PhaseDTests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Dataflow

private def okVal? {ε β : Type} : Except ε β → Option β
  | .ok b => some b
  | .error _ => none

private def iri! (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩

private def exAlice : WfIri := iri! "http://example.org/alice"
private def exOrg : WfIri := iri! "http://example.org/organisation"
private def exWorksFor : WfIri := iri! "http://example.org/worksFor"
private def exAffiliated : WfIri := iri! "http://example.org/affiliatedWith"
private def gObs : Subject := .iri (iri! "http://example.org/obs")
private def gSchema : Subject := .iri (iri! "http://example.org/schema")
private def gEmpty : Subject := .iri (iri! "http://example.org/empty")

private def trig : String :=
  "@prefix ex: <http://example.org/> .\n" ++
  "@prefix rdfs: <http://www.w3.org/2000/01/rdf-schema#> .\n" ++
  "ex:obs { ex:alice ex:worksFor ex:organisation . }\n" ++
  "ex:schema { ex:worksFor rdfs:subPropertyOf ex:affiliatedWith . }\n" ++
  "ex:empty { }\n"

private def doc : Document :=
  { bytes := trig.toUTF8, mediaType := "application/trig", source := "test:coherence" }

private def parsed? : Option Dataset :=
  okVal? ((decodeStage.comp (parseStage {} .rdf12 none)).run doc)

private def both : GraphSelection := { named := [gObs, gSchema] }
private def obsOnly : GraphSelection := { named := [gObs] }
private def defaultOnly : GraphSelection := { default := true }
private def emptyOnly : GraphSelection := { named := [gEmpty] }

private def affiliated : Triple := { s := .iri exAlice, p := exAffiliated, o := .iri exOrg }

private def qAff : Bgp := [{ s := .var "x", p := .iri exAffiliated, o := .var "y" }]

private theorem noCmps : ∀ c ∈ ([] : List WfIri), IsRdfMemberIri c := by
  intro c hc; cases hc

private def answers (sel : GraphSelection) : Option (List (Option Term)) :=
  (okVal? ((documentToRdfsBgp {} .rdf12 none [] [] noCmps sel qAff).run doc)).map
    (·.map (·.lookup "x"))

-- the parsed dataset keeps the empty named graph, and it is a set
#guard match parsed? with
  | some ds => ds.names.contains gEmpty && ds.names.length == 3 && ds.IsSetB
  | none => false

-- the selected graph: both named graphs give two triples; the empty graph none
#guard (parsed?.map fun ds => (ds.select both).length) == some 2
#guard (parsed?.map fun ds => (ds.select emptyOnly).length) == some 0
#guard (parsed?.map fun ds => (ds.select defaultOnly).length) == some 0

-- RDFS over the selection derives rdfs7's triple; with one graph it does not
#guard match parsed? with
  | some ds => match okVal? ((rdfsSelectStage [] [] noCmps both).run ds),
      okVal? ((rdfsSelectStage [] [] noCmps obsOnly).run ds) with
    | some c, some c1 => c.mem affiliated && !c1.mem affiliated
    | _, _ => false
  | none => false

-- the composed path: one answer, ex:alice, only when both graphs are selected
#guard answers both == some [some (.iri exAlice)]
#guard answers obsOnly == some []
#guard answers defaultOnly == some []
#guard answers emptyOnly == some []

-- ASK over the closure
#guard match parsed? with
  | some ds => match okVal? (((rdfsSelectStage [] [] noCmps both).comp (bgpAskStage qAff)).run ds) with
    | some b => b
    | none => false
  | none => false

-- ρdf and OWL 2 RL derive the same triple
#guard match parsed? with
  | some ds => match okVal? ((rhoDfSelectStage 8 both).run ds),
      okVal? ((owlRlSelectStage both).run ds) with
    | some c, some c' => c.mem affiliated && c'.mem affiliated
    | _, _ => false
  | none => false

-- simple entailment: no RDFS rule; a blank node in place of ex:alice is entailed
#guard match parsed? with
  | some ds =>
    !(okVal? ((simpleEntailsSelectStage both).run (ds, [affiliated]))).getD true &&
    (okVal? ((simpleEntailsSelectStage both).run
      (ds, [{ s := .bnode "x", p := exWorksFor, o := .iri exOrg }]))).getD false
  | none => false

-- RIF with no rules keeps the input facts
#guard match parsed? with
  | some ds => match okVal? ((rifSelectStage both [] 4).run ds) with
    | some fs => fs.length == ((ds.select both).flatMap RIF.RdfMapping.factsOfTriple).length &&
        fs.length > 0
    | none => false
  | none => false

/-! SHACL over the selection: data = the observation graph, shapes = a shapes
graph parsed from Turtle. -/

private def shapesText (n : Nat) : String :=
  "@prefix ex: <http://example.org/> .\n" ++
  "@prefix sh: <http://www.w3.org/ns/shacl#> .\n" ++
  "ex:S a sh:NodeShape ; sh:targetNode ex:alice ;\n" ++
  s!"  sh:property [ sh:path ex:worksFor ; sh:minCount {n} ] .\n"

private def shapesGraph? (n : Nat) : Option Graph :=
  (okVal? ((decodeStage.comp (parseStage {} .rdf12 none)).run
    { bytes := (shapesText n).toUTF8, mediaType := "text/turtle", source := "test:shapes" })).map
    (·.default)

#guard match parsed?, shapesGraph? 1, shapesGraph? 2 with
  | some ds, some s1, some s2 =>
    let data := ds.select obsOnly
    match okVal? ((shaclStage {}).run (data, s1)), okVal? ((shaclStage {}).run (data, s2)) with
    | some r1, some r2 => r1.conforms && !r2.conforms
    | _, _ => false
  | _, _, _ => false

/-! Update through the stage -/

private def upd? (ds : Dataset) (text : String) : Option Dataset :=
  match parseSparqlUpdate text with
  | .ok u => okVal? ((updateStage {}).run (ds, u))
  | .error _ => none

#guard match parsed? with
  | some ds =>
    match upd? ds "CLEAR GRAPH <http://example.org/empty>",
      upd? ds "DROP GRAPH <http://example.org/empty>" with
    | some a, some b => a.names.contains gEmpty && !b.names.contains gEmpty &&
        ds.names.contains gEmpty
    | _, _ => false
  | none => false

-- CLEAR of the observation graph keeps its name and removes the triple
#guard match parsed? with
  | some ds => match upd? ds "CLEAR GRAPH <http://example.org/obs>" with
    | some a => a.names.contains gObs && (a.select obsOnly).isEmpty
    | none => false
  | none => false

/-! The empty-input RDFS axiom example -/

private def spSpSp : Triple :=
  { s := .iri RDFS.rdfsSubPropertyOf, p := RDFS.rdfsSubPropertyOf, o := .iri RDFS.rdfsSubPropertyOf }

#guard match okVal? ((rdfsSelectStage [] [] noCmps defaultOnly).run Dataset.empty) with
  | some c => c.mem spSpSp
  | none => false

end L4Factoidal.Dataflow.PhaseDTests
