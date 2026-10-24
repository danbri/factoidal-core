/-
L4Factoidal.Storage.SelectedDatasetTests — checks of
`Storage/SelectedDataset.lean`, evaluated during `lake build`
(https://github.com/danbri/factoidal/issues/975, hand-over finding 6).

* The model keeps a named graph that the predicate selection empties, with no
  triple, as `Harness.Sbm11Query.selectedDataset` keeps it.
* The reference fallback's SELECT answer over the model is the answer over the
  whole dataset: a default-graph pattern, `GRAPH ?g`, `FROM` and `FROM NAMED`
  (the cases `referenceSelect_selectedModel` covers), and a `GRAPH <iri>`
  query with a graph-name selection, which the theorem does not cover.

No executable imports this module.
-/
import L4Factoidal.Storage.SelectedDataset
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.ResultsJsonFast

namespace L4Factoidal.Storage.SelectedDatasetTests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.SelectedDataset

private def iri (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩
private def tr (s p o : String) (hs : isIri s := by rfl) (hp : isIri p := by rfl)
    (ho : isIri o := by rfl) : Triple :=
  ⟨.iri (iri s hs), iri p hp, .iri (iri o ho)⟩

/-- The default graph has a `p` triple and a `q` triple; the named graph `g1`
has only a `q` triple; the named graph `g2` is empty. -/
private def D : Dataset :=
  { default := [tr "http://ex.org/a" "http://ex.org/p" "http://ex.org/b",
                tr "http://ex.org/a" "http://ex.org/q" "http://ex.org/c"]
  , named := [{ name := .iri (iri "http://ex.org/g1"),
                graph := [tr "http://ex.org/a" "http://ex.org/q" "http://ex.org/c"] },
              { name := .iri (iri "http://ex.org/g2"), graph := [] }] }

private def query? (text : String) : Option Query :=
  match parseSparql text with
  | .ok q => some q
  | .error _ => none

/-- The fallback answer over the model and over the whole dataset, as the
harness writes it (SPARQL 1.1 Query Results JSON), with the number of rows. -/
private def both (text : String) : Option ((String × Nat) × (String × Nat)) :=
  (query? text).map fun q =>
    let a := referenceSelect {} q (queryDataset q (selectedModel q D))
    let b := referenceSelect {} q (queryDataset q D)
    (((QueryResult.bindings q.projectedVars a).toSrjFast, a.length),
     ((QueryResult.bindings q.projectedVars b).toSrjFast, b.length))

private def agrees (text : String) : Bool :=
  match both text with
  | some (a, b) => a == b
  | none => false

private def rows (text : String) : Option Nat :=
  (both text).map (·.2.2)

-- the predicate selection empties `g1`; the model keeps it with no triple
#guard match query? "SELECT ?g WHERE { GRAPH ?g { ?s <http://ex.org/p> ?o } }" with
  | some q => (selectedModel q D).named.map (·.graph.length) == [0, 0]
  | none => false
#guard match query? "SELECT ?s WHERE { ?s <http://ex.org/p> ?o }" with
  | some q => (selectedModel q D).default.length == 1
  | none => false

-- the answers (covered by `referenceSelect_selectedModel`)
#guard agrees "SELECT ?s WHERE { ?s <http://ex.org/p> ?o }"
#guard rows "SELECT ?s WHERE { ?s <http://ex.org/p> ?o }" == some 1
#guard agrees "SELECT ?g WHERE { GRAPH ?g { ?s <http://ex.org/p> ?o } }"
#guard rows "SELECT ?g WHERE { GRAPH ?g { ?s <http://ex.org/p> ?o } }" == some 0
#guard agrees "SELECT ?g WHERE { GRAPH ?g { } }"
#guard rows "SELECT ?g WHERE { GRAPH ?g { } }" == some 2
#guard agrees "SELECT ?s FROM <http://ex.org/g1> WHERE { ?s <http://ex.org/q> ?o }"
#guard rows "SELECT ?s FROM <http://ex.org/g1> WHERE { ?s <http://ex.org/q> ?o }" == some 1
#guard agrees "SELECT ?g FROM NAMED <http://ex.org/g1> WHERE { GRAPH ?g { ?s <http://ex.org/p> ?o } }"
#guard agrees "SELECT ?g FROM NAMED <http://ex.org/g2> WHERE { GRAPH ?g { } }"
#guard rows "SELECT ?g FROM NAMED <http://ex.org/g2> WHERE { GRAPH ?g { } }" == some 1

-- a graph-name selection (not covered by the theorem): the model drops the
-- default graph and `g2`
#guard match query? "SELECT ?s WHERE { GRAPH <http://ex.org/g1> { ?s <http://ex.org/q> ?o } }" with
  | some q => (selectedModel q D).default.isEmpty && (selectedModel q D).named.length == 1
  | none => false
#guard agrees "SELECT ?s WHERE { GRAPH <http://ex.org/g1> { ?s <http://ex.org/q> ?o } }"
#guard rows "SELECT ?s WHERE { GRAPH <http://ex.org/g1> { ?s <http://ex.org/q> ?o } }" == some 1

end L4Factoidal.Storage.SelectedDatasetTests
