/-
L4Factoidal.Dataflow.SourcesTests — for each source of `Dataflow/Sources.lean`
(the dataset handle after operations, SPARQL Update, a reasoner, a union of
shards), a query over the source's record through the shipped evaluator: the
backend path answers, and its answer equals the reference answer
(`referenceAnswer`) over the record's reference dataset, whose denotation is
the source's `den` (`query_sound`). SELECT rows are compared up to order.
-/
import L4Factoidal.Dataflow.Sources
import L4Factoidal.Dataflow.EndToEnd
import L4Factoidal.SPARQL.UpdateParser

namespace L4Factoidal.Dataflow.SourcesTests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Dataflow

private def certified? (text : String) : Option CertifiedDataset :=
  match nquadsDocumentReader.certified { text } with
  | .ok c => some c
  | .error _ => none

private def source? (text : String) : Option Sourced := (certified? text).map Sourced.ofCertified

/-- The same elements with the same multiplicities: equal lengths, and each
element of `a` occurs as often in `b` as in `a`. Loops only (`count`, `all`):
`List.isPerm` reaches `List.erase`, a recursion on the list length
(`tools/lean-tail-recursion-audit.py --gate`). -/
private def sameMultiset {α} [BEq α] (a b : List α) : Bool :=
  a.length == b.length && a.all (fun x => a.count x == b.count x)

private def sameAnswer : Answer → Answer → Bool
  | .select h1 r1, .select h2 r2 => sameMultiset h1 h2 && sameMultiset r1 r2
  | a, b => a == b

/-- The backend path answers the query over the record, and the answer is the
reference answer over the reference dataset. -/
private def agrees (s? : Option Sourced) (qs : String) : Bool :=
  match s?, parseSparql qs none .v11 with
  | some s, .ok q =>
    let x := s.input {} q
    let onBackend := match q.form with
      | .select _ => (backendSelect? x).isSome
      | .ask => (backendAsk? x).isSome
      | _ => false
    onBackend && sameAnswer (shippedEvaluator.run x) (referenceAnswer x)
  | _, _ => false

private def ask? (s? : Option Sourced) (qs : String) : Option Bool :=
  match s?, parseSparql qs none .v11 with
  | some s, .ok q => match shippedEvaluator.run (s.input {} q) with
    | .ask b => some b
    | _ => none
  | _, _ => none

private def rows? (s? : Option Sourced) (qs : String) : Option Nat :=
  match s?, parseSparql qs none .v11 with
  | some s, .ok q => match shippedEvaluator.run (s.input {} q) with
    | .select _ rs => some rs.length
    | _ => none
  | _, _ => none

private def iri (s : String) (h : isIri s = true := by decide) : WfIri := ⟨s, h⟩

private def base : String :=
  "<http://e/s> <http://e/p> <http://e/o> .\n" ++
  "<http://e/s> <http://e/p> \"x\" <http://e/g> .\n" ++
  "_:b <http://e/p> <http://e/o2> _:k .\n"

/-! ## (b) The dataset handle after operations -/

private def addQ : Quad := (some (iri "http://e/h"), ⟨.iri (iri "http://e/t"), iri "http://e/p", .iri (iri "http://e/o")⟩)
private def delQ : Quad := (some (iri "http://e/g"), ⟨.iri (iri "http://e/s"), iri "http://e/p", .literal (Literal.string "x")⟩)
private def addD : Quad := (none, ⟨.iri (iri "http://e/s"), iri "http://e/q", .iri (iri "http://e/o")⟩)

private def handled : Option Sourced :=
  (certified? base).map fun c => handleSource c [.add [addQ, addD], .delete [delQ]]

#guard agrees handled "SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }"
#guard agrees handled "SELECT * WHERE { ?s ?p ?o }"
#guard agrees handled "ASK { GRAPH <http://e/h> { <http://e/t> ?p ?o } }"
#guard agrees handled "ASK { GRAPH <http://e/g> { ?s ?p \"x\" } }"
-- the add is visible, the delete removed the triple, and the emptied graph
-- keeps its name (SPARQL 1.1 Update section 3.1.2)
#guard ask? handled "ASK { GRAPH <http://e/h> { <http://e/t> ?p ?o } }" = some true
#guard ask? handled "ASK { GRAPH <http://e/g> { ?s ?p \"x\" } }" = some false
#guard ask? handled "ASK { <http://e/s> <http://e/q> ?o }" = some true
#guard rows? handled "SELECT * WHERE { ?s ?p ?o }" = some 2
#guard (match handled with
  | some s => s.ref.names.contains (.iri (iri "http://e/g")) | none => false)

/-! ## (c) A SPARQL 1.1 Update -/

private def updated (text : String) : Option Sourced :=
  match source? base, parseSparqlUpdate text with
  | some s, .ok u =>
    match hu : applyUpdateIn {} s.ref u with
    | .ok _ => some (updateSource {} s u hu)
    | .error _ => none
  | _, _ => none

private def upd1 : Option Sourced :=
  updated ("INSERT { GRAPH <http://e/n> { ?s <http://e/r> ?o } } WHERE { ?s <http://e/p> ?o } ;\n" ++
    "DELETE DATA { <http://e/s> <http://e/p> <http://e/o> }")

#guard upd1.isSome
#guard agrees upd1 "SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }"
-- After the DELETE DATA the default graph is empty. The backend's SELECT *
-- header over no rows is `[]` (`collectVarsInOrder`), the reference header is
-- `[s, p, o]` (`projectedVars`): the header gap that `Dataflow/Evaluator.lean`
-- lists under "Not claimed". The rows agree (none).
#guard (match upd1, parseSparql "SELECT * WHERE { ?s ?p ?o }" none .v11 with
  | some s, .ok q =>
    let x := s.input {} q
    (match shippedEvaluator.run x, referenceAnswer x with
     | .select h1 r1, .select h2 r2 => h1 == [] && h2 == ["s", "p", "o"] && r1.isEmpty && r2.isEmpty
     | _, _ => false)
  | _, _ => false)
#guard agrees upd1 "SELECT ?s ?p ?o WHERE { ?s ?p ?o }"
#guard agrees upd1 "ASK { GRAPH <http://e/n> { <http://e/s> <http://e/r> <http://e/o> } }"
#guard ask? upd1 "ASK { GRAPH <http://e/n> { <http://e/s> <http://e/r> <http://e/o> } }" = some true
#guard ask? upd1 "ASK { <http://e/s> <http://e/p> <http://e/o> }" = some false
#guard agrees (updated "DROP GRAPH <http://e/g>") "SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }"
#guard rows? (updated "DROP GRAPH <http://e/g>") "SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }" = some 1

/-! ## (d) A reasoner -/

private def tbox : String :=
  "<http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/C1> .\n" ++
  "<http://e/C1> <http://www.w3.org/2000/01/rdf-schema#subClassOf> <http://e/C2> .\n" ++
  "<http://e/a> <http://e/knows> <http://e/b> .\n" ++
  "<http://e/knows> <http://www.w3.org/2000/01/rdf-schema#domain> <http://e/Person> .\n"

private def reasoned (r : SoundReasoner) : Option Sourced :=
  (source? tbox).map fun s => s.reason r

private def isA (c : String) : String :=
  s!"ASK \{ <http://e/a> <http://www.w3.org/1999/02/22-rdf-syntax-ns#type> <http://e/{c}> }"

#guard agrees (reasoned rhoDfReasoner) (isA "C2")
#guard ask? (reasoned rhoDfReasoner) (isA "C2") = some true
#guard ask? (reasoned rhoDfReasoner) (isA "Person") = some true
#guard ask? (source? tbox) (isA "C2") = some false
#guard agrees (reasoned owlRlReasoner) (isA "C2")
#guard ask? (reasoned owlRlReasoner) (isA "C2") = some true
#guard agrees (reasoned rhoDfReasoner) "SELECT ?c WHERE { <http://e/a> a ?c }"
#guard agrees (reasoned (rdfsReasoner (withMinimalD []))) "SELECT ?c WHERE { <http://e/a> a ?c }"
-- the reasoner's record has no named graph
#guard rows? (reasoned rhoDfReasoner) "SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }" = some 0

/-! ## (e) A union of shards -/

private def shardA : String :=
  "<http://e/s> <http://e/p> <http://e/o> .\n" ++
  "<http://e/s> <http://e/p> \"a\" <http://e/g> .\n" ++
  "<http://e/s> <http://e/p> \"onlyA\" <http://e/ga> .\n"

private def shardB : String :=
  "<http://e/s> <http://e/p> <http://e/o> .\n" ++
  "<http://e/t> <http://e/p> \"b\" <http://e/g> .\n" ++
  "<http://e/t> <http://e/p> \"onlyB\" _:gb .\n"

private def shardC : String := "<http://e/u> <http://e/p> \"c\" <http://e/g> .\n"

private def unioned : Option Sourced :=
  match source? shardA, source? shardB with
  | some a, some b => some (a.union b)
  | _, _ => none

private def shards : Option Sourced :=
  match source? shardA, source? shardB, source? shardC with
  | some a, some b, some c => some (a.unionAll [b, c])
  | _, _, _ => none

#guard agrees unioned "SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }"
#guard agrees unioned "SELECT * WHERE { ?s ?p ?o }"
#guard agrees unioned "SELECT ?s WHERE { GRAPH <http://e/g> { ?s ?p ?o } }"
#guard agrees unioned "ASK { GRAPH ?g { <http://e/t> ?p \"onlyB\" } }"
#guard agrees shards "SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }"
#guard agrees shards "SELECT ?s WHERE { GRAPH <http://e/g> { ?s ?p ?o } }"
-- one default triple (both shards hold it), five named triples, three in <g>
#guard rows? unioned "SELECT * WHERE { ?s ?p ?o }" = some 1
#guard rows? unioned "SELECT * WHERE { GRAPH ?g { ?s ?p ?o } }" = some 4
#guard rows? shards "SELECT * WHERE { GRAPH <http://e/g> { ?s ?p ?o } }" = some 3
-- the shared graph name has one merged backend; the names are distinct
#guard (match unioned with
  | some s => (s.store.backend.named.map (·.name)).length == 3
  | none => false)

/-! ## (f) A store read as the default graph -/

private def graphOf? (text : String) : Option Graph := (certified? text).map (·.val.default)

private def storeSourced : Option Sourced :=
  match graphOf? "<http://e/s> <http://e/p> <http://e/o> .\n<http://e/s> <http://e/p> \"x\" .\n",
    graphOf? "<http://e/t> <http://e/p> <http://e/o> .\n<http://e/s> <http://e/p> <http://e/o> .\n" with
  | some g1, some g2 =>
    if h1 : g1.KeyNodup then
      if h2 : g2.KeyNodup then
        some (Sourced.ofStore (LawfulStore.union [LawfulStore.ofIndexed g1 h1, LawfulStore.ofIndexed g2 h2]))
      else none
    else none
  | _, _ => none

#guard storeSourced.isSome
#guard agrees storeSourced "SELECT ?s ?o WHERE { ?s <http://e/p> ?o }"
#guard agrees storeSourced "ASK { <http://e/t> ?p ?o }"
#guard rows? storeSourced "SELECT ?s ?o WHERE { ?s <http://e/p> ?o }" = some 3

end L4Factoidal.Dataflow.SourcesTests
