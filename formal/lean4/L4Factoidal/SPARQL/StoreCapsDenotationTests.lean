/-
L4Factoidal.SPARQL.StoreCapsDenotationTests — build-time checks of the laws of
`RDF/StoreCapsDenotation.lean` on concrete records
(https://github.com/danbri/factoidal/issues/975, phase B, step B1).

Each law has a Bool view for one bound, with a finite graph as the denotation:

* `nodupKeysB caps b`: `solveNodupKeys` (no two RDF-term-equal rows);
* `exactB caps g b`: `solveExact` against the graph `g` (every row is a
  matching triple of `g`, and every matching triple of `g` is a row, both up to
  RDF term equality);
* `distinctCompleteB` and `distinctExactB`: the predicate list holds every
  predicate of `g` (complete), or exactly those (exact).

The positive checks hold for every builder. The negative checks record where a
law does NOT hold. Each numbered item is a finding of step B1; findings 2 and 3
were repaired on 2026-10-23 and their checks now pin the repair:

1. A list record over a list with a repeated triple (`capsOfList [a, a, b]`)
   breaks `solveNodupKeys`. So does the in-memory index of that list, and a
   list whose two entries differ only in the case of a language tag (one RDF
   term, RDF 1.2 Concepts section 3.4). The theorems state these records lawful
   under `Graph.KeyNodup` (for a dataset: `Dataset.IsSet`).
2. The union of two records that hold one triple returned it twice and counted
   it twice (`unionSolve` concatenated, `unionCountExact` summed). REPAIRED:
   the union is a set union (RDF 1.1 Semantics: the union of graphs is the set
   union), and its count and LIMIT agree with its read.
3. The delta overlay over a record that advertises an exact estimate kept the
   flag, and its estimate overcounts under a tombstone: `overlay` over the
   in-memory index broke `estimateExact`. REPAIRED: a live overlay advertises
   an inexact estimate.
4. The COTTAS reader's predicate list has no graph scope, so for a named-graph
   scope it is complete and not exact.

No executable imports this module.
-/
import L4Factoidal.SPARQL.StoreBackend
import L4Factoidal.RDF.DatasetDenotation

namespace L4Factoidal.SPARQL.StoreCapsDenotationTests

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.SPARQL.StoreBackend
open L4Factoidal.RDF.CottasCaps

/-! ## Bool views of the laws -/

/-- `solveNodupKeys` for one bound. -/
def nodupKeysB (caps : StoreCaps) (b : PatternBound) : Bool :=
  decide (((caps.solve b).map Triple.key).Nodup)

/-- `solveExact` for one bound, with the finite graph `g` as the denotation. -/
def exactB (caps : StoreCaps) (g : Graph) (b : PatternBound) : Bool :=
  (caps.solve b).all (fun u => g.mem u && boundMatches b u) &&
  g.all (fun t => !boundMatches b t || (caps.solve b).any (fun u => u.eqb t))

/-- The predicate list is complete for `g` and has no duplicate. -/
def distinctCompleteB (caps : StoreCaps) (g : Graph) : Bool :=
  match caps.distinctPredicates with
  | none => true
  | some f =>
    match f () with
    | none => true
    | some ps => decide ps.Nodup && g.all (fun t => ps.contains t.p)

/-- The predicate list is exactly the predicates of `g`. -/
def distinctExactB (caps : StoreCaps) (g : Graph) : Bool :=
  distinctCompleteB caps g &&
  match caps.distinctPredicates with
  | none => true
  | some f =>
    match f () with
    | none => true
    | some ps => ps.all (fun p => g.any (fun t => t.p == p))

/-! ## Fixtures -/

private def iriW (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"http://e.org/", by decide⟩

private def pP : WfIri := iriW "http://e.org/p"
private def pQ : WfIri := iriW "http://e.org/q"
private def sA : Subject := .iri (iriW "http://e.org/a")
private def sB : Subject := .iri (iriW "http://e.org/b")

private def a : Triple := ⟨sA, pP, .iri (iriW "http://e.org/1")⟩
private def b : Triple := ⟨sB, pP, .iri (iriW "http://e.org/2")⟩
private def c : Triple := ⟨sB, pQ, .iri (iriW "http://e.org/3")⟩
private def langEn : Term := .literal (Literal.langString "chat" "en")
private def langEN : Term := .literal (Literal.langString "chat" "EN")
private def ten : Triple := ⟨sA, pQ, langEn⟩
private def tEN : Triple := ⟨sA, pQ, langEN⟩

/-- The bounds every check runs over: unbound, each position alone, two pairs,
and a language-tagged object in both spellings. -/
private def bounds : List PatternBound :=
  [ patternBoundAll, { s := some sA }, { s := some sB }, { p := some pP }, { p := some pQ }
  , { o := some (.iri (iriW "http://e.org/2")) }, { s := some sB, p := some pQ }
  , { p := some pP, o := some (.iri (iriW "http://e.org/1")) }
  , { o := some langEn }, { o := some langEN }, { p := some pQ, o := some langEN } ]

private def lawsB (caps : StoreCaps) (g : Graph) : Bool :=
  bounds.all (fun bd => exactB caps g bd && nodupKeysB caps bd)

/-! ## The list record -/

private def gSet : Graph := [a, b, c, ten]

#guard lawsB (capsOfList gSet) gSet
#guard lawsB (capsOfList []) []

/-! Finding 1: a duplicate-row backend. The answer is exact up to RDF term
equality, and it repeats a row. -/

private def gDup : Graph := [a, a, b]

#guard bounds.all (fun bd => exactB (capsOfList gDup) gDup bd)
#guard !nodupKeysB (capsOfList gDup) patternBoundAll
#guard !nodupKeysB (capsOfList gDup) { p := some pP }
#guard nodupKeysB (capsOfList gDup) { s := some sB }

/-- Two spellings of one RDF term: `"chat"@en` and `"chat"@EN`. -/
private def gCase : Graph := [ten, tEN]

#guard bounds.all (fun bd => exactB (capsOfList gCase) gCase bd)
#guard !nodupKeysB (capsOfList gCase) patternBoundAll
#guard !nodupKeysB (capsOfList gCase) { o := some langEN }

/-! ## The in-memory index -/

#guard lawsB (capsOfIndexed (OWL.RL.Index.ofGraph gSet)) gSet
#guard bounds.all (fun bd => exactB (capsOfIndexed (OWL.RL.Index.ofGraph gDup)) gDup bd)
#guard !nodupKeysB (capsOfIndexed (OWL.RL.Index.ofGraph gDup)) patternBoundAll
-- The language-tagged object bound reads both spellings: the index does not
-- use its structural object bucket for a tagged literal.
#guard ((capsOfIndexed (OWL.RL.Index.ofGraph gCase)).solve { o := some langEN }).length == 2

/-! ## The union -/

#guard lawsB (unionCaps [capsOfList [a], capsOfList [b, c]]) [a, b, c]

/-! Finding 2 (repaired): two members that hold one triple. The union reads it
once, counts it once, and LIMIT agrees. -/
#guard lawsB (unionCaps [capsOfList [a], capsOfList [a]]) [a]
#guard lawsB (capsOfBackend (.union [.list [a], .list [a]])) [a]
#guard lawsB (unionCaps [capsOfList [a, b], capsOfList [b, c], capsOfList [a, c]]) [a, b, c]
#guard (unionCaps [capsOfList [a, b], capsOfList [b, c]]).countExact patternBoundAll == 3
#guard (unionCaps [capsOfList [a, b], capsOfList [a, b], capsOfList [c]]).solveLimited
         patternBoundAll 3 == [a, b, c]
#guard (unionCaps [capsOfList [a, b], capsOfList [a, b], capsOfList [c]]).solveLimited
         patternBoundAll 2 == [a, b]
-- one RDF term in two spellings, in two members: read once
#guard lawsB (unionCaps [capsOfList [ten], capsOfList [tEN]]) [ten]

/-! ## The delta overlay -/

private def foldOne (es : List Storage.DeltaEntry) : DeltaResolved :=
  foldEntriesForGraph none es deltaResolvedEmpty

private def baseList : StoreCaps := capsOfList [a, b]

#guard lawsB (overlay baseList (foldOne [.add c none])) [a, b, c]
#guard lawsB (overlay baseList (foldOne [.remove a none])) [b]
#guard lawsB (overlay baseList (foldOne [.clear none, .add c none])) [c]
-- Re-adding a triple the base holds does not repeat it.
#guard lawsB (overlay baseList (foldOne [.add a none])) [a, b]

/-! Finding 3 (repaired): the overlay over the in-memory index overcounts
under a tombstone, and no longer advertises an exact estimate. -/

private def idxOverlay : StoreCaps :=
  overlay (capsOfIndexed (OWL.RL.Index.ofGraph [a, b])) (foldOne [.remove a none])

#guard (capsOfIndexed (OWL.RL.Index.ofGraph [a, b])).flags.estimateIsExact
#guard !idxOverlay.flags.estimateIsExact
#guard idxOverlay.estimate patternBoundAll == 2
#guard idxOverlay.countExact patternBoundAll == 1
#guard lawsB idxOverlay [b]

/-! ## The COTTAS record -/

/-- A reader over two scopes: the default graph `[a]` and the named graph
`g` `[c]`. Its predicate list is the whole file's. -/
private def opsTwo : CottasReadOps :=
  let rows : CottasScope → Graph := fun
    | .defaultGraph => [a]
    | .named _ => [c]
  { searchTok := fun sc bd => tripleMatchesBound bd (rows sc)
  , searchLimitedTok := fun sc bd n => capsTakeN n (tripleMatchesBound bd (rows sc))
  , estimateTok := fun sc bd => (tripleMatchesBound bd (rows sc)).length
  , countExactTok := fun sc bd => (tripleMatchesBound bd (rows sc)).length
  , predicatePresent := fun pr => pr == pP || pr == pQ
  , hasDecodeFailure := fun _ => false
  , distinctPredicates := fun _ => some [pP, pQ]
  , searchTokSelective := fun sc bd _ => tripleMatchesBound bd (rows sc) }

#guard lawsB (capsOfCottas opsTwo .defaultGraph) [a]
#guard lawsB (capsOfCottas opsTwo (.named "http://e.org/g")) [c]

/-! Finding 4: complete, not exact, for a scope. -/
#guard distinctCompleteB (capsOfCottas opsTwo (.named "http://e.org/g")) [c]
#guard !distinctExactB (capsOfCottas opsTwo (.named "http://e.org/g")) [c]
#guard !distinctExactB (capsOfCottas opsTwo .defaultGraph) [a]

/-! ## The read-ops arms

`capsOfReadOps` takes the reader's own presence test. A reader that reports a
present predicate as absent breaks `presenceSound`; the theorem has the
reader's presence law as a hypothesis. -/

private def opsLying : BackendReadOps :=
  { search := fun bd => tripleMatchesBound bd [a]
  , estimate := fun bd => (tripleMatchesBound bd [a]).length
  , predicatePresent := fun _ => false }

#guard lawsB (capsOfReadOps opsLying false) [a]
#guard !(capsOfReadOps opsLying false).predicatePresent pP
#guard ((capsOfReadOps opsLying false).solve { p := some pP }).length == 1

/-! ## The RML virtual source against its materialisation

`StoreBackendDenotation.capsOfRmlSource_exact` takes two open hypotheses. These
checks test the second, `RmlVirtualIsMaterialised`: the unbounded virtual solve
and the default graph of `RML.evalMapping` hold the same triples. -/

section Rml

open L4Factoidal.RML
open L4Factoidal.JSON

private def rmlDoc : Json :=
  .array [ .object [("id", .string "1"), ("name", .string "Alice")]
         , .object [("id", .string "2"), ("name", .string "Bob")]
         , .object [("id", .string "1"), ("name", .string "Alice")] ]

private def rmlSrc : LogicalSource :=
  { path := "people.json", iterator := some "$[*]", refFormulation := "http://w3id.org/rml/JSONPath" }

private def nameTm : TriplesMap :=
  { id := "http://e.org/tm/name", source := rmlSrc
  , subject := { form := .template "http://e.org/p/{$.id}" }
  , poms := [ { predicates := [{ form := .constant (.iri (iriW "http://e.org/name")) }]
              , objects := [.term { form := .reference "$.name" } none none] } ] }

private def bnodeTm : TriplesMap :=
  { id := "http://e.org/tm/bnode", source := rmlSrc
  , subject := { form := .unknown, termType := some .blankNode }
  , poms := [ { predicates := [{ form := .constant (.iri (iriW "http://e.org/name")) }]
              , objects := [.term { form := .reference "$.name" } none none] } ] }

private def rmlVs : VirtualSource :=
  { mapping := [nameTm, bnodeTm], docs := [("people.json", rmlDoc)] }

private def materialisedDefault (vs : VirtualSource) : Graph :=
  (evalMapping vs.baseIri vs.mapping vs.docFor).filterMap (fun q =>
    match q.g with
    | none => some ({ s := q.s, p := q.p, o := q.o } : Triple)
    | some _ => none)

private def sameTriplesB (g h : Graph) : Bool :=
  g.all (fun t => h.mem t) && h.all (fun t => g.mem t)

#guard sameTriplesB (rmlSolve rmlVs patternBoundAll) (materialisedDefault rmlVs)
#guard sameTriplesB (rmlSolve { rmlVs with mapping := [nameTm] } patternBoundAll)
         (materialisedDefault { rmlVs with mapping := [nameTm] })
#guard (rmlSolve rmlVs patternBoundAll).length == 5
#guard nodupKeysB (capsOfRmlSource rmlVs) patternBoundAll

end Rml

end L4Factoidal.SPARQL.StoreCapsDenotationTests
