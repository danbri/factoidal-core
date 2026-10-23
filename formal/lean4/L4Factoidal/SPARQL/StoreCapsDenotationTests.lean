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
law does NOT hold, and each one is a finding of step B1:

1. A list record over a list with a repeated triple (`capsOfList [a, a, b]`)
   breaks `solveNodupKeys`. So does the in-memory index of that list, and a
   list whose two entries differ only in the case of a language tag (one RDF
   term, RDF 1.2 Concepts section 3.4). The theorems state these records lawful
   under `Graph.KeyNodup` (for a dataset: `Dataset.IsSet`).
2. The union of two records that hold one triple returns it twice: `unionCaps`
   breaks `solveNodupKeys` unless the members' graphs are disjoint
   (`unionCaps_exact` has that hypothesis). The Lean tree has no live
   construction site of a union backend.
3. The delta overlay over a record that advertises an exact estimate keeps the
   flag, and its estimate overcounts under a tombstone: `overlay` over the
   in-memory index breaks `estimateExact`. `capsOfBackend` builds the overlay
   only over `capsOfCottas`, which does not advertise the flag.
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

/-! Finding 2: two members that hold one triple. -/
#guard bounds.all (fun bd => exactB (unionCaps [capsOfList [a], capsOfList [a]]) [a] bd)
#guard !nodupKeysB (unionCaps [capsOfList [a], capsOfList [a]]) patternBoundAll
#guard !nodupKeysB (capsOfBackend (.union [.list [a], .list [a]])) patternBoundAll

/-! ## The delta overlay -/

private def foldOne (es : List Storage.DeltaEntry) : DeltaResolved :=
  foldEntriesForGraph none es deltaResolvedEmpty

private def baseList : StoreCaps := capsOfList [a, b]

#guard lawsB (overlay baseList (foldOne [.add c none])) [a, b, c]
#guard lawsB (overlay baseList (foldOne [.remove a none])) [b]
#guard lawsB (overlay baseList (foldOne [.clear none, .add c none])) [c]
-- Re-adding a triple the base holds does not repeat it.
#guard lawsB (overlay baseList (foldOne [.add a none])) [a, b]

/-! Finding 3: the overlay over the in-memory index advertises an exact
estimate and overcounts. -/

private def idxOverlay : StoreCaps :=
  overlay (capsOfIndexed (OWL.RL.Index.ofGraph [a, b])) (foldOne [.remove a none])

#guard idxOverlay.flags.estimateIsExact
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

end L4Factoidal.SPARQL.StoreCapsDenotationTests
