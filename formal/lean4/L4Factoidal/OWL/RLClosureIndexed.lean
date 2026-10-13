/-
L4Factoidal.OWL.RLClosureIndexed — the OWL 2 RL/RDF closure over an
INDEXED triple store, with a proof that it computes the SAME list as
`RLClosure.closure`.

`RLClosure.lean` reads every premise by scanning the whole graph
(`withPred g p = g.filter …`). That is the specification-level lookup;
it costs O(|g|) per lookup, so a round over a 3 000-triple ontology
costs minutes and the W3C cases WebOnt-miscellaneous-001/002/011 hit
the 20 s budget before finishing ONE round (measured 2026-08-22, see
`PORT_NOTES.md`). The F* tree solved the same problem for RDFS with
`RDFS.Closure.SemiNaive.fst`; this file is the Lean counterpart for
OWL RL.

## Design: one row body, two premise stores

Each of the 61 row functions is written ONCE here, over an abstract
`Store` — a record holding the graph list and the six premise lookups
(`withPred`, `withSubj`, `withObj`, `withSubjPred`, `withPredObj`,
`memB`). Two stores exist:

* `Store.ofGraph g` packs `RLClosure`'s list scans. Every row applied
  to it is DEFINITIONALLY the `RLClosure` row (`eqRepSForS_ofGraph :
  eqRepSForS (Store.ofGraph g) d = eqRepSFor g d := rfl`, and so on
  for all 61 rows and the 13 clash rows). The per-row soundness
  lemmas of `RLTheorems.lean` therefore apply unchanged.
* `Store.ofIndex i` packs the hash-index lookups of an `Index`.

`Index.Wf i g` says the index is a faithful picture of the list `g`:
its array IS `g`, its membership set decides `memB g`, and each
bucket lookup returns EXACTLY the corresponding list filter, in the
same order. Under `Wf`, `Store.ofIndex i = Store.ofGraph g`
(`Store.ofIndex_eq`), so a round over the index produces the same
conclusion list as a round over the graph, the insertion of those
conclusions preserves `Wf` against `addAll`, and the fuel loop takes
the same branch at every round. The result:

    closureI_toGraph :
      (closureI (Index.ofGraph g) fuel).toGraph = closure g fuel

a LIST equality, at every fuel — stronger than the set equality the
task asked for; set membership, soundness against `Derives` and the
clash verdict follow as corollaries.

## Evaluation strategy and cost model

Evaluation is NAIVE with indexed joins, not semi-naive: every round
drives every row from every triple of the round's input snapshot,
exactly as `RLClosure.step` does. That choice is what makes the bridge
theorem a per-round list equality instead of a fixpoint argument; it
is also sufficient for the corpus (see `PORT_NOTES.md` for the
measured before/after — 0 cap hits at the same 20 s budget).

Cost model (hash operations are expected O(1); `n` = triples in the
round's input, `E` = conclusions emitted before deduplication):

* `Index.insert`: one `Array.push`, one `HashSet.insert`, five
  `HashMap.getD` + `insert` with a list cons — O(1).
* a bucket lookup: O(1) + O(result) for the reversal.
* `memB`: O(1).
* one round: 61 guard checks per input triple (string equalities on
  the predicate) + the joins, each proportional to its own output,
  + O(E) deduplication — O(n + E) instead of the list engine's
  O(n · E · n)-ish (each join a scan, each dedup a scan).
* rounds: at most the derivation depth of the graph (the loop stops
  at the first round that adds nothing), the same count as
  `RLClosure.closure`.

Buckets hold their triples in REVERSE insertion order (a cons per
insert is O(1) and needs no in-place array update); the lookup
reverses, which costs no more than consuming the result does. That is
what makes the bucket equal to the list filter as a list, not just as
a set.

## What is NOT here

No semi-naive delta evaluation and no rule stratification. Both would
change which triples each ROUND emits (not which triples the FIXPOINT
holds), so their bridge theorem is an equality at saturation, which is
a different and longer proof. They are the next step if a corpus ever
needs them; the measurements in `PORT_NOTES.md` say this one does not.
-/
import L4Factoidal.OWL.RLClosure
import Std.Data.HashMap
import Std.Data.HashSet

namespace L4Factoidal.OWL.RL

open L4Factoidal.RDF

/-! ## Section 1 — the abstract premise store -/

/-- The premise lookups a row reads, packaged. `graph` is the round's
input as a list — the rows that enumerate every subject (cls-int1,
prp-spo2) and the collection-walk fuel read it. -/
structure Store where
  graph        : Graph
  withPred     : WfIri → List Triple
  withSubj     : Subject → List Triple
  withObj      : Term → List Triple
  withSubjPred : Subject → WfIri → List Triple
  withPredObj  : WfIri → Term → List Triple
  memB         : Triple → Bool

/-- The list-scan store: `RLClosure`'s lookups, verbatim. -/
def Store.ofGraph (g : Graph) : Store :=
  { graph := g,
    withPred := RL.withPred g, withSubj := RL.withSubj g, withObj := RL.withObj g,
    withSubjPred := RL.withSubjPred g, withPredObj := RL.withPredObj g,
    memB := RL.memB g }

/-! ## Section 2 — the index -/

/-- The indexed triple store. `all` is the graph in insertion order;
`set` decides exact membership; the five maps are the SPO-style
access paths the rows use, each bucket holding the reversed filter. -/
structure Index where
  all  : Array Triple
  set  : Std.HashSet Triple
  byS  : Std.HashMap Subject (List Triple)
  byP  : Std.HashMap WfIri (List Triple)
  /-- Exact predicate-match counts, including duplicates. The certificate
      covers arbitrary bucket contents, without a graph well-formedness
      assumption. This makes planner estimates independent of bucket size. -/
  byPCount : Std.HashMap WfIri Nat
  byPCount_valid : ∀ p, byPCount.getD p 0 =
    ((byP.getD p []).filter (fun t => p == t.p)).length
  byO  : Std.HashMap Term (List Triple)
  bySP : Std.HashMap (Subject × WfIri) (List Triple)
  byPO : Std.HashMap (WfIri × Term) (List Triple)

namespace Index

def empty : Index :=
  { all := #[], set := ∅, byS := ∅, byP := ∅, byO := ∅, bySP := ∅, byPO := ∅,
    byPCount := ∅,
    byPCount_valid := by intro p; simp }

/-- The graph the index pictures, in insertion order. -/
def toGraph (i : Index) : Graph := i.all.toList

def memB (i : Index) (t : Triple) : Bool := i.set.contains t
def withSubj (i : Index) (s : Subject) : List Triple := (i.byS.getD s []).reverse
def withPred (i : Index) (p : WfIri) : List Triple := (i.byP.getD p []).reverse
def withObj (i : Index) (o : Term) : List Triple := (i.byO.getD o []).reverse
def withSubjPred (i : Index) (s : Subject) (p : WfIri) : List Triple :=
  (i.bySP.getD (s, p) []).reverse
def withPredObj (i : Index) (p : WfIri) (o : Term) : List Triple :=
  (i.byPO.getD (p, o) []).reverse

/-- Append a triple unconditionally (the index of `g ++ [t]`). -/
def push (i : Index) (t : Triple) : Index :=
  { all  := i.all.push t,
    set  := i.set.insert t,
    byS  := i.byS.insert t.s (t :: i.byS.getD t.s []),
    byP  := i.byP.insert t.p (t :: i.byP.getD t.p []),
    byPCount := i.byPCount.insert t.p (i.byPCount.getD t.p 0 + 1),
    byPCount_valid := by
      intro p
      simp only [Std.HashMap.getD_insert]
      by_cases h : t.p = p
      · subst p
        simp [i.byPCount_valid]
      · have hb : (t.p == p) = false := by simpa [Subtype.ext_iff] using h
        simp [hb, i.byPCount_valid],
    byO  := i.byO.insert t.o (t :: i.byO.getD t.o []),
    bySP := i.bySP.insert (t.s, t.p) (t :: i.bySP.getD (t.s, t.p) []),
    byPO := i.byPO.insert (t.p, t.o) (t :: i.byPO.getD (t.p, t.o) []) }

/-- Append every triple of a list unconditionally (the index of
`g ++ ts`). -/
def pushAll (i : Index) : List Triple → Index
  | []      => i
  | t :: ts => pushAll (i.push t) ts

/-- The index of a graph — duplicates and all, so that `toGraph` is
the input list itself. -/
def ofGraph (g : Graph) : Index := pushAll empty g

/-- Set-wise insertion with EXACT equality — the counterpart of
`RLClosure.addOne`. -/
def insert (i : Index) (t : Triple) : Index :=
  if i.memB t then i else i.push t

/-- The counterpart of `RLClosure.addAll`. -/
def insertAll (i : Index) : List Triple → Index
  | []      => i
  | t :: ts => insertAll (i.insert t) ts

end Index

/-- The hash-lookup store over an index. -/
def Store.ofIndex (i : Index) : Store :=
  { graph := i.toGraph,
    withPred := i.withPred, withSubj := i.withSubj, withObj := i.withObj,
    withSubjPred := i.withSubjPred, withPredObj := i.withPredObj,
    memB := i.memB }

/-! ## Section 3 — the collection walks and batched premises, over a
store -/

def listElemsS (s : Store) : Term → Nat → List Term
  | _,    0     => []
  | head, n + 1 =>
      (asSubject head).flatMap (fun node =>
        (s.withSubjPred node rdfFirst).map (fun u => u.o) ++
        (s.withSubjPred node rdfRest).flatMap (fun r => listElemsS s r.o n))

def listCellsS (s : Store) : Term → Nat → List Subject
  | _,    0     => []
  | head, n + 1 =>
      (asSubject head).flatMap (fun node =>
        node :: (s.withSubjPred node rdfRest).flatMap
          (fun r => listCellsS s r.o n))

def listSeqsS (s : Store) : Term → Nat → List (List Term)
  | _,    0     => []
  | head, n + 1 =>
    if head == Term.iri rdfNil then [[]]
    else
      (asSubject head).flatMap (fun node =>
        (s.withSubjPred node rdfFirst).flatMap (fun f =>
          (s.withSubjPred node rdfRest).flatMap (fun r =>
            (listSeqsS s r.o n).map (fun rest => f.o :: rest))))

def typesAllBS (s : Store) (y : Subject) (cs : List Term) : Bool :=
  cs.all (fun c => s.memB ⟨y, rdfType, c⟩)

def sharesKeyValuesBS (s : Store) (x y : Subject) (ps : List WfIri) : Bool :=
  ps.all (fun p => (s.withSubjPred x p).any (fun ux => s.memB ⟨y, p, ux.o⟩))

def chainTargetsS (s : Store) : Subject → List WfIri → List Term
  | start, []       => [start.toTerm]
  | start, [p]      => (s.withSubjPred start p).map (fun u => u.o)
  | start, p :: rest =>
      (s.withSubjPred start p).flatMap (fun u =>
        (asSubject u.o).flatMap (fun mid => chainTargetsS s mid rest))

/-! ## Section 4 — the rows, over a store

Same bodies as `RLClosure` Section 5, with the lookups read from the
store. -/

def eqRefSForS (_s : Store) (d : Triple) : List Triple :=
  [⟨d.s, owlSameAs, d.s.toTerm⟩]

def eqRefPForS (_s : Store) (d : Triple) : List Triple :=
  [⟨Subject.iri d.p, owlSameAs, Term.iri d.p⟩]

def eqRefOForS (_s : Store) (d : Triple) : List Triple :=
  (asSubject d.o).map (fun os => ⟨os, owlSameAs, os.toTerm⟩)

def eqSymForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (asSubject d.o).map (fun ys => ⟨ys, owlSameAs, d.s.toTerm⟩)
  else []

def eqTransForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (asSubject d.o).flatMap (fun ys =>
      (s.withSubjPred ys owlSameAs).map (fun u => ⟨d.s, owlSameAs, u.o⟩))
  else []

def eqRepSForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (asSubject d.o).flatMap (fun s' =>
      (s.withSubj d.s).map (fun u => ⟨s', u.p, u.o⟩))
  else []

def eqRepPForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (subjIri d.s).flatMap (fun p =>
        (asIri d.o).flatMap (fun p' =>
          (s.withPred p).map (fun u => ⟨u.s, p', u.o⟩)))
  else []

def eqRepOForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlSameAs then
    (s.withObj d.s.toTerm).map (fun u => ⟨u.s, u.p, d.o⟩)
  else []

def prpDomForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsDomain then
    (subjIri d.s).flatMap (fun p => (s.withPred p).map (fun u => ⟨u.s, rdfType, d.o⟩))
  else []

def prpRngForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsRange then
    (subjIri d.s).flatMap (fun p =>
        (s.withPred p).flatMap (fun u =>
          (asSubject u.o).map (fun ys => ⟨ys, rdfType, d.o⟩)))
  else []

def prpFpForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlFunctionalProperty then
    (subjIri d.s).flatMap (fun p =>
        (s.withPred p).flatMap (fun u1 =>
          (asSubject u1.o).flatMap (fun y1s =>
            (s.withSubjPred u1.s p).map (fun u2 => ⟨y1s, owlSameAs, u2.o⟩))))
  else []

def prpIfpForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlInverseFunctionalProperty then
    (subjIri d.s).flatMap (fun p =>
        (s.withPred p).flatMap (fun u1 =>
          (s.withPredObj p u1.o).map (fun u2 =>
            ⟨u1.s, owlSameAs, u2.s.toTerm⟩)))
  else []

def prpSympForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlSymmetricProperty then
    (subjIri d.s).flatMap (fun p =>
        (s.withPred p).flatMap (fun u =>
          (asSubject u.o).map (fun ys => ⟨ys, p, u.s.toTerm⟩)))
  else []

def prpTrpForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlTransitiveProperty then
    (subjIri d.s).flatMap (fun p =>
        (s.withPred p).flatMap (fun u1 =>
          (asSubject u1.o).flatMap (fun ys =>
            (s.withSubjPred ys p).map (fun u2 => ⟨u1.s, p, u2.o⟩))))
  else []

def prpSpo1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsSubPropertyOf then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (s.withPred p1).map (fun u => ⟨u.s, p2, u.o⟩)))
  else []

def prpSpo2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlPropertyChainAxiom then
    (subjIri d.s).flatMap (fun p =>
      (listSeqsS s d.o (listFuel s.graph)).flatMap (fun terms =>
        (nonEmpty (allIris terms)).flatMap (fun preds =>
          (subjectsOf s.graph).flatMap (fun x1 =>
            (chainTargetsS s x1 preds).map (fun xn => ⟨x1, p, xn⟩)))))
  else []

def prpEqp1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlEquivalentProperty then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (s.withPred p1).map (fun u => ⟨u.s, p2, u.o⟩)))
  else []

def prpEqp2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlEquivalentProperty then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (s.withPred p2).map (fun u => ⟨u.s, p1, u.o⟩)))
  else []

def prpInv1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlInverseOf then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (s.withPred p1).flatMap (fun u =>
            (asSubject u.o).map (fun ys => ⟨ys, p2, u.s.toTerm⟩))))
  else []

def invFpIfpForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlInverseOf then
    (subjIri d.s).flatMap (fun p1 =>
      (asIri d.o).flatMap (fun p2 =>
        if s.memB ⟨Subject.iri p1, rdfType, Term.iri owlFunctionalProperty⟩
        then [(⟨Subject.iri p2, rdfType,
                Term.iri owlInverseFunctionalProperty⟩ : Triple)]
        else []))
  else []

def invIfpFpForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlInverseOf then
    (subjIri d.s).flatMap (fun p1 =>
      (asIri d.o).flatMap (fun p2 =>
        if s.memB ⟨Subject.iri p1, rdfType,
                   Term.iri owlInverseFunctionalProperty⟩
        then [(⟨Subject.iri p2, rdfType,
                Term.iri owlFunctionalProperty⟩ : Triple)]
        else []))
  else []

def invFpIfpRevForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlInverseOf then
    (subjIri d.s).flatMap (fun p1 =>
      (asIri d.o).flatMap (fun p2 =>
        if s.memB ⟨Subject.iri p2, rdfType, Term.iri owlFunctionalProperty⟩
        then [(⟨Subject.iri p1, rdfType,
                Term.iri owlInverseFunctionalProperty⟩ : Triple)]
        else []))
  else []

def invIfpFpRevForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlInverseOf then
    (subjIri d.s).flatMap (fun p1 =>
      (asIri d.o).flatMap (fun p2 =>
        if s.memB ⟨Subject.iri p2, rdfType,
                   Term.iri owlInverseFunctionalProperty⟩
        then [(⟨Subject.iri p1, rdfType,
                Term.iri owlFunctionalProperty⟩ : Triple)]
        else []))
  else []

def prpInv2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlInverseOf then
    (subjIri d.s).flatMap (fun p1 =>
        (asIri d.o).flatMap (fun p2 =>
          (s.withPred p2).flatMap (fun u =>
            (asSubject u.o).map (fun ys => ⟨ys, p1, u.s.toTerm⟩))))
  else []

def prpKeyForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlHasKey then
    (listSeqsS s d.o (listFuel s.graph)).flatMap (fun terms =>
      (nonEmpty (allIris terms)).flatMap (fun preds =>
        (s.withPredObj rdfType d.s.toTerm).flatMap (fun tx =>
          (s.withPredObj rdfType d.s.toTerm).flatMap (fun ty =>
            if sharesKeyValuesBS s tx.s ty.s preds
            then [⟨tx.s, owlSameAs, ty.s.toTerm⟩] else []))))
  else []

def clsInt1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlIntersectionOf then
    (nonEmpty (listSeqsS s d.o (listFuel s.graph))).flatMap (fun cs =>
      (subjectsOf s.graph).flatMap (fun y =>
        if typesAllBS s y cs then [⟨y, rdfType, d.s.toTerm⟩] else []))
  else []

def clsInt2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlIntersectionOf then
    (listElemsS s d.o (listFuel s.graph)).flatMap (fun ci =>
      (s.withPredObj rdfType d.s.toTerm).map (fun u => ⟨u.s, rdfType, ci⟩))
  else []

def clsUniForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlUnionOf then
    (listElemsS s d.o (listFuel s.graph)).flatMap (fun ci =>
      (s.withPredObj rdfType ci).map (fun u =>
        ⟨u.s, rdfType, d.s.toTerm⟩))
  else []

def clsSvf1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlSomeValuesFrom then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPred p).flatMap (fun u =>
          (asSubject u.o).flatMap (fun vs =>
            if s.memB ⟨vs, rdfType, d.o⟩
            then [⟨u.s, rdfType, d.s.toTerm⟩] else []))))
  else []

def clsSvf2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlSomeValuesFrom && d.o == Term.iri owlThing then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPred p).map (fun u => ⟨u.s, rdfType, d.s.toTerm⟩)))
  else []

def clsAvfForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlAllValuesFrom then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPredObj rdfType d.s.toTerm).flatMap (fun tu =>
          (s.withSubjPred tu.s p).flatMap (fun u =>
            (asSubject u.o).map (fun vs => ⟨vs, rdfType, d.o⟩)))))
  else []

def clsHv1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlHasValue then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPredObj rdfType d.s.toTerm).map (fun tu => ⟨tu.s, p, d.o⟩)))
  else []

def clsHv2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlHasValue then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPredObj p d.o).map (fun u => ⟨u.s, rdfType, d.s.toTerm⟩)))
  else []

def clsHs1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlHasSelf && d.o == Term.literal litTrueBoolean then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPredObj rdfType d.s.toTerm).map (fun tu =>
          ⟨tu.s, p, tu.s.toTerm⟩)))
  else []

def clsHs2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlHasSelf && d.o == Term.literal litTrueBoolean then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPred p).flatMap (fun u =>
          if u.o == u.s.toTerm then [⟨u.s, rdfType, d.s.toTerm⟩] else [])))
  else []

def clsMaxc2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlMaxCardinality && d.o == Term.literal litNni1 then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withPredObj rdfType d.s.toTerm).flatMap (fun tu =>
          (s.withSubjPred tu.s p).flatMap (fun u1 =>
            (asSubject u1.o).flatMap (fun y1s =>
              (s.withSubjPred tu.s p).map (fun u2 =>
                ⟨y1s, owlSameAs, u2.o⟩))))))
  else []

def clsOoForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlOneOf then
    (listElemsS s d.o (listFuel s.graph)).flatMap (fun yi =>
      (asSubject yi).map (fun yis => ⟨yis, rdfType, d.s.toTerm⟩))
  else []

def caxScoForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsSubClassOf then
    (s.withPredObj rdfType d.s.toTerm).map (fun u => ⟨u.s, rdfType, d.o⟩)
  else []

def caxEqc1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlEquivalentClass then
    (s.withPredObj rdfType d.s.toTerm).map (fun u => ⟨u.s, rdfType, d.o⟩)
  else []

def caxEqc2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlEquivalentClass then
    (s.withPredObj rdfType d.o).map (fun u => ⟨u.s, rdfType, d.s.toTerm⟩)
  else []

def scmClsForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlClass then
    [⟨d.s, rdfsSubClassOf, d.s.toTerm⟩,
     ⟨d.s, owlEquivalentClass, d.s.toTerm⟩,
     ⟨d.s, rdfsSubClassOf, Term.iri owlThing⟩,
     ⟨Subject.iri owlNothing, rdfsSubClassOf, d.s.toTerm⟩]
  else []

def scmScoForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsSubClassOf then
    (asSubject d.o).flatMap (fun c2s =>
      (s.withSubjPred c2s rdfsSubClassOf).map (fun u =>
        ⟨d.s, rdfsSubClassOf, u.o⟩))
  else []

def scmEqc1ForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == owlEquivalentClass then
    ⟨d.s, rdfsSubClassOf, d.o⟩ ::
      (asSubject d.o).map (fun c2s => ⟨c2s, rdfsSubClassOf, d.s.toTerm⟩)
  else []

def scmEqc2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsSubClassOf then
    (asSubject d.o).flatMap (fun c2s =>
      if s.memB ⟨c2s, rdfsSubClassOf, d.s.toTerm⟩
      then [⟨d.s, owlEquivalentClass, d.o⟩] else [])
  else []

def scmSpoForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsSubPropertyOf then
    (asSubject d.o).flatMap (fun p2s =>
      (s.withSubjPred p2s rdfsSubPropertyOf).map (fun u =>
        ⟨d.s, rdfsSubPropertyOf, u.o⟩))
  else []

def scmEqp1ForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == owlEquivalentProperty then
    ⟨d.s, rdfsSubPropertyOf, d.o⟩ ::
      (asSubject d.o).map (fun p2s => ⟨p2s, rdfsSubPropertyOf, d.s.toTerm⟩)
  else []

def scmEqp2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsSubPropertyOf then
    (asSubject d.o).flatMap (fun p2s =>
      if s.memB ⟨p2s, rdfsSubPropertyOf, d.s.toTerm⟩
      then [⟨d.s, owlEquivalentProperty, d.o⟩] else [])
  else []

def scmDom1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsDomain then
    (asSubject d.o).flatMap (fun c1s =>
      (s.withSubjPred c1s rdfsSubClassOf).map (fun u =>
        ⟨d.s, rdfsDomain, u.o⟩))
  else []

def scmDom2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsDomain then
    (s.withPredObj rdfsSubPropertyOf d.s.toTerm).map (fun u =>
      ⟨u.s, rdfsDomain, d.o⟩)
  else []

def scmRng1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsRange then
    (asSubject d.o).flatMap (fun c1s =>
      (s.withSubjPred c1s rdfsSubClassOf).map (fun u =>
        ⟨d.s, rdfsRange, u.o⟩))
  else []

def scmRng2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsRange then
    (s.withPredObj rdfsSubPropertyOf d.s.toTerm).map (fun u =>
      ⟨u.s, rdfsRange, d.o⟩)
  else []

def scmOpForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlObjectProperty then
    [⟨d.s, rdfsSubPropertyOf, d.s.toTerm⟩,
     ⟨d.s, owlEquivalentProperty, d.s.toTerm⟩]
  else []

def scmDpForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlDatatypeProperty then
    [⟨d.s, rdfsSubPropertyOf, d.s.toTerm⟩,
     ⟨d.s, owlEquivalentProperty, d.s.toTerm⟩]
  else []

/-- **scm-svf1** — Table 9, driven by `?c1 owl:someValuesFrom ?y1`. -/
def scmSvf1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlSomeValuesFrom then
    (asSubject d.o).flatMap (fun y1 =>
      (s.withSubjPred d.s owlOnProperty).flatMap (fun up =>
        (s.withPredObj owlOnProperty up.o).flatMap (fun uc2 =>
          (s.withSubjPred uc2.s owlSomeValuesFrom).flatMap (fun uy2 =>
            if s.memB ⟨y1, rdfsSubClassOf, uy2.o⟩
            then [⟨d.s, rdfsSubClassOf, uc2.s.toTerm⟩] else []))))
  else []

/-- **scm-svf2** — Table 9, driven by `?c1 owl:someValuesFrom ?y`. -/
def scmSvf2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlSomeValuesFrom then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun up1 =>
      (asSubject up1.o).flatMap (fun p1 =>
        (s.withSubjPred p1 rdfsSubPropertyOf).flatMap (fun usp =>
          (s.withPredObj owlOnProperty usp.o).flatMap (fun uc2 =>
            if s.memB ⟨uc2.s, owlSomeValuesFrom, d.o⟩
            then [⟨d.s, rdfsSubClassOf, uc2.s.toTerm⟩] else []))))
  else []

/-- **scm-avf1** — Table 9, driven by `?c1 owl:allValuesFrom ?y1`. -/
def scmAvf1ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlAllValuesFrom then
    (asSubject d.o).flatMap (fun y1 =>
      (s.withSubjPred d.s owlOnProperty).flatMap (fun up =>
        (s.withPredObj owlOnProperty up.o).flatMap (fun uc2 =>
          (s.withSubjPred uc2.s owlAllValuesFrom).flatMap (fun uy2 =>
            if s.memB ⟨y1, rdfsSubClassOf, uy2.o⟩
            then [⟨d.s, rdfsSubClassOf, uc2.s.toTerm⟩] else []))))
  else []

/-- **scm-avf2** — Table 9, driven by `?c1 owl:allValuesFrom ?y`.
    The conclusion runs the other way: `∀p2.y ⊑ ∀p1.y` when
    `p1 ⊑ p2`. -/
def scmAvf2ForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlAllValuesFrom then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun up1 =>
      (asSubject up1.o).flatMap (fun p1 =>
        (s.withSubjPred p1 rdfsSubPropertyOf).flatMap (fun usp =>
          (s.withPredObj owlOnProperty usp.o).flatMap (fun uc2 =>
            if s.memB ⟨uc2.s, owlAllValuesFrom, d.o⟩
            then [⟨uc2.s, rdfsSubClassOf, d.s.toTerm⟩] else []))))
  else []

/-- **scm-hv** — Table 9, driven by `?c1 owl:hasValue ?i`. -/
def scmHvForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlHasValue then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun up1 =>
      (asSubject up1.o).flatMap (fun p1 =>
        (s.withSubjPred p1 rdfsSubPropertyOf).flatMap (fun usp =>
          (s.withPredObj owlOnProperty usp.o).flatMap (fun uc2 =>
            if s.memB ⟨uc2.s, owlHasValue, d.o⟩
            then [⟨d.s, rdfsSubClassOf, uc2.s.toTerm⟩] else []))))
  else []

def scmIntForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlIntersectionOf then
    (listElemsS s d.o (listFuel s.graph)).map (fun ci =>
      ⟨d.s, rdfsSubClassOf, ci⟩)
  else []

def scmUniForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlUnionOf then
    (listElemsS s d.o (listFuel s.graph)).flatMap (fun ci =>
      (asSubject ci).map (fun cis => ⟨cis, rdfsSubClassOf, d.s.toTerm⟩))
  else []

/-! ### The `[ext]` rows, over a store -/

def eqDiffSymForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == owlDifferentFrom then
    (asSubject d.o).map (fun ys => ⟨ys, owlDifferentFrom, d.s.toTerm⟩)
  else []

def pdwToDiffForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlPropertyDisjointWith then
    (subjIri d.s).flatMap (fun p1 =>
      (asIri d.o).flatMap (fun p2 =>
        (s.withPred p1).flatMap (fun t1 =>
          (asSubject t1.o).flatMap (fun o1s =>
            (s.withSubjPred t1.s p2).flatMap (fun t2 =>
              if o1s.toTerm == t2.o then []
              else [⟨o1s, owlDifferentFrom, t2.o⟩])))))
  else []

def caxDwToDiffForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlDisjointWith then
    (subjIri d.s).flatMap (fun c1 =>
      (asIri d.o).flatMap (fun c2 =>
        (s.withPredObj rdfType (Term.iri c1)).flatMap (fun tx =>
          (s.withPredObj rdfType (Term.iri c2)).flatMap (fun ty =>
            if tx.s == ty.s then [] else [⟨tx.s, owlDifferentFrom, ty.s.toTerm⟩]))))
  else []

def fpDiffToDiffForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlDifferentFrom then
    (s.withObj d.s.toTerm).flatMap (fun t1 =>
      if s.memB ⟨Subject.iri t1.p, rdfType, Term.iri owlFunctionalProperty⟩ then
        (s.withPredObj t1.p d.o).flatMap (fun t2 =>
          if t1.s == t2.s then [] else [⟨t1.s, owlDifferentFrom, t2.s.toTerm⟩])
      else [])
  else []

def ifpDiffToDiffForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlDifferentFrom then
    (s.withSubj d.s).flatMap (fun t1 =>
      if s.memB ⟨Subject.iri t1.p, rdfType,
          Term.iri owlInverseFunctionalProperty⟩ then
        (asSubject t1.o).flatMap (fun y1s =>
          (asSubject d.o).flatMap (fun x2s =>
            (s.withSubjPred x2s t1.p).flatMap (fun t2 =>
              if y1s.toTerm == t2.o then []
              else [⟨y1s, owlDifferentFrom, t2.o⟩])))
      else [])
  else []

def chainToTransForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlPropertyChainAxiom then
    (subjIri d.s).flatMap (fun p =>
      (listSeqsS s d.o (listFuel s.graph)).flatMap (fun terms =>
        if terms == [Term.iri p, Term.iri p]
        then [⟨Subject.iri p, rdfType, Term.iri owlTransitiveProperty⟩]
        else []))
  else []

def prpRflForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlReflexiveProperty then
    (subjIri d.s).flatMap (fun p =>
      (iriIndividuals s.graph).map (fun i => ⟨Subject.iri i, p, Term.iri i⟩))
  else []

def xsdAxiomsForS (_s : Store) (d : Triple) : List Triple :=
  if drivesXsdAxioms d then xsdAxiomTriples else []

def dtRangeIntersectForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfsRange then
    (asIri d.o).flatMap (fun d1 =>
      (s.withSubjPred d.s rdfsRange).flatMap (fun t2 =>
        (asIri t2.o).flatMap (fun d2 =>
          xsdRangeIntersections.flatMap (fun e =>
            if (e.1 == d1 && e.2.1 == d2) || (e.1 == d2 && e.2.1 == d1)
            then e.2.2.map (fun d3 => ⟨d.s, rdfsRange, Term.iri d3⟩)
            else []))))
  else []

def caxDwToComplementForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == owlDisjointWith then
    (subjIri d.s).flatMap (fun c1 =>
      (asIri d.o).flatMap (fun c2 => complementWitnessTriples c1 c2))
  else []

def clsMaxqc1ToComplementForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlMaxQualifiedCardinality && d.o == Term.literal litNni1 then
    (s.withSubjPred d.s owlOnProperty).flatMap (fun onp =>
      (asIri onp.o).flatMap (fun p =>
        (s.withSubjPred d.s owlOnClass).flatMap (fun onc =>
          (asIri onc.o).flatMap (fun c =>
            (s.withPredObj rdfType d.s.toTerm).flatMap (fun tu =>
              (s.withSubjPred tu.s p).flatMap (fun u1 =>
                (asSubject u1.o).flatMap (fun y1s =>
                  if s.memB ⟨y1s, rdfType, Term.iri c⟩ then
                    (s.withSubjPred y1s owlDifferentFrom).flatMap (fun df =>
                      (asSubject df.o).flatMap (fun y2s =>
                        if s.memB ⟨tu.s, p, y2s.toTerm⟩
                        then complementTypeTriples y2s c else []))
                  else [])))))))
  else []

def minCard1ComprehensionForS (_s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlObjectProperty then
    (subjIri d.s).flatMap minCard1WitnessTriples
  else []

def caxAdcToDwForS (s : Store) (d : Triple) : List Triple :=
  if d.p == rdfType && d.o == Term.iri owlAllDisjointClasses then
    (s.withSubjPred d.s owlMembers).flatMap (fun mem =>
      (listElemsS s mem.o (listFuel s.graph)).flatMap (fun ci =>
        (asIri ci).flatMap (fun ci' =>
          (listElemsS s mem.o (listFuel s.graph)).flatMap (fun cj =>
            (asIri cj).flatMap (fun cj' =>
              if ci' == cj' then []
              else [⟨Subject.iri ci', owlDisjointWith, Term.iri cj'⟩])))))
  else []

/-! ## Section 5 — one round and the loop, over the index -/

/-- **inv-flip** `[ext]` — the store version scans `s.graph`, exactly
as the list version scans `g`. -/
def inverseOfDomRngFlipForS (s : Store) (d : Triple) : List Triple :=
  if d.p == owlInverseOf then
    (subjIri d.s).flatMap (fun p1 =>
      (asIri d.o).flatMap (fun p2 =>
        s.graph.flatMap (fun t =>
          match t.s, t.o with
          | .iri srcP, .iri c =>
              if      srcP == p1 && t.p == rdfsDomain then [(⟨.iri p2, rdfsRange, .iri c⟩ : Triple)]
              else if srcP == p1 && t.p == rdfsRange  then [(⟨.iri p2, rdfsDomain, .iri c⟩ : Triple)]
              else if srcP == p2 && t.p == rdfsDomain then [(⟨.iri p1, rdfsRange, .iri c⟩ : Triple)]
              else if srcP == p2 && t.p == rdfsRange  then [(⟨.iri p1, rdfsDomain, .iri c⟩ : Triple)]
              else []
          | _, _ => [])))
  else []

def conclusionsListS (s : Store) (d : Triple) : List (List Triple) :=
    [ eqRefSForS s d, eqRefPForS s d, eqRefOForS s d,
      eqSymForS s d, eqTransForS s d,
      eqRepSForS s d, eqRepPForS s d, eqRepOForS s d,
      prpDomForS s d, prpRngForS s d, prpFpForS s d, prpIfpForS s d,
      prpSympForS s d, prpTrpForS s d, prpSpo1ForS s d, prpSpo2ForS s d,
      prpEqp1ForS s d, prpEqp2ForS s d, prpInv1ForS s d, prpInv2ForS s d,
      invFpIfpForS s d, invIfpFpForS s d, invFpIfpRevForS s d,
      invIfpFpRevForS s d,
      prpKeyForS s d,
      clsInt1ForS s d, clsInt2ForS s d, clsUniForS s d,
      clsSvf1ForS s d, clsSvf2ForS s d, clsAvfForS s d,
      clsHv1ForS s d, clsHv2ForS s d, clsHs1ForS s d, clsHs2ForS s d,
      clsMaxc2ForS s d, clsOoForS s d,
      caxScoForS s d, caxEqc1ForS s d, caxEqc2ForS s d,
      scmClsForS s d, scmScoForS s d, scmEqc1ForS s d, scmEqc2ForS s d,
      scmSpoForS s d, scmEqp1ForS s d, scmEqp2ForS s d,
      scmDom1ForS s d, scmDom2ForS s d, scmRng1ForS s d, scmRng2ForS s d,
      scmOpForS s d, scmDpForS s d,
      scmSvf1ForS s d, scmSvf2ForS s d, scmAvf1ForS s d, scmAvf2ForS s d,
      scmHvForS s d,
      scmIntForS s d, scmUniForS s d,
      eqDiffSymForS s d, pdwToDiffForS s d, caxDwToDiffForS s d,
      fpDiffToDiffForS s d, ifpDiffToDiffForS s d,
      chainToTransForS s d, prpRflForS s d,
      xsdAxiomsForS s d, dtRangeIntersectForS s d,
      caxDwToComplementForS s d, clsMaxqc1ToComplementForS s d,
      minCard1ComprehensionForS s d, caxAdcToDwForS s d,
      inverseOfDomRngFlipForS s d ]

def conclusionsFromS (s : Store) (d : Triple) : List Triple :=
  (conclusionsListS s d).flatten

def stepConclusionsS (s : Store) : List Triple :=
  axiomTriples ++ s.graph.flatMap (conclusionsFromS s)

/-- One closure round over the index — the counterpart of
`RLClosure.step`. -/
def stepI (i : Index) : Index :=
  i.insertAll (stepConclusionsS (Store.ofIndex i))

/-- The fuel loop — the counterpart of `RLClosure.closure`, same
stopping rule (the size did not change). -/
def closureI (i : Index) (fuel : Nat) : Index :=
  match fuel with
  | 0     => i
  | n + 1 =>
      let i' := stepI i
      if i'.all.size = i.all.size then i else closureI i' n

/-- The indexed closure of a graph, as a graph. -/
def indexedClosure (g : Graph) (fuel : Nat) : Graph :=
  (closureI (Index.ofGraph g) fuel).toGraph

/-! ## Section 6 — the clash rows, over a store -/

def eqDiff1AtS (s : Store) (d : Triple) : Bool :=
  d.p == owlSameAs && s.memB ⟨d.s, owlDifferentFrom, d.o⟩

def prpIrpAtS (s : Store) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlIrreflexiveProperty then
    (subjIri d.s).any (fun p => (s.withPred p).any (fun u => u.o == u.s.toTerm))
  else false

def prpAsypAtS (s : Store) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAsymmetricProperty then
    (subjIri d.s).any (fun p =>
        (s.withPred p).any (fun u1 =>
          (asSubject u1.o).any (fun y => s.memB ⟨y, p, u1.s.toTerm⟩)))
  else false

def prpPdwAtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlPropertyDisjointWith then
    (subjIri d.s).any (fun p1 =>
        (asIri d.o).any (fun p2 =>
          (s.withPred p1).any (fun u => s.memB ⟨u.s, p2, u.o⟩)))
  else false

def prpNpa1AtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlSourceIndividual then
    (asSubject d.o).any (fun x =>
      (s.withSubjPred d.s owlAssertionProperty).any (fun ap =>
        (asIri ap.o).any (fun p =>
          (s.withSubjPred d.s owlTargetIndividual).any (fun ti =>
            s.memB ⟨x, p, ti.o⟩))))
  else false

def prpNpa2AtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlSourceIndividual then
    (asSubject d.o).any (fun x =>
      (s.withSubjPred d.s owlAssertionProperty).any (fun ap =>
        (asIri ap.o).any (fun p =>
          (s.withSubjPred d.s owlTargetValue).any (fun tv =>
            s.memB ⟨x, p, tv.o⟩))))
  else false

def clsNothing2AtS (_s : Store) (d : Triple) : Bool :=
  d.p == rdfType && d.o == Term.iri owlNothing

def clsComAtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlComplementOf then
    (s.withPredObj rdfType d.s.toTerm).any (fun u =>
      s.memB ⟨u.s, rdfType, d.o⟩)
  else false

def clsMaxc1AtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlMaxCardinality && d.o == Term.literal litNni0 then
    (s.withSubjPred d.s owlOnProperty).any (fun onp =>
      (asIri onp.o).any (fun p =>
        (s.withPredObj rdfType d.s.toTerm).any (fun tu =>
          !(s.withSubjPred tu.s p).isEmpty)))
  else false

def clsMaxqc1AtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlMaxQualifiedCardinality && d.o == Term.literal litNni0 then
    (s.withSubjPred d.s owlOnProperty).any (fun onp =>
      (asIri onp.o).any (fun p =>
        (s.withSubjPred d.s owlOnClass).any (fun onc =>
          (s.withPredObj rdfType d.s.toTerm).any (fun tu =>
            (s.withSubjPred tu.s p).any (fun u =>
              (asSubject u.o).any (fun ys =>
                s.memB ⟨ys, rdfType, onc.o⟩))))))
  else false

def clsMaxqc2AtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlMaxQualifiedCardinality && d.o == Term.literal litNni0 then
    (s.withSubjPred d.s owlOnProperty).any (fun onp =>
      (asIri onp.o).any (fun p =>
        (s.withSubjPred d.s owlOnClass).any (fun onc =>
          onc.o == Term.iri owlThing &&
          (s.withPredObj rdfType d.s.toTerm).any (fun tu =>
            !(s.withSubjPred tu.s p).isEmpty))))
  else false

def caxDwAtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlDisjointWith then
    (s.withPredObj rdfType d.s.toTerm).any (fun u =>
      s.memB ⟨u.s, rdfType, d.o⟩)
  else false

def caxAdcAtS (s : Store) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAllDisjointClasses then
    (s.withSubjPred d.s owlMembers).any (fun mem =>
      (listCellsS s mem.o (listFuel s.graph)).any (fun ci =>
        (listCellsS s mem.o (listFuel s.graph)).any (fun cj =>
          !(ci == cj) &&
          (s.withSubjPred ci rdfFirst).any (fun fi =>
            (s.withSubjPred cj rdfFirst).any (fun fj =>
              !(fi.o == fj.o) &&
              (s.withPredObj rdfType fi.o).any (fun u =>
                s.memB ⟨u.s, rdfType, fj.o⟩))))))
  else false

def eqDiff2AtS (s : Store) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAllDifferent then
    (s.withSubjPred d.s owlMembers).any (fun mem =>
      (listCellsS s mem.o (listFuel s.graph)).any (fun ci =>
        (listCellsS s mem.o (listFuel s.graph)).any (fun cj =>
          !(ci == cj) &&
          (s.withSubjPred ci rdfFirst).any (fun fi =>
            (s.withSubjPred cj rdfFirst).any (fun fj =>
              !(fi.o == fj.o) &&
              (asSubject fi.o).any (fun zs =>
                s.memB ⟨zs, owlSameAs, fj.o⟩))))))
  else false

def eqDiff3AtS (s : Store) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAllDifferent then
    (s.withSubjPred d.s owlDistinctMembers).any (fun mem =>
      (listCellsS s mem.o (listFuel s.graph)).any (fun ci =>
        (listCellsS s mem.o (listFuel s.graph)).any (fun cj =>
          !(ci == cj) &&
          (s.withSubjPred ci rdfFirst).any (fun fi =>
            (s.withSubjPred cj rdfFirst).any (fun fj =>
              !(fi.o == fj.o) &&
              (asSubject fi.o).any (fun zs =>
                s.memB ⟨zs, owlSameAs, fj.o⟩))))))
  else false

def prpAdpAtS (s : Store) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlAllDisjointProperties then
    (s.withSubjPred d.s owlMembers).any (fun mem =>
      (listCellsS s mem.o (listFuel s.graph)).any (fun ci =>
        (listCellsS s mem.o (listFuel s.graph)).any (fun cj =>
          !(ci == cj) &&
          (s.withSubjPred ci rdfFirst).any (fun fi =>
            (s.withSubjPred cj rdfFirst).any (fun fj =>
              !(fi.o == fj.o) &&
              (asIri fi.o).any (fun p1 =>
                (asIri fj.o).any (fun p2 =>
                  (s.withPred p1).any (fun u =>
                    s.memB ⟨u.s, p2, u.o⟩))))))))
  else false

/-- **prp-fp** over fillers of provably different data values. -/
def prpFpLitAtS (s : Store) (d : Triple) : Bool :=
  if d.p == rdfType && d.o == Term.iri owlFunctionalProperty then
    (subjIri d.s).any (fun p =>
      (s.withPred p).any (fun u1 =>
        (asLit u1.o).any (fun l1 =>
          (s.withSubjPred u1.s p).any (fun u2 =>
            (asLit u2.o).any (fun l2 =>
              valuesProvablyDistinct (Term.literal l1) (Term.literal l2))))))
  else false

def clashRowsS (s : Store) (d : Triple) : List Bool :=
  [ eqDiff1AtS s d, prpIrpAtS s d, prpAsypAtS s d, prpPdwAtS s d,
    prpNpa1AtS s d, prpNpa2AtS s d, clsNothing2AtS s d, clsComAtS s d,
    clsMaxc1AtS s d, clsMaxqc1AtS s d, clsMaxqc2AtS s d,
    caxDwAtS s d, caxAdcAtS s d,
    eqDiff2AtS s d, eqDiff3AtS s d, prpAdpAtS s d,
    prpFpLitAtS s d ]

def clashFromS (s : Store) (d : Triple) : Bool :=
  (clashRowsS s d).any (fun b => b)

def detectClashS (s : Store) : Bool :=
  s.graph.any (fun d => clashFromS s d)

/-! ### The three sound extension rows over a store -/

def dtRangeClashAtS (s : Store) (d : Triple) : Bool :=
  if d.p == rdfsRange then
    (subjIri d.s).any (fun p =>
      (asIri d.o).any (fun dr =>
        (s.withPred p).any (fun u =>
          (asLit u.o).any (fun l =>
            xsdValueSpacesDisjoint l.val.datatype dr))))
  else false

def bottomPropClashAtS (s : Store) (d : Triple) : Bool :=
  if d.p == owlOnProperty then
    (asIri d.o).any (fun p =>
      isBottomProperty p &&
      (s.graph.any (fun t => t.s == d.s && existentialObligation t.p t.o)) &&
      (s.graph.any (fun m => m.p == rdfType && m.o == d.s.toTerm)))
  else false

def clsSvfBotAtS (s : Store) (d : Triple) : Bool :=
  d.p == owlSomeValuesFrom && d.o == Term.iri owlNothing &&
  s.graph.any (fun m => m.p == rdfType && m.o == d.s.toTerm)

def thingNothingClashAtS (_s : Store) (d : Triple) : Bool :=
  d.p == owlEquivalentClass &&
  ((d.s == Subject.iri owlThing && d.o == Term.iri owlNothing) ||
   (d.s == Subject.iri owlNothing && d.o == Term.iri owlThing))

def extClashRowsS (s : Store) (d : Triple) : List Bool :=
  [ dtRangeClashAtS s d, bottomPropClashAtS s d, clsSvfBotAtS s d,
    thingNothingClashAtS s d ]

def extClashFromS (s : Store) (d : Triple) : Bool :=
  (extClashRowsS s d).any (fun b => b)

def detectClashExtS (s : Store) : Bool :=
  s.graph.any (fun d => extClashFromS s d)

/-- The table rows OR the three sound extension rows, over a store. -/
def detectClashPlusS (s : Store) : Bool :=
  detectClashS s || detectClashExtS s

/-- The clash decision over an index. -/
def detectClashI (i : Index) : Bool := detectClashS (Store.ofIndex i)

/-- The extended clash decision over an index — the one the corpus
probe consults. -/
def detectClashPlusI (i : Index) : Bool := detectClashPlusS (Store.ofIndex i)

/-! ## Section 7 — the list-scan store IS `RLClosure`

Every store-parameterised function, applied to `Store.ofGraph g`, is
the `RLClosure` function. The walkers need one induction each (they
are recursive definitions, so `rfl` does not see through the
recursor); every row is then `rfl`. -/

theorem listElemsS_ofGraph (g : Graph) : listElemsS (Store.ofGraph g) = listElems g := by
  funext head n
  induction n generalizing head with
  | zero => rfl
  | succ n ih =>
    simp only [listElemsS, listElems, ih]
    rfl

theorem listCellsS_ofGraph (g : Graph) : listCellsS (Store.ofGraph g) = listCells g := by
  funext head n
  induction n generalizing head with
  | zero => rfl
  | succ n ih =>
    simp only [listCellsS, listCells, ih]
    rfl

theorem listSeqsS_ofGraph (g : Graph) : listSeqsS (Store.ofGraph g) = listSeqs g := by
  funext head n
  induction n generalizing head with
  | zero => rfl
  | succ n ih =>
    simp only [listSeqsS, listSeqs, ih]
    rfl

theorem typesAllBS_ofGraph (g : Graph) : typesAllBS (Store.ofGraph g) = typesAllB g := rfl

theorem sharesKeyValuesBS_ofGraph (g : Graph) :
    sharesKeyValuesBS (Store.ofGraph g) = sharesKeyValuesB g := rfl

theorem chainTargetsS_ofGraph (g : Graph) :
    chainTargetsS (Store.ofGraph g) = chainTargets g := by
  funext start ps
  induction ps generalizing start with
  | nil => rfl
  | cons p rest ih =>
    cases rest with
    | nil => rfl
    | cons q rest' =>
      simp only [chainTargetsS, chainTargets, ih]
      rfl

theorem eqRefSForS_ofGraph (g : Graph) : eqRefSForS (Store.ofGraph g) = eqRefSFor g := rfl
theorem eqRefPForS_ofGraph (g : Graph) : eqRefPForS (Store.ofGraph g) = eqRefPFor g := rfl
theorem eqRefOForS_ofGraph (g : Graph) : eqRefOForS (Store.ofGraph g) = eqRefOFor g := rfl
theorem eqSymForS_ofGraph (g : Graph) : eqSymForS (Store.ofGraph g) = eqSymFor g := rfl
theorem eqTransForS_ofGraph (g : Graph) : eqTransForS (Store.ofGraph g) = eqTransFor g := rfl
theorem eqRepSForS_ofGraph (g : Graph) : eqRepSForS (Store.ofGraph g) = eqRepSFor g := rfl
theorem eqRepPForS_ofGraph (g : Graph) : eqRepPForS (Store.ofGraph g) = eqRepPFor g := rfl
theorem eqRepOForS_ofGraph (g : Graph) : eqRepOForS (Store.ofGraph g) = eqRepOFor g := rfl
theorem prpDomForS_ofGraph (g : Graph) : prpDomForS (Store.ofGraph g) = prpDomFor g := rfl
theorem prpRngForS_ofGraph (g : Graph) : prpRngForS (Store.ofGraph g) = prpRngFor g := rfl
theorem prpFpForS_ofGraph (g : Graph) : prpFpForS (Store.ofGraph g) = prpFpFor g := rfl
theorem prpIfpForS_ofGraph (g : Graph) : prpIfpForS (Store.ofGraph g) = prpIfpFor g := rfl
theorem prpSympForS_ofGraph (g : Graph) : prpSympForS (Store.ofGraph g) = prpSympFor g := rfl
theorem prpTrpForS_ofGraph (g : Graph) : prpTrpForS (Store.ofGraph g) = prpTrpFor g := rfl
theorem prpSpo1ForS_ofGraph (g : Graph) : prpSpo1ForS (Store.ofGraph g) = prpSpo1For g := rfl
theorem prpSpo2ForS_ofGraph (g : Graph) : prpSpo2ForS (Store.ofGraph g) = prpSpo2For g := by
  funext d
  unfold prpSpo2ForS prpSpo2For
  rw [listSeqsS_ofGraph, chainTargetsS_ofGraph]
  rfl
theorem prpEqp1ForS_ofGraph (g : Graph) : prpEqp1ForS (Store.ofGraph g) = prpEqp1For g := rfl
theorem prpEqp2ForS_ofGraph (g : Graph) : prpEqp2ForS (Store.ofGraph g) = prpEqp2For g := rfl
theorem prpInv1ForS_ofGraph (g : Graph) : prpInv1ForS (Store.ofGraph g) = prpInv1For g := rfl
theorem prpInv2ForS_ofGraph (g : Graph) : prpInv2ForS (Store.ofGraph g) = prpInv2For g := rfl
theorem invFpIfpForS_ofGraph (g : Graph) :
    invFpIfpForS (Store.ofGraph g) = invFpIfpFor g := rfl
theorem invIfpFpForS_ofGraph (g : Graph) :
    invIfpFpForS (Store.ofGraph g) = invIfpFpFor g := rfl
theorem invFpIfpRevForS_ofGraph (g : Graph) :
    invFpIfpRevForS (Store.ofGraph g) = invFpIfpRevFor g := rfl
theorem invIfpFpRevForS_ofGraph (g : Graph) :
    invIfpFpRevForS (Store.ofGraph g) = invIfpFpRevFor g := rfl
theorem prpKeyForS_ofGraph (g : Graph) : prpKeyForS (Store.ofGraph g) = prpKeyFor g := by
  funext d
  unfold prpKeyForS prpKeyFor
  rw [listSeqsS_ofGraph, sharesKeyValuesBS_ofGraph]
  rfl
theorem clsInt1ForS_ofGraph (g : Graph) : clsInt1ForS (Store.ofGraph g) = clsInt1For g := by
  funext d
  unfold clsInt1ForS clsInt1For
  rw [listSeqsS_ofGraph, typesAllBS_ofGraph]
  rfl
theorem clsInt2ForS_ofGraph (g : Graph) : clsInt2ForS (Store.ofGraph g) = clsInt2For g := by
  funext d
  unfold clsInt2ForS clsInt2For
  rw [listElemsS_ofGraph]
  rfl
theorem clsUniForS_ofGraph (g : Graph) : clsUniForS (Store.ofGraph g) = clsUniFor g := by
  funext d
  unfold clsUniForS clsUniFor
  rw [listElemsS_ofGraph]
  rfl
theorem clsSvf1ForS_ofGraph (g : Graph) : clsSvf1ForS (Store.ofGraph g) = clsSvf1For g := rfl
theorem clsSvf2ForS_ofGraph (g : Graph) : clsSvf2ForS (Store.ofGraph g) = clsSvf2For g := rfl
theorem clsAvfForS_ofGraph (g : Graph) : clsAvfForS (Store.ofGraph g) = clsAvfFor g := rfl
theorem clsHv1ForS_ofGraph (g : Graph) : clsHv1ForS (Store.ofGraph g) = clsHv1For g := rfl
theorem clsHv2ForS_ofGraph (g : Graph) : clsHv2ForS (Store.ofGraph g) = clsHv2For g := rfl
theorem clsHs1ForS_ofGraph (g : Graph) : clsHs1ForS (Store.ofGraph g) = clsHs1For g := rfl
theorem clsHs2ForS_ofGraph (g : Graph) : clsHs2ForS (Store.ofGraph g) = clsHs2For g := rfl
theorem clsMaxc2ForS_ofGraph (g : Graph) : clsMaxc2ForS (Store.ofGraph g) = clsMaxc2For g := rfl
theorem clsOoForS_ofGraph (g : Graph) : clsOoForS (Store.ofGraph g) = clsOoFor g := by
  funext d
  unfold clsOoForS clsOoFor
  rw [listElemsS_ofGraph]
  rfl
theorem caxScoForS_ofGraph (g : Graph) : caxScoForS (Store.ofGraph g) = caxScoFor g := rfl
theorem caxEqc1ForS_ofGraph (g : Graph) : caxEqc1ForS (Store.ofGraph g) = caxEqc1For g := rfl
theorem caxEqc2ForS_ofGraph (g : Graph) : caxEqc2ForS (Store.ofGraph g) = caxEqc2For g := rfl
theorem scmClsForS_ofGraph (g : Graph) : scmClsForS (Store.ofGraph g) = scmClsFor g := rfl
theorem scmScoForS_ofGraph (g : Graph) : scmScoForS (Store.ofGraph g) = scmScoFor g := rfl
theorem scmEqc1ForS_ofGraph (g : Graph) : scmEqc1ForS (Store.ofGraph g) = scmEqc1For g := rfl
theorem scmEqc2ForS_ofGraph (g : Graph) : scmEqc2ForS (Store.ofGraph g) = scmEqc2For g := rfl
theorem scmSpoForS_ofGraph (g : Graph) : scmSpoForS (Store.ofGraph g) = scmSpoFor g := rfl
theorem scmEqp1ForS_ofGraph (g : Graph) : scmEqp1ForS (Store.ofGraph g) = scmEqp1For g := rfl
theorem scmEqp2ForS_ofGraph (g : Graph) : scmEqp2ForS (Store.ofGraph g) = scmEqp2For g := rfl
theorem scmDom1ForS_ofGraph (g : Graph) : scmDom1ForS (Store.ofGraph g) = scmDom1For g := rfl
theorem scmDom2ForS_ofGraph (g : Graph) : scmDom2ForS (Store.ofGraph g) = scmDom2For g := rfl
theorem scmRng1ForS_ofGraph (g : Graph) : scmRng1ForS (Store.ofGraph g) = scmRng1For g := rfl
theorem scmRng2ForS_ofGraph (g : Graph) : scmRng2ForS (Store.ofGraph g) = scmRng2For g := rfl
theorem scmOpForS_ofGraph (g : Graph) :
    scmOpForS (Store.ofGraph g) = scmOpFor g := by
  funext d
  unfold scmOpForS scmOpFor
  rfl

theorem scmDpForS_ofGraph (g : Graph) :
    scmDpForS (Store.ofGraph g) = scmDpFor g := by
  funext d
  unfold scmDpForS scmDpFor
  rfl

theorem scmSvf1ForS_ofGraph (g : Graph) :
    scmSvf1ForS (Store.ofGraph g) = scmSvf1For g := rfl
theorem scmSvf2ForS_ofGraph (g : Graph) :
    scmSvf2ForS (Store.ofGraph g) = scmSvf2For g := rfl
theorem scmAvf1ForS_ofGraph (g : Graph) :
    scmAvf1ForS (Store.ofGraph g) = scmAvf1For g := rfl
theorem scmAvf2ForS_ofGraph (g : Graph) :
    scmAvf2ForS (Store.ofGraph g) = scmAvf2For g := rfl
theorem scmHvForS_ofGraph (g : Graph) :
    scmHvForS (Store.ofGraph g) = scmHvFor g := rfl
theorem scmIntForS_ofGraph (g : Graph) : scmIntForS (Store.ofGraph g) = scmIntFor g := by
  funext d
  unfold scmIntForS scmIntFor
  rw [listElemsS_ofGraph]
  rfl
theorem scmUniForS_ofGraph (g : Graph) : scmUniForS (Store.ofGraph g) = scmUniFor g := by
  funext d
  unfold scmUniForS scmUniFor
  rw [listElemsS_ofGraph]
  rfl

-- The `[ext]` rows. Only the two that call a recursive walker
-- (`chainToTrans` through `listSeqsS`) or read `s.graph` through a
-- helper (`prpRfl` through `iriIndividuals`) need more than `rfl`.
theorem eqDiffSymForS_ofGraph (g : Graph) :
    eqDiffSymForS (Store.ofGraph g) = eqDiffSymFor g := rfl
theorem pdwToDiffForS_ofGraph (g : Graph) :
    pdwToDiffForS (Store.ofGraph g) = pdwToDiffFor g := rfl
theorem caxDwToDiffForS_ofGraph (g : Graph) :
    caxDwToDiffForS (Store.ofGraph g) = caxDwToDiffFor g := rfl
theorem fpDiffToDiffForS_ofGraph (g : Graph) :
    fpDiffToDiffForS (Store.ofGraph g) = fpDiffToDiffFor g := rfl
theorem ifpDiffToDiffForS_ofGraph (g : Graph) :
    ifpDiffToDiffForS (Store.ofGraph g) = ifpDiffToDiffFor g := rfl
theorem chainToTransForS_ofGraph (g : Graph) :
    chainToTransForS (Store.ofGraph g) = chainToTransFor g := by
  funext d
  unfold chainToTransForS chainToTransFor
  rw [listSeqsS_ofGraph]
  rfl
theorem prpRflForS_ofGraph (g : Graph) :
    prpRflForS (Store.ofGraph g) = prpRflFor g := rfl
theorem xsdAxiomsForS_ofGraph (g : Graph) :
    xsdAxiomsForS (Store.ofGraph g) = xsdAxiomsFor g := rfl
theorem dtRangeIntersectForS_ofGraph (g : Graph) :
    dtRangeIntersectForS (Store.ofGraph g) = dtRangeIntersectFor g := rfl
theorem caxDwToComplementForS_ofGraph (g : Graph) :
    caxDwToComplementForS (Store.ofGraph g) = caxDwToComplementFor g := rfl
theorem clsMaxqc1ToComplementForS_ofGraph (g : Graph) :
    clsMaxqc1ToComplementForS (Store.ofGraph g) = clsMaxqc1ToComplementFor g := rfl
theorem minCard1ComprehensionForS_ofGraph (g : Graph) :
    minCard1ComprehensionForS (Store.ofGraph g) = minCard1ComprehensionFor g := rfl
theorem inverseOfDomRngFlipForS_ofGraph (g : Graph) :
    inverseOfDomRngFlipForS (Store.ofGraph g) = inverseOfDomRngFlipFor g := rfl
theorem caxAdcToDwForS_ofGraph (g : Graph) :
    caxAdcToDwForS (Store.ofGraph g) = caxAdcToDwFor g := by
  funext d
  unfold caxAdcToDwForS caxAdcToDwFor
  rw [listElemsS_ofGraph]
  rfl

/-- A round's conclusion list over the list-scan store is
`RLClosure.conclusionsFrom`. -/
theorem conclusionsFromS_ofGraph (g : Graph) :
    conclusionsFromS (Store.ofGraph g) = conclusionsFrom g := by
  funext d
  simp only [conclusionsFromS, conclusionsFrom, conclusionsListS, conclusionsList,
    eqRefSForS_ofGraph, eqRefPForS_ofGraph, eqRefOForS_ofGraph,
    eqSymForS_ofGraph, eqTransForS_ofGraph,
    eqRepSForS_ofGraph, eqRepPForS_ofGraph, eqRepOForS_ofGraph,
    prpDomForS_ofGraph, prpRngForS_ofGraph, prpFpForS_ofGraph, prpIfpForS_ofGraph,
    prpSympForS_ofGraph, prpTrpForS_ofGraph, prpSpo1ForS_ofGraph, prpSpo2ForS_ofGraph,
    prpEqp1ForS_ofGraph, prpEqp2ForS_ofGraph, prpInv1ForS_ofGraph, prpInv2ForS_ofGraph,
    invFpIfpForS_ofGraph, invIfpFpForS_ofGraph, invFpIfpRevForS_ofGraph,
    invIfpFpRevForS_ofGraph,
    prpKeyForS_ofGraph,
    clsInt1ForS_ofGraph, clsInt2ForS_ofGraph, clsUniForS_ofGraph,
    clsSvf1ForS_ofGraph, clsSvf2ForS_ofGraph, clsAvfForS_ofGraph,
    clsHv1ForS_ofGraph, clsHv2ForS_ofGraph, clsHs1ForS_ofGraph, clsHs2ForS_ofGraph,
    clsMaxc2ForS_ofGraph, clsOoForS_ofGraph,
    caxScoForS_ofGraph, caxEqc1ForS_ofGraph, caxEqc2ForS_ofGraph,
    scmClsForS_ofGraph, scmScoForS_ofGraph, scmEqc1ForS_ofGraph, scmEqc2ForS_ofGraph,
    scmSpoForS_ofGraph, scmEqp1ForS_ofGraph, scmEqp2ForS_ofGraph,
    scmDom1ForS_ofGraph, scmDom2ForS_ofGraph, scmRng1ForS_ofGraph, scmRng2ForS_ofGraph,
    scmOpForS_ofGraph, scmDpForS_ofGraph,
    scmSvf1ForS_ofGraph, scmSvf2ForS_ofGraph, scmAvf1ForS_ofGraph,
    scmAvf2ForS_ofGraph, scmHvForS_ofGraph,
    scmIntForS_ofGraph, scmUniForS_ofGraph,
    eqDiffSymForS_ofGraph, pdwToDiffForS_ofGraph, caxDwToDiffForS_ofGraph,
    fpDiffToDiffForS_ofGraph, ifpDiffToDiffForS_ofGraph,
    chainToTransForS_ofGraph, prpRflForS_ofGraph,
    xsdAxiomsForS_ofGraph, dtRangeIntersectForS_ofGraph,
    caxDwToComplementForS_ofGraph, clsMaxqc1ToComplementForS_ofGraph,
    minCard1ComprehensionForS_ofGraph, caxAdcToDwForS_ofGraph,
    inverseOfDomRngFlipForS_ofGraph]

theorem stepConclusionsS_ofGraph (g : Graph) :
    stepConclusionsS (Store.ofGraph g) = stepConclusions g := by
  unfold stepConclusionsS stepConclusions
  rw [conclusionsFromS_ofGraph]
  rfl

theorem caxAdcAtS_ofGraph (g : Graph) : caxAdcAtS (Store.ofGraph g) = caxAdcAt g := by
  funext d
  unfold caxAdcAtS caxAdcAt
  rw [listCellsS_ofGraph]
  rfl

theorem eqDiff2AtS_ofGraph (g : Graph) :
    eqDiff2AtS (Store.ofGraph g) = eqDiff2At g := by
  funext d
  unfold eqDiff2AtS eqDiff2At
  rw [listCellsS_ofGraph]
  rfl

theorem eqDiff3AtS_ofGraph (g : Graph) :
    eqDiff3AtS (Store.ofGraph g) = eqDiff3At g := by
  funext d
  unfold eqDiff3AtS eqDiff3At
  rw [listCellsS_ofGraph]
  rfl

theorem prpAdpAtS_ofGraph (g : Graph) :
    prpAdpAtS (Store.ofGraph g) = prpAdpAt g := by
  funext d
  unfold prpAdpAtS prpAdpAt
  rw [listCellsS_ofGraph]
  rfl

theorem clashFromS_ofGraph (g : Graph) : clashFromS (Store.ofGraph g) = clashFrom g := by
  funext d
  simp only [clashFromS, clashFrom, clashRowsS, clashRows, caxAdcAtS_ofGraph,
    eqDiff2AtS_ofGraph, eqDiff3AtS_ofGraph, prpAdpAtS_ofGraph]
  rfl

theorem detectClashS_ofGraph (g : Graph) : detectClashS (Store.ofGraph g) = detectClash g := by
  unfold detectClashS detectClash
  rw [clashFromS_ofGraph]
  rfl

theorem extClashFromS_ofGraph (g : Graph) :
    extClashFromS (Store.ofGraph g) = extClashFrom g := by
  funext d
  simp only [extClashFromS, extClashFrom, extClashRowsS, extClashRows]
  rfl

theorem detectClashExtS_ofGraph (g : Graph) :
    detectClashExtS (Store.ofGraph g) = detectClashExt g := by
  unfold detectClashExtS detectClashExt
  rw [extClashFromS_ofGraph]
  rfl

theorem detectClashPlusS_ofGraph (g : Graph) :
    detectClashPlusS (Store.ofGraph g) = detectClashPlus g := by
  unfold detectClashPlusS detectClashPlus
  rw [detectClashS_ofGraph, detectClashExtS_ofGraph]

/-! ## Section 8 — the index is a faithful picture of a list

`Index.Wf i g`: every component of `i` agrees with the list
functions on `g`, bucket lookups as LISTS (same order). -/

/-- A bucket map keyed by `key` holds, under each key, the reversed
filter of `g` for that key. -/
def BucketWf {κ : Type} [BEq κ] [Hashable κ]
    (m : Std.HashMap κ (List Triple)) (key : Triple → κ) (g : Graph) : Prop :=
  ∀ k, (m.getD k []).reverse = g.filter (fun u => key u == k)

theorem BucketWf.empty {κ : Type} [BEq κ] [Hashable κ] (key : Triple → κ) :
    BucketWf (∅ : Std.HashMap κ (List Triple)) key [] := by
  intro k
  simp [Std.HashMap.getD_empty]

theorem BucketWf.push {κ : Type} [BEq κ] [Hashable κ] [LawfulBEq κ]
    {m : Std.HashMap κ (List Triple)} {key : Triple → κ} {g : Graph}
    (h : BucketWf m key g) (t : Triple) :
    BucketWf (m.insert (key t) (t :: m.getD (key t) [])) key (g ++ [t]) := by
  intro k
  rw [Std.HashMap.getD_insert, List.filter_append]
  have hk := h k
  by_cases hkt : key t = k
  · subst hkt
    simp [hk]
  · have hb : (key t == k) = false := by simpa using hkt
    simp [hb, hk]

structure Index.Wf (i : Index) (g : Graph) : Prop where
  all  : i.all.toList = g
  mem  : ∀ t, i.memB t = RL.memB g t
  byS  : BucketWf i.byS (fun u => u.s) g
  byP  : BucketWf i.byP (fun u => u.p) g
  byO  : BucketWf i.byO (fun u => u.o) g
  bySP : BucketWf i.bySP (fun u => (u.s, u.p)) g
  byPO : BucketWf i.byPO (fun u => (u.p, u.o)) g

namespace Index

theorem Wf.empty : Wf empty [] :=
  { all := rfl,
    mem := fun t => by simp [Index.memB, Index.empty, RL.memB],
    byS := BucketWf.empty _, byP := BucketWf.empty _, byO := BucketWf.empty _,
    bySP := BucketWf.empty _, byPO := BucketWf.empty _ }

theorem memB_append_single (g : Graph) (t u : Triple) :
    RL.memB (g ++ [t]) u = (RL.memB g u || t == u) := by
  simp only [RL.memB, List.any_append, List.any_cons, List.any_nil, Bool.or_false]

theorem Wf.push {i : Index} {g : Graph} (h : Wf i g) (t : Triple) :
    Wf (i.push t) (g ++ [t]) :=
  { all := by simp [Index.push, h.all],
    mem := fun u => by
      simp only [Index.memB, Index.push, Std.HashSet.contains_insert, memB_append_single]
      rw [← h.mem u, Index.memB]
      exact Bool.or_comm _ _,
    byS := h.byS.push t, byP := h.byP.push t, byO := h.byO.push t,
    bySP := h.bySP.push t, byPO := h.byPO.push t }

theorem Wf.pushAll (ts : List Triple) :
    ∀ {i : Index} {g : Graph}, Wf i g → Wf (i.pushAll ts) (g ++ ts) := by
  induction ts with
  | nil => intro i g h; simpa [Index.pushAll] using h
  | cons t ts ih =>
    intro i g h
    simp only [Index.pushAll]
    have := ih (h.push t)
    simpa [List.append_assoc] using this

theorem Wf.ofGraph (g : Graph) : Wf (ofGraph g) g := by
  have := Wf.pushAll g Wf.empty
  simpa [Index.ofGraph] using this

theorem Wf.insert {i : Index} {g : Graph} (h : Wf i g) (t : Triple) :
    Wf (i.insert t) (addOne g t) := by
  unfold Index.insert addOne
  rw [h.mem t]
  split
  · exact h
  · exact h.push t

theorem Wf.insertAll (ts : List Triple) :
    ∀ {i : Index} {g : Graph}, Wf i g → Wf (i.insertAll ts) (addAll g ts) := by
  induction ts with
  | nil => intro i g h; exact h
  | cons t ts ih =>
    intro i g h
    simp only [Index.insertAll, addAll]
    exact ih (h.insert t)

/-- The lookups of a well-formed index ARE the list lookups. -/
theorem Wf.withSubj_eq {i : Index} {g : Graph} (h : Wf i g) (s : Subject) :
    i.withSubj s = RL.withSubj g s := h.byS s

theorem Wf.withPred_eq {i : Index} {g : Graph} (h : Wf i g) (p : WfIri) :
    i.withPred p = RL.withPred g p := h.byP p

theorem Wf.withObj_eq {i : Index} {g : Graph} (h : Wf i g) (o : Term) :
    i.withObj o = RL.withObj g o := h.byO o

theorem Wf.withSubjPred_eq {i : Index} {g : Graph} (h : Wf i g) (s : Subject) (p : WfIri) :
    i.withSubjPred s p = RL.withSubjPred g s p := by
  rw [Index.withSubjPred, h.bySP (s, p), RL.withSubjPred]
  -- `(u.s, u.p) == (s, p)` is the conjunction the list filter tests.
  refine List.filter_congr (fun u _ => ?_)
  rw [Bool.eq_iff_iff]
  simp [beq_iff_eq, Bool.and_eq_true, Prod.mk.injEq, Subtype.ext_iff]

theorem Wf.withPredObj_eq {i : Index} {g : Graph} (h : Wf i g) (p : WfIri) (o : Term) :
    i.withPredObj p o = RL.withPredObj g p o := by
  rw [Index.withPredObj, h.byPO (p, o), RL.withPredObj]
  refine List.filter_congr (fun u _ => ?_)
  rw [Bool.eq_iff_iff]
  simp [beq_iff_eq, Bool.and_eq_true, Prod.mk.injEq, Subtype.ext_iff]

end Index

/-- **The store bridge.** Over a well-formed index, the hash-lookup
store is the list-scan store — as a value, so every row, round and
clash function agrees on the two by rewriting. -/
theorem Store.ofIndex_eq {i : Index} {g : Graph} (h : i.Wf g) :
    Store.ofIndex i = Store.ofGraph g := by
  simp only [Store.ofIndex, Store.ofGraph, Store.mk.injEq, Index.toGraph]
  exact ⟨h.all, funext h.withPred_eq, funext h.withSubj_eq, funext h.withObj_eq,
    funext (fun s => funext (h.withSubjPred_eq s)),
    funext (fun p => funext (h.withPredObj_eq p)),
    funext h.mem⟩

/-! ## Section 9 — the bridge theorems -/

/-- One indexed round pictures one list round. -/
theorem Index.Wf.step {i : Index} {g : Graph} (h : i.Wf g) : (stepI i).Wf (RL.step g) := by
  unfold stepI RL.step
  rw [Store.ofIndex_eq h, stepConclusionsS_ofGraph]
  exact h.insertAll _

/-- The indexed loop pictures the list loop at every fuel: both take
the same branch at every round. -/
theorem Index.Wf.closure (fuel : Nat) :
    ∀ {i : Index} {g : Graph}, i.Wf g → (closureI i fuel).Wf (RL.closure g fuel) := by
  induction fuel with
  | zero => intro i g h; exact h
  | succ n ih =>
    intro i g h
    simp only [closureI, RL.closure]
    have hs : (stepI i).all.size = (RL.step g).length := by
      rw [← Array.length_toList, h.step.all]
    have hi : i.all.size = g.length := by
      rw [← Array.length_toList, h.all]
    rw [hs, hi]
    split
    · exact h
    · exact ih h.step

/-- **The bridge.** The indexed closure is the list closure — as a
LIST, at every fuel. -/
theorem indexedClosure_eq (g : Graph) (fuel : Nat) :
    indexedClosure g fuel = closure g fuel :=
  (Index.Wf.closure fuel (Index.Wf.ofGraph g)).all

/-- Set-membership form of the bridge. -/
theorem mem_indexedClosure_iff (g : Graph) (fuel : Nat) (t : Triple) :
    t ∈ indexedClosure g fuel ↔ t ∈ closure g fuel := by
  rw [indexedClosure_eq]

/-- The clash verdict over the index is the clash verdict over the
list it pictures. -/
theorem detectClashI_eq {i : Index} {g : Graph} (h : i.Wf g) :
    detectClashI i = detectClash g := by
  rw [detectClashI, Store.ofIndex_eq h, detectClashS_ofGraph]

/-- The extended decision over a well-formed index is the list one. -/
theorem detectClashPlusI_eq {i : Index} {g : Graph} (h : i.Wf g) :
    detectClashPlusI i = detectClashPlus g := by
  rw [detectClashPlusI, Store.ofIndex_eq h, detectClashPlusS_ofGraph]

/-- The indexed consistency check is `RLClosure.inconsistent`. -/
theorem detectClashI_closureI (g : Graph) (fuel : Nat) :
    detectClashI (closureI (Index.ofGraph g) fuel) = inconsistent g fuel :=
  detectClashI_eq (Index.Wf.closure fuel (Index.Wf.ofGraph g))

/-! ## Section 11 — semi-naive rounds, list-equal to the naive rounds

The naive round (`stepI`) evaluates every row at every driving triple of
the round's input `S`. When `S` is itself the output of a naive round over
`P` (so `S = P ++ D`, where `D`, the delta, is what that round appended),
a row evaluated at a driving triple `d ∈ P` can only produce a triple
outside `S` through an instance that reads a triple of `D`: an instance
whose premises all lie in `P` was already concluded by the round over `P`,
and that round put every conclusion into `S`.

`stepConclusionsSN` therefore evaluates, at each driving triple `d ∈ P`,
only the DELTA TERM of each row (`RowSpec.delta`), and every row in full
at each `d ∈ D`:

* a row that reads nothing but `d` (`RowSpec.indep`: eq-ref, eq-sym,
  scm-cls, ...) contributes nothing at `d ∈ P`;
* a row whose premises other than `d` come from ONE lookup, or from a
  scan of the graph, or from one membership test (`RowSpec.additive`:
  cax-sco, scm-sco, eq-rep-s/p/o, prp-dom, ...) is evaluated at `d ∈ P`
  over the index of `D` alone — the delta term `{d} ⋈ D`;
* every other row (`RowSpec.full`: two or more lookups, collection
  walks) is evaluated at `d ∈ P` over the whole of `S`, as the naive
  round does.

The emitted list keeps the naive round's order: the driving triples in
graph order and, at each, the rows in `conclusionsListS` order. It differs
from the naive round's list only by triples that are already in `S`.
`addAll S` drops exactly those (`addAll_filter_of_subset`), so the
semi-naive round returns the SAME LIST as the naive round
(`stepConclusionsSN_addAll`), and the semi-naive loop returns the same
list as `closure` at every fuel (`indexedClosureSN_eq`). Soundness, the
fuel dichotomy, completeness at a saturated graph and every other theorem
about `closure` hold for it unchanged.

Each row's delta term carries one proof obligation, `RowSpec.Ok`: on a
graph `P ++ D`, the delta term and the full row agree on every triple the
full row over `P` does not already conclude. -/

/-- A row together with the term the semi-naive round evaluates at a
driving triple of the previous round's input. `delta sS sD lo d` reads the
store of the whole input (`sS`), the store of the delta (`sD`) and the length
`lo` of the previous round's input. -/
structure RowSpec where
  f     : Store → Triple → List Triple
  delta : Store → Store → Nat → Triple → List Triple
  /-- The predicate the row's driving triple must have for `delta` to emit
      anything; `none` when `delta` never emits. -/
  guard : Option WfIri

/-- The obligation of a delta term: on `P ++ D`, once the triples the row
concludes from `P` alone are filtered out, the delta term and the full row
are the same list. -/
def RowSpec.Ok (r : RowSpec) : Prop :=
  ∀ (P D : Graph) (d : Triple) (q : Triple → Bool),
    (∀ t ∈ r.f (Store.ofGraph P) d, q t = false) →
    (r.f (Store.ofGraph (P ++ D)) d).filter q =
      (r.delta (Store.ofGraph (P ++ D)) (Store.ofGraph D) P.length d).filter q

/-- A row that reads only its driving triple: nothing at an old one. -/
def RowSpec.indep (f : Store → Triple → List Triple) : RowSpec :=
  { f := f, delta := fun _ _ _ _ => [], guard := none }

/-- A row additive over `P ++ D`: at an old driving triple, the row over
the delta's store. -/
def RowSpec.additive (g : WfIri) (f : Store → Triple → List Triple) : RowSpec :=
  { f := f, delta := fun _ sD _ d => f sD d, guard := some g }

/-- A row evaluated in full at every driving triple, as the naive round
does. -/
def RowSpec.full (g : WfIri) (f : Store → Triple → List Triple) : RowSpec :=
  { f := f, delta := fun sS _ _ d => f sS d, guard := some g }

theorem RowSpec.indep_ok {f : Store → Triple → List Triple}
    (h : ∀ s s' d, f s d = f s' d) : (RowSpec.indep f).Ok := by
  intro P D d q hq
  simp only [RowSpec.indep, List.filter_nil]
  rw [h (Store.ofGraph (P ++ D)) (Store.ofGraph P) d]
  exact List.filter_eq_nil_iff.mpr (fun t ht => by simp [hq t ht])

theorem RowSpec.additive_ok {g : WfIri} {f : Store → Triple → List Triple}
    (h : ∀ P D d, f (Store.ofGraph (P ++ D)) d =
      f (Store.ofGraph P) d ++ f (Store.ofGraph D) d) :
    (RowSpec.additive g f).Ok := by
  intro P D d q hq
  simp only [RowSpec.additive]
  rw [h P D d, List.filter_append,
    List.filter_eq_nil_iff.mpr (fun t ht => by simp [hq t ht]), List.nil_append]

theorem RowSpec.full_ok (g : WfIri) (f : Store → Triple → List Triple) :
    (RowSpec.full g f).Ok := by
  intro P D d q _
  rfl

/-! ### The lookups of `P ++ D` -/

theorem withPred_append (P D : Graph) (p : WfIri) :
    RL.withPred (P ++ D) p = RL.withPred P p ++ RL.withPred D p := by
  simp [RL.withPred, List.filter_append]

theorem withSubj_append (P D : Graph) (s : Subject) :
    RL.withSubj (P ++ D) s = RL.withSubj P s ++ RL.withSubj D s := by
  simp [RL.withSubj, List.filter_append]

theorem withObj_append (P D : Graph) (o : Term) :
    RL.withObj (P ++ D) o = RL.withObj P o ++ RL.withObj D o := by
  simp [RL.withObj, List.filter_append]

theorem withSubjPred_append (P D : Graph) (s : Subject) (p : WfIri) :
    RL.withSubjPred (P ++ D) s p = RL.withSubjPred P s p ++ RL.withSubjPred D s p := by
  simp [RL.withSubjPred, List.filter_append]

theorem withPredObj_append (P D : Graph) (p : WfIri) (o : Term) :
    RL.withPredObj (P ++ D) p o = RL.withPredObj P p o ++ RL.withPredObj D p o := by
  simp [RL.withPredObj, List.filter_append]

theorem memB_append (P D : Graph) (t : Triple) :
    RL.memB (P ++ D) t = (RL.memB P t || RL.memB D t) := by
  simp [RL.memB, List.any_append]

theorem iriIndividuals_append (P D : Graph) :
    iriIndividuals (P ++ D) = iriIndividuals P ++ iriIndividuals D := by
  simp [iriIndividuals, List.flatMap_append]

/-- A zero-or-one element list distributes a `flatMap` over `++`. -/
theorem flatMap_append_of_length_le_one {α β : Type} {l : List α}
    (hl : l.length ≤ 1) (f g : α → List β) :
    l.flatMap (fun x => f x ++ g x) = l.flatMap f ++ l.flatMap g := by
  match l, hl with
  | [], _ => rfl
  | [_], _ => simp

theorem asSubject_length (t : Term) : (asSubject t).length ≤ 1 := by
  unfold asSubject; split <;> simp

theorem asIri_length (t : Term) : (asIri t).length ≤ 1 := by
  unfold asIri; split <;> simp

theorem subjIri_length (s : Subject) : (subjIri s).length ≤ 1 := by
  unfold subjIri; split <;> simp

theorem asSubject_flatMap_append {β : Type} (t : Term) (f g : Subject → List β) :
    (asSubject t).flatMap (fun x => f x ++ g x) =
      (asSubject t).flatMap f ++ (asSubject t).flatMap g :=
  flatMap_append_of_length_le_one (asSubject_length t) f g

theorem asIri_flatMap_append {β : Type} (t : Term) (f g : WfIri → List β) :
    (asIri t).flatMap (fun x => f x ++ g x) = (asIri t).flatMap f ++ (asIri t).flatMap g :=
  flatMap_append_of_length_le_one (asIri_length t) f g

theorem subjIri_flatMap_append {β : Type} (s : Subject) (f g : WfIri → List β) :
    (subjIri s).flatMap (fun x => f x ++ g x) = (subjIri s).flatMap f ++ (subjIri s).flatMap g :=
  flatMap_append_of_length_le_one (subjIri_length s) f g

theorem ite_append_nil {β : Type} {c : Prop} [Decidable c] (X Y : List β) :
    (if c then X ++ Y else []) = (if c then X else []) ++ (if c then Y else []) := by
  split <;> simp

/-- The additivity proof of a row with one lookup: unfold the row, split
every lookup of `P ++ D`, and distribute. -/
macro "additive_row" : tactic => `(tactic| (
  intro P D d
  simp only [Store.ofGraph, withPred_append, withSubj_append, withObj_append,
    withSubjPred_append, withPredObj_append, iriIndividuals_append,
    List.map_append, List.flatMap_append, asSubject_flatMap_append,
    asIri_flatMap_append, subjIri_flatMap_append, ite_append_nil]))

theorem eqTransForS_add (P D : Graph) (d : Triple) : eqTransForS (Store.ofGraph (P ++ D)) d =
    eqTransForS (Store.ofGraph P) d ++ eqTransForS (Store.ofGraph D) d := by
  revert P D d; unfold eqTransForS; additive_row
theorem eqRepSForS_add (P D : Graph) (d : Triple) : eqRepSForS (Store.ofGraph (P ++ D)) d =
    eqRepSForS (Store.ofGraph P) d ++ eqRepSForS (Store.ofGraph D) d := by
  revert P D d; unfold eqRepSForS; additive_row
theorem eqRepPForS_add (P D : Graph) (d : Triple) : eqRepPForS (Store.ofGraph (P ++ D)) d =
    eqRepPForS (Store.ofGraph P) d ++ eqRepPForS (Store.ofGraph D) d := by
  revert P D d; unfold eqRepPForS; additive_row
theorem eqRepOForS_add (P D : Graph) (d : Triple) : eqRepOForS (Store.ofGraph (P ++ D)) d =
    eqRepOForS (Store.ofGraph P) d ++ eqRepOForS (Store.ofGraph D) d := by
  revert P D d; unfold eqRepOForS; additive_row

theorem prpDomForS_add (P D : Graph) (d : Triple) : prpDomForS (Store.ofGraph (P ++ D)) d =
    prpDomForS (Store.ofGraph P) d ++ prpDomForS (Store.ofGraph D) d := by
  revert P D d; unfold prpDomForS; additive_row
theorem prpRngForS_add (P D : Graph) (d : Triple) : prpRngForS (Store.ofGraph (P ++ D)) d =
    prpRngForS (Store.ofGraph P) d ++ prpRngForS (Store.ofGraph D) d := by
  revert P D d; unfold prpRngForS; additive_row
theorem prpSympForS_add (P D : Graph) (d : Triple) : prpSympForS (Store.ofGraph (P ++ D)) d =
    prpSympForS (Store.ofGraph P) d ++ prpSympForS (Store.ofGraph D) d := by
  revert P D d; unfold prpSympForS; additive_row
theorem prpSpo1ForS_add (P D : Graph) (d : Triple) : prpSpo1ForS (Store.ofGraph (P ++ D)) d =
    prpSpo1ForS (Store.ofGraph P) d ++ prpSpo1ForS (Store.ofGraph D) d := by
  revert P D d; unfold prpSpo1ForS; additive_row
theorem prpEqp1ForS_add (P D : Graph) (d : Triple) : prpEqp1ForS (Store.ofGraph (P ++ D)) d =
    prpEqp1ForS (Store.ofGraph P) d ++ prpEqp1ForS (Store.ofGraph D) d := by
  revert P D d; unfold prpEqp1ForS; additive_row
theorem prpEqp2ForS_add (P D : Graph) (d : Triple) : prpEqp2ForS (Store.ofGraph (P ++ D)) d =
    prpEqp2ForS (Store.ofGraph P) d ++ prpEqp2ForS (Store.ofGraph D) d := by
  revert P D d; unfold prpEqp2ForS; additive_row
theorem prpInv1ForS_add (P D : Graph) (d : Triple) : prpInv1ForS (Store.ofGraph (P ++ D)) d =
    prpInv1ForS (Store.ofGraph P) d ++ prpInv1ForS (Store.ofGraph D) d := by
  revert P D d; unfold prpInv1ForS; additive_row
theorem prpInv2ForS_add (P D : Graph) (d : Triple) : prpInv2ForS (Store.ofGraph (P ++ D)) d =
    prpInv2ForS (Store.ofGraph P) d ++ prpInv2ForS (Store.ofGraph D) d := by
  revert P D d; unfold prpInv2ForS; additive_row
theorem caxScoForS_add (P D : Graph) (d : Triple) : caxScoForS (Store.ofGraph (P ++ D)) d =
    caxScoForS (Store.ofGraph P) d ++ caxScoForS (Store.ofGraph D) d := by
  revert P D d; unfold caxScoForS; additive_row
theorem caxEqc1ForS_add (P D : Graph) (d : Triple) : caxEqc1ForS (Store.ofGraph (P ++ D)) d =
    caxEqc1ForS (Store.ofGraph P) d ++ caxEqc1ForS (Store.ofGraph D) d := by
  revert P D d; unfold caxEqc1ForS; additive_row
theorem caxEqc2ForS_add (P D : Graph) (d : Triple) : caxEqc2ForS (Store.ofGraph (P ++ D)) d =
    caxEqc2ForS (Store.ofGraph P) d ++ caxEqc2ForS (Store.ofGraph D) d := by
  revert P D d; unfold caxEqc2ForS; additive_row
theorem scmScoForS_add (P D : Graph) (d : Triple) : scmScoForS (Store.ofGraph (P ++ D)) d =
    scmScoForS (Store.ofGraph P) d ++ scmScoForS (Store.ofGraph D) d := by
  revert P D d; unfold scmScoForS; additive_row
theorem scmSpoForS_add (P D : Graph) (d : Triple) : scmSpoForS (Store.ofGraph (P ++ D)) d =
    scmSpoForS (Store.ofGraph P) d ++ scmSpoForS (Store.ofGraph D) d := by
  revert P D d; unfold scmSpoForS; additive_row
theorem scmDom1ForS_add (P D : Graph) (d : Triple) : scmDom1ForS (Store.ofGraph (P ++ D)) d =
    scmDom1ForS (Store.ofGraph P) d ++ scmDom1ForS (Store.ofGraph D) d := by
  revert P D d; unfold scmDom1ForS; additive_row
theorem scmDom2ForS_add (P D : Graph) (d : Triple) : scmDom2ForS (Store.ofGraph (P ++ D)) d =
    scmDom2ForS (Store.ofGraph P) d ++ scmDom2ForS (Store.ofGraph D) d := by
  revert P D d; unfold scmDom2ForS; additive_row
theorem scmRng1ForS_add (P D : Graph) (d : Triple) : scmRng1ForS (Store.ofGraph (P ++ D)) d =
    scmRng1ForS (Store.ofGraph P) d ++ scmRng1ForS (Store.ofGraph D) d := by
  revert P D d; unfold scmRng1ForS; additive_row
theorem scmRng2ForS_add (P D : Graph) (d : Triple) : scmRng2ForS (Store.ofGraph (P ++ D)) d =
    scmRng2ForS (Store.ofGraph P) d ++ scmRng2ForS (Store.ofGraph D) d := by
  revert P D d; unfold scmRng2ForS; additive_row
theorem prpRflForS_add (P D : Graph) (d : Triple) : prpRflForS (Store.ofGraph (P ++ D)) d =
    prpRflForS (Store.ofGraph P) d ++ prpRflForS (Store.ofGraph D) d := by
  revert P D d; unfold prpRflForS; additive_row
theorem dtRangeIntersectForS_add (P D : Graph) (d : Triple) : dtRangeIntersectForS (Store.ofGraph (P ++ D)) d =
    dtRangeIntersectForS (Store.ofGraph P) d ++ dtRangeIntersectForS (Store.ofGraph D) d := by
  revert P D d; unfold dtRangeIntersectForS; additive_row
theorem inverseOfDomRngFlipForS_add (P D : Graph) (d : Triple) : inverseOfDomRngFlipForS (Store.ofGraph (P ++ D)) d =
    inverseOfDomRngFlipForS (Store.ofGraph P) d ++ inverseOfDomRngFlipForS (Store.ofGraph D) d := by
  revert P D d; unfold inverseOfDomRngFlipForS; additive_row

/-! ### Delta terms of two collection rows: prp-spo2 and cls-int1

Both rows iterate every subject of the graph for each reading of their
collection (`subjectsOf s.graph`), so the naive round costs the graph size
times the number of `owl:propertyChainAxiom` (resp. `owl:intersectionOf`)
triples. At an old driving triple the semi-naive round evaluates the row in
full only when the delta can change its output: when the delta holds an
`rdf:first` or `rdf:rest` triple, when the collection walk at the larger
fuel `listFuel S` reads more than at the previous round's fuel, or when the
delta holds an edge on a chain property (prp-spo2) or a typing in a member
class (cls-int1) of one of the readings. Otherwise every conclusion the row
draws from `S` it already drew from the previous round's input. -/

@[simp] theorem Store.ofGraph_graph (g : Graph) : (Store.ofGraph g).graph = g := rfl

theorem withSubjPred_nil_of {D : Graph} {s : Subject} {p : WfIri}
    (h : ∀ u ∈ D, u.p ≠ p) : RL.withSubjPred D s p = [] := by
  unfold RL.withSubjPred
  refine List.filter_eq_nil_iff.mpr (fun u hu => ?_)
  have := h u hu
  simp only [Bool.and_eq_true, beq_iff_eq, not_and]
  exact fun _ hv => this hv

theorem withPred_isEmpty {D : Graph} {p : WfIri}
    (h : ((Store.ofGraph D).withPred p).isEmpty = true) : ∀ u ∈ D, u.p ≠ p := by
  intro u hu hup
  have hm : u ∈ (Store.ofGraph D).withPred p := by
    simp only [Store.ofGraph, RL.withPred, List.mem_filter]
    exact ⟨hu, by simp [hup]⟩
  rw [List.isEmpty_iff] at h
  rw [h] at hm
  cases hm

theorem withPredObj_isEmpty {D : Graph} {p : WfIri} {o : Term}
    (h : ((Store.ofGraph D).withPredObj p o).isEmpty = true) :
    ∀ u ∈ D, ¬ (u.p = p ∧ u.o = o) := by
  intro u hu ⟨hup, huo⟩
  have hm : u ∈ (Store.ofGraph D).withPredObj p o := by
    simp only [Store.ofGraph, RL.withPredObj, List.mem_filter]
    exact ⟨hu, by simp [hup, huo]⟩
  rw [List.isEmpty_iff] at h
  rw [h] at hm
  cases hm

/-- With no `rdf:first` or `rdf:rest` triple in the delta, the collection
walk reads the same cells over `P ++ D` as over `P`. -/
theorem listSeqsS_append_of_noList {P D : Graph}
    (hf : ∀ u ∈ D, u.p ≠ rdfFirst) (hr : ∀ u ∈ D, u.p ≠ rdfRest) :
    ∀ (n : Nat) (h : Term),
      listSeqsS (Store.ofGraph (P ++ D)) h n = listSeqsS (Store.ofGraph P) h n := by
  intro n
  induction n with
  | zero => intro h; rfl
  | succ n ih =>
    intro h
    simp only [listSeqsS]
    split
    · rfl
    · simp only [Store.ofGraph, withSubjPred_append, withSubjPred_nil_of hf,
        withSubjPred_nil_of hr, List.append_nil]
      simp only [Store.ofGraph] at ih
      simp only [ih]

/-- With no delta edge on a chain property, the chain walk is the same over
`P ++ D` as over `P`. -/
theorem chainTargetsS_append_of {P D : Graph} :
    ∀ (ps : List WfIri) (x : Subject), (∀ p ∈ ps, ∀ u ∈ D, u.p ≠ p) →
      chainTargetsS (Store.ofGraph (P ++ D)) x ps = chainTargetsS (Store.ofGraph P) x ps := by
  intro ps
  induction ps with
  | nil => intro x _; rfl
  | cons p rest ih =>
    intro x h
    have hp : ∀ u ∈ D, u.p ≠ p := h p List.mem_cons_self
    cases rest with
    | nil =>
      simp only [chainTargetsS, Store.ofGraph, withSubjPred_append, withSubjPred_nil_of hp,
        List.append_nil]
    | cons q rest' =>
      have ih' := fun y => ih y (fun p' hp' => h p' (List.mem_cons_of_mem _ hp'))
      simp only [chainTargetsS, Store.ofGraph, withSubjPred_append, withSubjPred_nil_of hp,
        List.append_nil]
      simp only [Store.ofGraph] at ih'
      simp only [ih']

/-- A chain of at least one link starts at a subject of the graph. -/
theorem subjectsOf_of_chainTargetsS {P : Graph} {x : Subject} {xn : Term} :
    ∀ {p : WfIri} {ps : List WfIri}, xn ∈ chainTargetsS (Store.ofGraph P) x (p :: ps) →
      x ∈ subjectsOf P := by
  intro p ps h
  cases ps with
  | nil =>
    simp only [chainTargetsS, Store.ofGraph, List.mem_map] at h
    obtain ⟨u, hu, _⟩ := h
    simp only [RL.withSubjPred, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hu
    exact List.mem_map.mpr ⟨u, hu.1, hu.2.1⟩
  | cons q rest =>
    simp only [chainTargetsS, Store.ofGraph, List.mem_flatMap] at h
    obtain ⟨u, hu, _⟩ := h
    simp only [RL.withSubjPred, List.mem_filter, Bool.and_eq_true, beq_iff_eq] at hu
    exact List.mem_map.mpr ⟨u, hu.1, hu.2.1⟩

/-- The run-time test that a collection row's output at an old driving
triple cannot change: no list cell in the delta, and the walk reads no more
at the larger fuel. -/
def listStable (sS sD : Store) (lo : Nat) (head : Term) : Bool :=
  (sD.withPred rdfFirst).isEmpty && (sD.withPred rdfRest).isEmpty &&
    listSeqsS sS head (listFuel sS.graph) == listSeqsS sS head (lo + 1)

theorem listStable_spec {P D : Graph} {head : Term}
    (h : listStable (Store.ofGraph (P ++ D)) (Store.ofGraph D) P.length head = true) :
    (∀ u ∈ D, u.p ≠ rdfFirst) ∧ (∀ u ∈ D, u.p ≠ rdfRest) ∧
      listSeqsS (Store.ofGraph (P ++ D)) head (listFuel (P ++ D)) =
        listSeqsS (Store.ofGraph P) head (listFuel P) := by
  simp only [listStable, Bool.and_eq_true, beq_iff_eq, Store.ofGraph_graph] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hf := withPred_isEmpty h1
  have hr := withPred_isEmpty h2
  refine ⟨hf, hr, ?_⟩
  rw [h3, listSeqsS_append_of_noList hf hr]
  rfl

/-- prp-spo2 at an old driving triple. -/
def prpSpo2Delta (sS sD : Store) (lo : Nat) (d : Triple) : List Triple :=
  if d.p == owlPropertyChainAxiom && listStable sS sD lo d.o &&
      (listSeqsS sS d.o (listFuel sS.graph)).all (fun terms =>
        (allIris terms).all (fun preds => preds.all (fun p => (sD.withPred p).isEmpty)))
  then [] else prpSpo2ForS sS d

theorem prpSpo2_ok :
    (RowSpec.mk prpSpo2ForS prpSpo2Delta (some owlPropertyChainAxiom)).Ok := by
  intro P D d q hq
  simp only [prpSpo2Delta]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨⟨hg, hst⟩, hpreds⟩ := hc
    obtain ⟨_, _, hseq⟩ := listStable_spec hst
    simp only [List.filter_nil]
    refine List.filter_eq_nil_iff.mpr (fun t ht => ?_)
    have hP : t ∈ prpSpo2ForS (Store.ofGraph P) d := by
      unfold prpSpo2ForS at ht ⊢
      rw [if_pos hg] at ht ⊢
      · simp only [List.mem_flatMap, List.mem_map, Store.ofGraph_graph] at ht ⊢
        obtain ⟨p, hp, terms, hterms, preds, hpr, x1, _, xn, hxn, rfl⟩ := ht
        have hnoD : ∀ p' ∈ preds, ∀ u ∈ D, u.p ≠ p' := by
          intro p' hp' u hu
          have hm : preds ∈ allIris terms := (List.mem_filter.mp hpr).1
          exact withPred_isEmpty (hpreds terms hterms preds hm p' hp') u hu
        rw [chainTargetsS_append_of preds x1 hnoD] at hxn
        rw [hseq] at hterms
        have hne : preds ≠ [] := by
          intro h0
          simp [nonEmpty, h0] at hpr
        obtain ⟨p1, ps, rfl⟩ := List.exists_cons_of_ne_nil hne
        exact ⟨p, hp, terms, hterms, p1 :: ps, hpr, x1,
          subjectsOf_of_chainTargetsS hxn, xn, hxn, rfl⟩
    simp [hq t hP]
  · rfl

/-- cls-int1's typing test reads the same over `P ++ D` as over `P` when the
delta types nothing in a member class. -/
theorem typesAllBS_append_of {P D : Graph} {y : Subject} :
    ∀ (cs : List Term), (∀ c ∈ cs, ∀ u ∈ D, ¬ (u.p = rdfType ∧ u.o = c)) →
      typesAllBS (Store.ofGraph (P ++ D)) y cs = typesAllBS (Store.ofGraph P) y cs := by
  intro cs h
  simp only [typesAllBS, Store.ofGraph]
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hD : RL.memB D ⟨y, rdfType, c⟩ = false := by
      simp only [RL.memB, List.any_eq_false, beq_iff_eq]
      intro u hu heq
      exact h c List.mem_cons_self u hu ⟨by rw [heq], by rw [heq]⟩
    simp only [List.all_cons]
    rw [memB_append, hD, Bool.or_false, ih (fun c' hc' => h c' (List.mem_cons_of_mem _ hc'))]

theorem subjectsOf_of_typesAllBS {P : Graph} {y : Subject} {c : Term} {cs : List Term}
    (h : typesAllBS (Store.ofGraph P) y (c :: cs) = true) : y ∈ subjectsOf P := by
  simp only [typesAllBS, Store.ofGraph, List.all_cons, Bool.and_eq_true] at h
  have hm := h.1
  simp only [RL.memB, List.any_eq_true, beq_iff_eq] at hm
  obtain ⟨u, hu, rfl⟩ := hm
  exact List.mem_map.mpr ⟨_, hu, rfl⟩

/-- cls-int1 at an old driving triple. -/
def clsInt1Delta (sS sD : Store) (lo : Nat) (d : Triple) : List Triple :=
  if d.p == owlIntersectionOf && listStable sS sD lo d.o &&
      (listSeqsS sS d.o (listFuel sS.graph)).all (fun cs =>
        cs.all (fun c => (sD.withPredObj rdfType c).isEmpty))
  then [] else clsInt1ForS sS d

theorem clsInt1_ok :
    (RowSpec.mk clsInt1ForS clsInt1Delta (some owlIntersectionOf)).Ok := by
  intro P D d q hq
  simp only [clsInt1Delta]
  split
  · rename_i hc
    simp only [Bool.and_eq_true, List.all_eq_true] at hc
    obtain ⟨⟨hg, hst⟩, hcls⟩ := hc
    obtain ⟨_, _, hseq⟩ := listStable_spec hst
    simp only [List.filter_nil]
    refine List.filter_eq_nil_iff.mpr (fun t ht => ?_)
    have hP : t ∈ clsInt1ForS (Store.ofGraph P) d := by
      unfold clsInt1ForS at ht ⊢
      rw [if_pos hg] at ht ⊢
      · simp only [List.mem_flatMap, Store.ofGraph_graph] at ht ⊢
        obtain ⟨cs, hcs, y, _, hy⟩ := ht
        have hcs' : cs ∈ listSeqsS (Store.ofGraph (P ++ D)) d.o (listFuel (P ++ D)) :=
          (List.mem_filter.mp hcs).1
        have hnoD : ∀ c ∈ cs, ∀ u ∈ D, ¬ (u.p = rdfType ∧ u.o = c) :=
          fun c hc u hu => withPredObj_isEmpty (hcls cs hcs' c hc) u hu
        rw [typesAllBS_append_of cs hnoD] at hy
        rw [hseq] at hcs
        have hne : cs ≠ [] := by
          intro h0
          simp [nonEmpty, h0] at hcs
        obtain ⟨c1, cs1, rfl⟩ := List.exists_cons_of_ne_nil hne
        refine ⟨c1 :: cs1, hcs, y, ?_, hy⟩
        split at hy
        · rename_i htrue
          exact subjectsOf_of_typesAllBS htrue
        · simp at hy
    simp [hq t hP]
  · rfl

/-! ### Delta terms that test the delta's predicates

scm-svf1, scm-svf2, scm-avf1, scm-avf2 and scm-hv read only triples whose
predicates are fixed vocabulary (`owl:onProperty`, `owl:someValuesFrom`,
`owl:allValuesFrom`, `owl:hasValue`, `rdfs:subClassOf`,
`rdfs:subPropertyOf`). When the delta holds no triple with one of those
predicates, every lookup the row makes over `P ++ D` returns what it
returns over `P`, so at an old driving triple the row concludes nothing new
(`RowSpec.skip_ok`). Otherwise the row is evaluated in full. -/

/-- A row evaluated at an old driving triple only when the delta holds a
triple whose predicate is in `preds`. -/
def RowSpec.skip (g : WfIri) (preds : List WfIri) (f : Store → Triple → List Triple) :
    RowSpec :=
  { f := f,
    delta := fun sS sD _ d =>
      if preds.all (fun p => (sD.withPred p).isEmpty) then [] else f sS d,
    guard := some g }

theorem RowSpec.skip_ok {g : WfIri} {preds : List WfIri} {f : Store → Triple → List Triple}
    (h : ∀ P D d, (∀ p ∈ preds, ∀ u ∈ D, u.p ≠ p) →
      f (Store.ofGraph (P ++ D)) d = f (Store.ofGraph P) d) :
    (RowSpec.skip g preds f).Ok := by
  intro P D d q hq
  simp only [RowSpec.skip]
  split
  · rename_i hall
    have hD : ∀ p ∈ preds, ∀ u ∈ D, u.p ≠ p := by
      intro p hp
      exact withPred_isEmpty ((List.all_eq_true.mp hall) p hp)
    rw [h P D d hD, List.filter_nil]
    exact List.filter_eq_nil_iff.mpr (fun t ht => by simp [hq t ht])
  · rfl

theorem withPred_nil_of {D : Graph} {p : WfIri} (h : ∀ u ∈ D, u.p ≠ p) :
    RL.withPred D p = [] := by
  unfold RL.withPred
  refine List.filter_eq_nil_iff.mpr (fun u hu => ?_)
  have := h u hu
  simp only [beq_iff_eq]
  exact this

theorem withPredObj_nil_of {D : Graph} {p : WfIri} {o : Term} (h : ∀ u ∈ D, u.p ≠ p) :
    RL.withPredObj D p o = [] := by
  unfold RL.withPredObj
  refine List.filter_eq_nil_iff.mpr (fun u hu => ?_)
  have := h u hu
  simp only [Bool.and_eq_true, beq_iff_eq, not_and]
  exact fun hv => absurd hv this

theorem memB_false_of_pred {D : Graph} {p : WfIri} (h : ∀ u ∈ D, u.p ≠ p)
    {s : Subject} {o : Term} : RL.memB D ⟨s, p, o⟩ = false := by
  simp only [RL.memB, List.any_eq_false, beq_iff_eq]
  intro u hu heq
  exact h u hu (by rw [heq])

/-- The lookups of the five rows, with no delta triple on their predicates. -/
macro "skip_row" : tactic => `(tactic| (
  intro P D d h
  have h1 := h _ (List.mem_cons_self)
  have h2 := h _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have h3 := h _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have a1 := fun s => withSubjPred_nil_of (s := s) h1
  have a2 := fun s => withSubjPred_nil_of (s := s) h2
  have a3 := fun s => withSubjPred_nil_of (s := s) h3
  have b1 := fun o => withPredObj_nil_of (o := o) h1
  have b2 := fun o => withPredObj_nil_of (o := o) h2
  have b3 := fun o => withPredObj_nil_of (o := o) h3
  have c1 := fun s o => memB_false_of_pred (s := s) (o := o) h1
  have c2 := fun s o => memB_false_of_pred (s := s) (o := o) h2
  have c3 := fun s o => memB_false_of_pred (s := s) (o := o) h3
  simp only [Store.ofGraph, withSubjPred_append, withPredObj_append, memB_append,
    a1, a2, a3, b1, b2, b3, c1, c2, c3, List.append_nil, Bool.or_false]
  all_goals rfl))

set_option linter.unusedSimpArgs false in
theorem scmSvf1ForS_skip : ∀ P D d,
    (∀ p ∈ [owlOnProperty, owlSomeValuesFrom, rdfsSubClassOf], ∀ u ∈ D, u.p ≠ p) →
    scmSvf1ForS (Store.ofGraph (P ++ D)) d = scmSvf1ForS (Store.ofGraph P) d := by
  unfold scmSvf1ForS; skip_row

set_option linter.unusedSimpArgs false in
theorem scmSvf2ForS_skip : ∀ P D d,
    (∀ p ∈ [owlOnProperty, rdfsSubPropertyOf, owlSomeValuesFrom], ∀ u ∈ D, u.p ≠ p) →
    scmSvf2ForS (Store.ofGraph (P ++ D)) d = scmSvf2ForS (Store.ofGraph P) d := by
  unfold scmSvf2ForS; skip_row

set_option linter.unusedSimpArgs false in
theorem scmAvf1ForS_skip : ∀ P D d,
    (∀ p ∈ [owlOnProperty, owlAllValuesFrom, rdfsSubClassOf], ∀ u ∈ D, u.p ≠ p) →
    scmAvf1ForS (Store.ofGraph (P ++ D)) d = scmAvf1ForS (Store.ofGraph P) d := by
  unfold scmAvf1ForS; skip_row

set_option linter.unusedSimpArgs false in
theorem scmAvf2ForS_skip : ∀ P D d,
    (∀ p ∈ [owlOnProperty, rdfsSubPropertyOf, owlAllValuesFrom], ∀ u ∈ D, u.p ≠ p) →
    scmAvf2ForS (Store.ofGraph (P ++ D)) d = scmAvf2ForS (Store.ofGraph P) d := by
  unfold scmAvf2ForS; skip_row

set_option linter.unusedSimpArgs false in
theorem scmHvForS_skip : ∀ P D d,
    (∀ p ∈ [owlOnProperty, rdfsSubPropertyOf, owlHasValue], ∀ u ∈ D, u.p ≠ p) →
    scmHvForS (Store.ofGraph (P ++ D)) d = scmHvForS (Store.ofGraph P) d := by
  unfold scmHvForS; skip_row

/-- The 74 rows of `conclusionsListS`, in its order, each with the term the
semi-naive round evaluates at a driving triple of the previous round's
input. -/
def rowTable : List RowSpec := [
    RowSpec.indep eqRefSForS,
    RowSpec.indep eqRefPForS,
    RowSpec.indep eqRefOForS,
    RowSpec.indep eqSymForS,
    RowSpec.additive owlSameAs eqTransForS,
    RowSpec.additive owlSameAs eqRepSForS,
    RowSpec.additive owlSameAs eqRepPForS,
    RowSpec.additive owlSameAs eqRepOForS,
    RowSpec.additive rdfsDomain prpDomForS,
    RowSpec.additive rdfsRange prpRngForS,
    RowSpec.full rdfType prpFpForS,
    RowSpec.full rdfType prpIfpForS,
    RowSpec.additive rdfType prpSympForS,
    RowSpec.full rdfType prpTrpForS,
    RowSpec.additive rdfsSubPropertyOf prpSpo1ForS,
    RowSpec.mk prpSpo2ForS prpSpo2Delta (some owlPropertyChainAxiom),
    RowSpec.additive owlEquivalentProperty prpEqp1ForS,
    RowSpec.additive owlEquivalentProperty prpEqp2ForS,
    RowSpec.additive owlInverseOf prpInv1ForS,
    RowSpec.additive owlInverseOf prpInv2ForS,
    RowSpec.full owlInverseOf invFpIfpForS,
    RowSpec.full owlInverseOf invIfpFpForS,
    RowSpec.full owlInverseOf invFpIfpRevForS,
    RowSpec.full owlInverseOf invIfpFpRevForS,
    RowSpec.full owlHasKey prpKeyForS,
    RowSpec.mk clsInt1ForS clsInt1Delta (some owlIntersectionOf),
    RowSpec.full owlIntersectionOf clsInt2ForS,
    RowSpec.full owlUnionOf clsUniForS,
    RowSpec.full owlSomeValuesFrom clsSvf1ForS,
    RowSpec.full owlSomeValuesFrom clsSvf2ForS,
    RowSpec.full owlAllValuesFrom clsAvfForS,
    RowSpec.full owlHasValue clsHv1ForS,
    RowSpec.full owlHasValue clsHv2ForS,
    RowSpec.full owlHasSelf clsHs1ForS,
    RowSpec.full owlHasSelf clsHs2ForS,
    RowSpec.full owlMaxCardinality clsMaxc2ForS,
    RowSpec.full owlOneOf clsOoForS,
    RowSpec.additive rdfsSubClassOf caxScoForS,
    RowSpec.additive owlEquivalentClass caxEqc1ForS,
    RowSpec.additive owlEquivalentClass caxEqc2ForS,
    RowSpec.indep scmClsForS,
    RowSpec.additive rdfsSubClassOf scmScoForS,
    RowSpec.indep scmEqc1ForS,
    RowSpec.full rdfsSubClassOf scmEqc2ForS,
    RowSpec.additive rdfsSubPropertyOf scmSpoForS,
    RowSpec.indep scmEqp1ForS,
    RowSpec.full rdfsSubPropertyOf scmEqp2ForS,
    RowSpec.additive rdfsDomain scmDom1ForS,
    RowSpec.additive rdfsDomain scmDom2ForS,
    RowSpec.additive rdfsRange scmRng1ForS,
    RowSpec.additive rdfsRange scmRng2ForS,
    RowSpec.indep scmOpForS,
    RowSpec.indep scmDpForS,
    RowSpec.skip owlSomeValuesFrom [owlOnProperty, owlSomeValuesFrom, rdfsSubClassOf] scmSvf1ForS,
    RowSpec.skip owlSomeValuesFrom [owlOnProperty, rdfsSubPropertyOf, owlSomeValuesFrom] scmSvf2ForS,
    RowSpec.skip owlAllValuesFrom [owlOnProperty, owlAllValuesFrom, rdfsSubClassOf] scmAvf1ForS,
    RowSpec.skip owlAllValuesFrom [owlOnProperty, rdfsSubPropertyOf, owlAllValuesFrom] scmAvf2ForS,
    RowSpec.skip owlHasValue [owlOnProperty, rdfsSubPropertyOf, owlHasValue] scmHvForS,
    RowSpec.full owlIntersectionOf scmIntForS,
    RowSpec.full owlUnionOf scmUniForS,
    RowSpec.indep eqDiffSymForS,
    RowSpec.full owlPropertyDisjointWith pdwToDiffForS,
    RowSpec.full owlDisjointWith caxDwToDiffForS,
    RowSpec.full owlDifferentFrom fpDiffToDiffForS,
    RowSpec.full owlDifferentFrom ifpDiffToDiffForS,
    RowSpec.full owlPropertyChainAxiom chainToTransForS,
    RowSpec.additive rdfType prpRflForS,
    RowSpec.indep xsdAxiomsForS,
    RowSpec.additive rdfsRange dtRangeIntersectForS,
    RowSpec.indep caxDwToComplementForS,
    RowSpec.full owlMaxQualifiedCardinality clsMaxqc1ToComplementForS,
    RowSpec.indep minCard1ComprehensionForS,
    RowSpec.full rdfType caxAdcToDwForS,
    RowSpec.additive owlInverseOf inverseOfDomRngFlipForS ]

/-- `rowTable` lists the rows of `conclusionsListS`, in its order. -/
theorem rowTable_f (s : Store) (d : Triple) :
    rowTable.flatMap (fun r => r.f s d) = conclusionsFromS s d := by
  simp only [rowTable, conclusionsFromS, conclusionsListS, List.flatMap_cons, List.flatMap_nil,
    RowSpec.indep, RowSpec.additive, RowSpec.full, RowSpec.skip, List.flatten_cons, List.flatten_nil,
    List.append_nil]

/-- Every delta term of `rowTable` meets its obligation. -/
theorem rowTable_ok : ∀ r ∈ rowTable, r.Ok := by
  intro r hr
  simp only [rowTable, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact RowSpec.indep_ok (fun _ _ _ => rfl)
  · exact RowSpec.indep_ok (fun _ _ _ => rfl)
  · exact RowSpec.indep_ok (fun _ _ _ => rfl)
  · exact RowSpec.indep_ok (fun _ _ _ => rfl)
  · exact RowSpec.additive_ok eqTransForS_add
  · exact RowSpec.additive_ok eqRepSForS_add
  · exact RowSpec.additive_ok eqRepPForS_add
  · exact RowSpec.additive_ok eqRepOForS_add
  · exact RowSpec.additive_ok prpDomForS_add
  · exact RowSpec.additive_ok prpRngForS_add
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.additive_ok prpSympForS_add
  · exact RowSpec.full_ok _ _
  · exact RowSpec.additive_ok prpSpo1ForS_add
  · exact prpSpo2_ok
  · exact RowSpec.additive_ok prpEqp1ForS_add
  · exact RowSpec.additive_ok prpEqp2ForS_add
  · exact RowSpec.additive_ok prpInv1ForS_add
  · exact RowSpec.additive_ok prpInv2ForS_add
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact clsInt1_ok
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.additive_ok caxScoForS_add
  · exact RowSpec.additive_ok caxEqc1ForS_add
  · exact RowSpec.additive_ok caxEqc2ForS_add
  · exact RowSpec.indep_ok (fun _ _ _ => rfl)
  · exact RowSpec.additive_ok scmScoForS_add
  · exact RowSpec.indep_ok (fun _ _ _ => rfl)
  · exact RowSpec.full_ok _ _
  · exact RowSpec.additive_ok scmSpoForS_add
  · exact RowSpec.indep_ok (fun _ _ _ => rfl)
  · exact RowSpec.full_ok _ _
  · exact RowSpec.additive_ok scmDom1ForS_add
  · exact RowSpec.additive_ok scmDom2ForS_add
  · exact RowSpec.additive_ok scmRng1ForS_add
  · exact RowSpec.additive_ok scmRng2ForS_add
  · exact RowSpec.indep_ok (fun _ _ _ => rfl)
  · exact RowSpec.indep_ok (fun _ _ _ => rfl)
  · exact RowSpec.skip_ok scmSvf1ForS_skip
  · exact RowSpec.skip_ok scmSvf2ForS_skip
  · exact RowSpec.skip_ok scmAvf1ForS_skip
  · exact RowSpec.skip_ok scmAvf2ForS_skip
  · exact RowSpec.skip_ok scmHvForS_skip
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.indep_ok (fun _ _ _ => rfl)
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.full_ok _ _
  · exact RowSpec.additive_ok prpRflForS_add
  · exact RowSpec.indep_ok (fun _ _ _ => rfl)
  · exact RowSpec.additive_ok dtRangeIntersectForS_add
  · exact RowSpec.indep_ok (fun _ _ _ => rfl)
  · exact RowSpec.full_ok _ _
  · exact RowSpec.indep_ok (fun _ _ _ => rfl)
  · exact RowSpec.full_ok _ _
  · exact RowSpec.additive_ok inverseOfDomRngFlipForS_add


/-! ### The round -/

/-- The terms the semi-naive round evaluates at a driving triple of the
previous round's input. -/
def oldBlock (sS sD : Store) (lo : Nat) (d : Triple) : List Triple :=
  rowTable.flatMap (fun r => r.delta sS sD lo d)


/-! ### Dispatch on the driving triple's predicate

At an old driving triple only the rows whose guard is its predicate can
emit. `dispatchMap` maps each guard predicate to those rows, in
`rowTable` order, so an old driving triple costs one hash lookup instead
of a test per row (`oldBlock_eq_dispatch`). -/

/-- A row whose guard is not the driving triple's predicate emits nothing at
it. -/
def RowSpec.GuardOk (r : RowSpec) : Prop :=
  ∀ (sS sD : Store) (lo : Nat) (d : Triple), r.guard ≠ some d.p → r.delta sS sD lo d = []

theorem beq_false_of_guard {g : WfIri} {d : Triple} (h : some g ≠ some d.p) :
    (d.p == g) = false := by
  rw [beq_eq_false_iff_ne]
  intro e
  exact h (by rw [e])

theorem rowTable_guard : ∀ r ∈ rowTable, r.GuardOk := by
  intro r hr
  simp only [rowTable, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro _ _ _ _ _; rfl
  · intro _ _ _ _ _; rfl
  · intro _ _ _ _ _; rfl
  · intro _ _ _ _ _; rfl
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlSameAs) h
    simp only [RowSpec.additive, eqTransForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlSameAs) h
    simp only [RowSpec.additive, eqRepSForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlSameAs) h
    simp only [RowSpec.additive, eqRepPForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlSameAs) h
    simp only [RowSpec.additive, eqRepOForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfsDomain) h
    simp only [RowSpec.additive, prpDomForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfsRange) h
    simp only [RowSpec.additive, prpRngForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfType) h
    simp only [RowSpec.full, prpFpForS, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfType) h
    simp only [RowSpec.full, prpIfpForS, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfType) h
    simp only [RowSpec.additive, prpSympForS, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfType) h
    simp only [RowSpec.full, prpTrpForS, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfsSubPropertyOf) h
    simp only [RowSpec.additive, prpSpo1ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlPropertyChainAxiom) h
    simp only [prpSpo2Delta, prpSpo2ForS, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlEquivalentProperty) h
    simp only [RowSpec.additive, prpEqp1ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlEquivalentProperty) h
    simp only [RowSpec.additive, prpEqp2ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlInverseOf) h
    simp only [RowSpec.additive, prpInv1ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlInverseOf) h
    simp only [RowSpec.additive, prpInv2ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlInverseOf) h
    simp only [RowSpec.full, invFpIfpForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlInverseOf) h
    simp only [RowSpec.full, invIfpFpForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlInverseOf) h
    simp only [RowSpec.full, invFpIfpRevForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlInverseOf) h
    simp only [RowSpec.full, invIfpFpRevForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlHasKey) h
    simp only [RowSpec.full, prpKeyForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlIntersectionOf) h
    simp only [clsInt1Delta, clsInt1ForS, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlIntersectionOf) h
    simp only [RowSpec.full, clsInt2ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlUnionOf) h
    simp only [RowSpec.full, clsUniForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlSomeValuesFrom) h
    simp only [RowSpec.full, clsSvf1ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlSomeValuesFrom) h
    simp only [RowSpec.full, clsSvf2ForS, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlAllValuesFrom) h
    simp only [RowSpec.full, clsAvfForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlHasValue) h
    simp only [RowSpec.full, clsHv1ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlHasValue) h
    simp only [RowSpec.full, clsHv2ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlHasSelf) h
    simp only [RowSpec.full, clsHs1ForS, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlHasSelf) h
    simp only [RowSpec.full, clsHs2ForS, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlMaxCardinality) h
    simp only [RowSpec.full, clsMaxc2ForS, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlOneOf) h
    simp only [RowSpec.full, clsOoForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfsSubClassOf) h
    simp only [RowSpec.additive, caxScoForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlEquivalentClass) h
    simp only [RowSpec.additive, caxEqc1ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlEquivalentClass) h
    simp only [RowSpec.additive, caxEqc2ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro _ _ _ _ _; rfl
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfsSubClassOf) h
    simp only [RowSpec.additive, scmScoForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro _ _ _ _ _; rfl
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfsSubClassOf) h
    simp only [RowSpec.full, scmEqc2ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfsSubPropertyOf) h
    simp only [RowSpec.additive, scmSpoForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro _ _ _ _ _; rfl
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfsSubPropertyOf) h
    simp only [RowSpec.full, scmEqp2ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfsDomain) h
    simp only [RowSpec.additive, scmDom1ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfsDomain) h
    simp only [RowSpec.additive, scmDom2ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfsRange) h
    simp only [RowSpec.additive, scmRng1ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfsRange) h
    simp only [RowSpec.additive, scmRng2ForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro _ _ _ _ _; rfl
  · intro _ _ _ _ _; rfl
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlSomeValuesFrom) h
    simp only [RowSpec.skip, scmSvf1ForS, hb, Bool.false_eq_true, ↓reduceIte, ite_self]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlSomeValuesFrom) h
    simp only [RowSpec.skip, scmSvf2ForS, hb, Bool.false_eq_true, ↓reduceIte, ite_self]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlAllValuesFrom) h
    simp only [RowSpec.skip, scmAvf1ForS, hb, Bool.false_eq_true, ↓reduceIte, ite_self]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlAllValuesFrom) h
    simp only [RowSpec.skip, scmAvf2ForS, hb, Bool.false_eq_true, ↓reduceIte, ite_self]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlHasValue) h
    simp only [RowSpec.skip, scmHvForS, hb, Bool.false_eq_true, ↓reduceIte, ite_self]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlIntersectionOf) h
    simp only [RowSpec.full, scmIntForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlUnionOf) h
    simp only [RowSpec.full, scmUniForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro _ _ _ _ _; rfl
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlPropertyDisjointWith) h
    simp only [RowSpec.full, pdwToDiffForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlDisjointWith) h
    simp only [RowSpec.full, caxDwToDiffForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlDifferentFrom) h
    simp only [RowSpec.full, fpDiffToDiffForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlDifferentFrom) h
    simp only [RowSpec.full, ifpDiffToDiffForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlPropertyChainAxiom) h
    simp only [RowSpec.full, chainToTransForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfType) h
    simp only [RowSpec.additive, prpRflForS, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · intro _ _ _ _ _; rfl
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfsRange) h
    simp only [RowSpec.additive, dtRangeIntersectForS, hb, Bool.false_eq_true, ↓reduceIte]
  · intro _ _ _ _ _; rfl
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlMaxQualifiedCardinality) h
    simp only [RowSpec.full, clsMaxqc1ToComplementForS, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · intro _ _ _ _ _; rfl
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := rdfType) h
    simp only [RowSpec.full, caxAdcToDwForS, hb, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  · intro sS sD lo d h
    have hb := beq_false_of_guard (g := owlInverseOf) h
    simp only [RowSpec.additive, inverseOfDomRngFlipForS, hb, Bool.false_eq_true, ↓reduceIte]

/-- The rows of `rowTable` whose guard is `p`, in `rowTable` order. -/
def rowsFor (p : WfIri) : List RowSpec := rowTable.filter (fun r => r.guard == some p)

/-- Each guard predicate, mapped to its rows. -/
def dispatchMap : Std.HashMap WfIri (List RowSpec) :=
  (rowTable.filterMap (·.guard)).foldl (fun m p => m.insert p (rowsFor p)) ∅

theorem foldl_insert_getD (ps : List WfIri) :
    ∀ (m : Std.HashMap WfIri (List RowSpec)) (q : WfIri),
      (ps.foldl (fun m p => m.insert p (rowsFor p)) m).getD q [] =
        if q ∈ ps then rowsFor q else m.getD q [] := by
  induction ps with
  | nil => intro m q; simp
  | cons p ps ih =>
    intro m q
    simp only [List.foldl_cons, ih, Std.HashMap.getD_insert, List.mem_cons]
    by_cases hq : q ∈ ps
    · simp [hq]
    · by_cases hpq : p = q
      · subst hpq; simp
      · have hb : (p == q) = false := beq_eq_false_iff_ne.mpr hpq
        have hor : ¬ (q = p ∨ q ∈ ps) := fun h => h.elim (fun e => hpq e.symm) hq
        rw [if_neg hq, if_neg hor, hb]
        rfl

theorem dispatchMap_getD (q : WfIri) : dispatchMap.getD q [] = rowsFor q := by
  unfold dispatchMap
  rw [foldl_insert_getD]
  split
  · rfl
  · rename_i hq
    simp only [Std.HashMap.getD_empty]
    symm
    unfold rowsFor
    refine List.filter_eq_nil_iff.mpr (fun r hr hg => hq ?_)
    have : r.guard = some q := by simpa using hg
    exact List.mem_filterMap.mpr ⟨r, hr, this⟩

theorem flatMap_filter_of_nil {α β : Type} {l : List α} {f : α → List β} {p : α → Bool}
    (h : ∀ x ∈ l, p x = false → f x = []) : (l.filter p).flatMap f = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have ih' := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    by_cases hx : p x = true
    · simp [hx, ih']
    · have hf := h x List.mem_cons_self (by simpa using hx)
      simp [hx, hf, ih']

/-- The block of an old driving triple, through the dispatch map. -/
def oldBlockFast (sS sD : Store) (lo : Nat) (d : Triple) : List Triple :=
  (dispatchMap.getD d.p []).flatMap (fun r => r.delta sS sD lo d)

theorem oldBlockFast_eq (sS sD : Store) (lo : Nat) (d : Triple) :
    oldBlockFast sS sD lo d = oldBlock sS sD lo d := by
  unfold oldBlockFast oldBlock
  rw [dispatchMap_getD, rowsFor, flatMap_filter_of_nil]
  intro r hr hg
  apply rowTable_guard r hr
  intro e
  rw [e] at hg
  simp at hg

/-- Everything a semi-naive round emits, before deduplication. `lo` is the
length of the previous round's input: the first `lo` triples of `sS.graph`
are old driving triples, the rest are the delta. -/
def stepConclusionsSN (sS sD : Store) (lo : Nat) : List Triple :=
  axiomTriples ++ ((sS.graph.take lo).flatMap (oldBlockFast sS sD lo) ++
    (sS.graph.drop lo).flatMap (conclusionsFromS sS))

/-- One semi-naive round over the index: the delta's own index is built
from the triples after position `lo`. -/
def stepSNI (i : Index) (lo : Nat) : Index :=
  i.insertAll (stepConclusionsSN (Store.ofIndex i)
    (Store.ofIndex (if lo = 0 then Index.empty else Index.ofGraph (i.toGraph.drop lo))) lo)

/-- The semi-naive loop, with the naive loop's stopping rule (the size did
not change). The first round has `lo = 0`, so every driving triple is new
and the round is the naive round. -/
def closureSNI (i : Index) (lo : Nat) (fuel : Nat) : Index :=
  match fuel with
  | 0     => i
  | n + 1 =>
      let i' := stepSNI i lo
      if i'.all.size = i.all.size then i else closureSNI i' i.all.size n

/-- The semi-naive closure of a graph, as a graph. -/
def indexedClosureSN (g : Graph) (fuel : Nat) : Graph :=
  (closureSNI (Index.ofGraph g) 0 fuel).toGraph

/-! ### `addAll` drops what the graph holds -/

theorem memB_addOne_of_memB {g : Graph} {t u : Triple} (h : RL.memB g u = true) :
    RL.memB (addOne g t) u = true := by
  unfold addOne
  split
  · exact h
  · simp only [RL.memB, List.any_append, Bool.or_eq_true] at h ⊢
    exact Or.inl h

theorem memB_addAll_of_memB (ts : List Triple) :
    ∀ {g : Graph} {u : Triple}, RL.memB g u = true → RL.memB (addAll g ts) u = true := by
  induction ts with
  | nil => intro g u h; exact h
  | cons t ts ih => intro g u h; exact ih (memB_addOne_of_memB h)

theorem memB_addAll_of_mem_list (ts : List Triple) :
    ∀ {g : Graph} {u : Triple}, u ∈ ts → RL.memB (addAll g ts) u = true := by
  induction ts with
  | nil => intro g u h; cases h
  | cons t ts ih =>
    intro g u h
    show RL.memB (addAll (addOne g t) ts) u = true
    rcases List.mem_cons.mp h with rfl | h
    · apply memB_addAll_of_memB
      unfold addOne
      split
      · assumption
      · simp [RL.memB]
    · exact ih h

theorem addAll_prefix (ts : List Triple) :
    ∀ (g : Graph), ∃ x, addAll g ts = g ++ x := by
  induction ts with
  | nil => intro g; exact ⟨[], by simp [addAll]⟩
  | cons t ts ih =>
    intro g
    obtain ⟨x, hx⟩ := ih (addOne g t)
    unfold addOne at hx
    split at hx
    · exact ⟨x, by simp only [addAll, addOne]; rw [if_pos (by assumption)]; exact hx⟩
    · exact ⟨[t] ++ x, by simp only [addAll, addOne]; rw [if_neg (by assumption)]; simp [hx]⟩

/-- `addAll` over a graph that already holds every triple of `S` ignores
the triples of `S` in its list. -/
theorem addAll_filter_of_subset (S : Graph) (ts : List Triple) :
    ∀ (g : Graph), (∀ u, RL.memB S u = true → RL.memB g u = true) →
      addAll g ts = addAll g (ts.filter (fun t => !RL.memB S t)) := by
  induction ts with
  | nil => intro g _; rfl
  | cons t ts ih =>
    intro g hg
    by_cases ht : RL.memB S t = true
    · have hgt : RL.memB g t = true := hg t ht
      simp only [addAll, List.filter_cons, ht, Bool.not_true, Bool.false_eq_true, if_false]
      have : addOne g t = g := by unfold addOne; rw [if_pos hgt]
      rw [this]
      exact ih g hg
    · simp only [addAll, List.filter_cons, Bool.not_eq_true] at ht ⊢
      simp only [ht, Bool.not_false, if_true, addAll]
      exact ih (addOne g t) (fun u hu => memB_addOne_of_memB (hg u hu))

/-! ### The round is the naive round -/

theorem flatMap_filter_congr {α β : Type} {l : List α} {f g : α → List β} {q : β → Bool}
    (h : ∀ x ∈ l, (f x).filter q = (g x).filter q) :
    (l.flatMap f).filter q = (l.flatMap g).filter q := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.filter_append]
    rw [h x (List.mem_cons_self), ih (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-- At an old driving triple, the delta terms and the full rows agree on
every triple outside `S`. -/
theorem oldBlock_filter {P D : Graph} {d : Triple}
    (hS : ∀ t ∈ conclusionsFrom P d, RL.memB (P ++ D) t = true) :
    (oldBlock (Store.ofGraph (P ++ D)) (Store.ofGraph D) P.length d).filter
        (fun t => !RL.memB (P ++ D) t) =
      (conclusionsFromS (Store.ofGraph (P ++ D)) d).filter
        (fun t => !RL.memB (P ++ D) t) := by
  rw [← rowTable_f]
  unfold oldBlock
  apply flatMap_filter_congr
  intro r hr
  refine (rowTable_ok r hr P D d _ ?_).symm
  intro t ht
  have hc : t ∈ conclusionsFrom P d := by
    rw [← conclusionsFromS_ofGraph, ← rowTable_f]
    exact List.mem_flatMap.mpr ⟨r, hr, ht⟩
  simp [hS t hc]

/-- **One semi-naive round is one naive round**, as a list, when the
previous round's input `P` is a prefix of `S` and every conclusion of a
driving triple of `P` over `P` is already in `S`. -/
theorem addAll_stepConclusionsSN {P D : Graph} {lo : Nat} (hlo : P.length = lo)
    (hS : ∀ d ∈ P, ∀ t ∈ conclusionsFrom P d, RL.memB (P ++ D) t = true) :
    addAll (P ++ D) (stepConclusionsSN (Store.ofGraph (P ++ D)) (Store.ofGraph D) lo) =
      RL.step (P ++ D) := by
  have hself : ∀ u, RL.memB (P ++ D) u = true → RL.memB (P ++ D) u = true := fun _ h => h
  rw [RL.step, ← stepConclusionsS_ofGraph,
    addAll_filter_of_subset (P ++ D) _ _ hself,
    addAll_filter_of_subset (P ++ D) (stepConclusionsS _) _ hself]
  congr 1
  have hg : (Store.ofGraph (P ++ D)).graph = P ++ D := rfl
  unfold stepConclusionsSN stepConclusionsS
  rw [hg, List.take_left' hlo, List.drop_left' hlo,
    show oldBlockFast (Store.ofGraph (P ++ D)) (Store.ofGraph D) lo =
      oldBlock (Store.ofGraph (P ++ D)) (Store.ofGraph D) lo from funext (oldBlockFast_eq _ _ _)]
  conv => rhs; rw [List.flatMap_append]
  simp only [List.filter_append]
  congr 2
  subst hlo
  exact flatMap_filter_congr (fun d hd => oldBlock_filter (hS d hd))

/-- What a semi-naive round needs of its input `S` and its `lo`: `S` is
the previous input `P` followed by a delta, `lo` is the length of `P`, and
`S` holds every conclusion of a driving triple of `P` over `P`. -/
def RoundOk (S : Graph) (lo : Nat) : Prop :=
  ∃ P D, S = P ++ D ∧ P.length = lo ∧
    ∀ d ∈ P, ∀ t ∈ conclusionsFrom P d, RL.memB S t = true

theorem RoundOk.start (S : Graph) : RoundOk S 0 :=
  ⟨[], S, rfl, rfl, fun _ h => by cases h⟩

theorem RoundOk.next (S : Graph) : RoundOk (RL.step S) S.length := by
  obtain ⟨x, hx⟩ := addAll_prefix (stepConclusions S) S
  refine ⟨S, x, hx, rfl, ?_⟩
  intro d hd t ht
  unfold RL.step
  apply memB_addAll_of_mem_list
  unfold stepConclusions
  exact List.mem_append_right _ (List.mem_flatMap.mpr ⟨d, hd, ht⟩)

/-- One indexed semi-naive round pictures one list round. -/
theorem Index.Wf.stepSN {i : Index} {S : Graph} {lo : Nat} (h : i.Wf S)
    (hr : RoundOk S lo) : (stepSNI i lo).Wf (RL.step S) := by
  obtain ⟨P, D, rfl, hlo, hS⟩ := hr
  unfold stepSNI
  have hD : i.toGraph.drop lo = D := by
    rw [Index.toGraph, h.all, List.drop_left' hlo]
  -- With `lo = 0` no driving triple is old, so the delta's store is never read.
  have hsame : stepConclusionsSN (Store.ofIndex i)
      (Store.ofIndex (if lo = 0 then Index.empty else Index.ofGraph (i.toGraph.drop lo))) lo =
      stepConclusionsSN (Store.ofIndex i) (Store.ofGraph D) lo := by
    by_cases h0 : lo = 0
    · subst h0
      simp [stepConclusionsSN]
    · rw [if_neg h0, hD, Store.ofIndex_eq (Index.Wf.ofGraph D)]
  rw [hsame, Store.ofIndex_eq h, ← addAll_stepConclusionsSN hlo hS]
  exact h.insertAll _

/-- The semi-naive loop pictures the list loop at every fuel. -/
theorem Index.Wf.closureSN (fuel : Nat) :
    ∀ {i : Index} {S : Graph} {lo : Nat}, i.Wf S → RoundOk S lo →
      (closureSNI i lo fuel).Wf (RL.closure S fuel) := by
  induction fuel with
  | zero => intro i S lo h _; exact h
  | succ n ih =>
    intro i S lo h hr
    simp only [closureSNI, RL.closure]
    have hs : (stepSNI i lo).all.size = (RL.step S).length := by
      rw [← Array.length_toList, (h.stepSN hr).all]
    have hi : i.all.size = S.length := by
      rw [← Array.length_toList, h.all]
    rw [hs, hi]
    split
    · exact h
    · exact ih (h.stepSN hr) (RoundOk.next S)

/-- **The semi-naive closure is the naive closure**, as a list, at every
fuel. -/
theorem indexedClosureSN_eq (g : Graph) (fuel : Nat) :
    indexedClosureSN g fuel = RL.closure g fuel :=
  (Index.Wf.closureSN fuel (Index.Wf.ofGraph g) (RoundOk.start g)).all

/-! ## Section 10 — the semi-naive indexed loop is what the compiler emits

`closure` and `closureFix` (`RLClosure.lean`) are the specification: each round
reads its premises by scanning the graph and adds its conclusions with a list
scan (`memB`). Run on a chain of 80 subclass axioms, the command line spent
83 percent of its instructions in that scan, and the time grew 18 to 20 times for
each doubling of the chain (survey of 2026-10-10,
`docs/designissues/2026-10-10-lean-vs-fstar-performance.md`). `indexedClosure`
(naive rounds over the index) and `indexedClosureSN` (semi-naive rounds over the
index, Section 11) return the same list at every fuel (`indexedClosure_eq`,
`indexedClosureSN_eq`). The two `csimp` theorems below make every function
compiled after this module call the semi-naive loop in place of the scanning
one. Until 2026-10-13 they named the naive indexed loop
(https://github.com/danbri/factoidal/issues/756 item 2). The definitions of
`closure` and `closureFix`, and every theorem stated about them, do not change.

`closureFix` is defined in `RLClosure.lean`, before this module, so its own
body keeps calling `closure`. `closureFixIndexed` is the function the compiler
substitutes for it in the modules that import this one. -/

/-- `closureFix` through the semi-naive indexed loop. -/
def closureFixIndexed (g : Graph) : Graph :=
  indexedClosureSN g (closureFuelBound g)

theorem closureFix_eq_closureFixIndexed (g : Graph) :
    closureFix g = closureFixIndexed g :=
  (indexedClosureSN_eq g (closureFuelBound g)).symm

/-- The compiler calls `indexedClosureSN` wherever the source says `closure`. -/
@[csimp] theorem closure_eq_indexedClosure : @closure = @indexedClosureSN :=
  funext fun g => funext fun fuel => (indexedClosureSN_eq g fuel).symm

/-- The compiler calls `closureFixIndexed` wherever the source says `closureFix`. -/
@[csimp] theorem closureFix_eq_indexed : @closureFix = @closureFixIndexed :=
  funext closureFix_eq_closureFixIndexed

end L4Factoidal.OWL.RL
