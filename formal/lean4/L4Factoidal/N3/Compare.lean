/-
L4Factoidal.N3.Compare — whether two N3 graphs are the same up to the
names of their blank nodes.

Two N3 graphs are compared as sets of triples, a graph term as the set of its
triples, after `{}` is read as `true` (`N3Term.normalize`; Notation3
Semantics § "Log Semantics"), and up to a bijection of blank-node labels
(RDF 1.1 Concepts § 3.6 "Graph Comparison", extended to the blank nodes inside
graph terms, which the reader labels per graph term).

Method: individualisation and refinement. Every label starts with the same
colour; a round gives each label the hash of its colour and of the sorted
keys of the top-level triples it occurs in (at any depth), with the label
itself written `*` and the others written by their colour. Four rounds. When
the colours of each graph are distinct, both graphs are renamed to their
colours and compared as sets of keys: equal sets mean isomorphic graphs (the
colours are computed from the structure only, so isomorphic graphs get the
same colours). When a graph has two labels of one colour (a symmetric graph),
one label of `g1` with that colour is paired in turn with each label of `g2`
with that colour, both get a new colour, and the search goes on
(`isoSearch`). If no pairing gives `equal` the graphs are not isomorphic. A
search deeper than 64 pairings is `budgetExceeded`, which is never a pass
(`Harness/N3Run.lean`).

The colours are 64-bit hashes; two different structures with one hash make
the method report `budgetExceeded` or, if both graphs are renamed to the same
colliding colours, `equal` for graphs that are not isomorphic. No theorem
excludes that; it is the reason this module is a test oracle and not a
specification.

No `sorry`, no `axiom`, no `partial def`.
-/
import L4Factoidal.N3.Writer
import L4Factoidal.RDF.Isomorphism
import Std.Data.HashMap

namespace L4Factoidal.N3

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- Sort and remove repeats. -/
def sortDedup (xs : List String) : List String :=
  let sorted := xs.mergeSort (fun a b => decide (a ≤ b))
  (sorted.foldl (fun (acc : List String) x =>
    match acc with
    | y :: _ => if x == y then acc else x :: acc
    | [] => [x]) []).reverse

/-- The key of a term, blank nodes written by `lab`, graph terms as sorted
sets, `{}` as `true`. -/
def N3Term.key (lab : BNodeId → String) : N3Term → String
  | .iri i => "<" ++ i.val ++ ">"
  | .bnode b => lab b
  | .lit l => tsLiteralToTurtleBy (fun s => "<" ++ s ++ ">") false l
  | .var v => "?" ++ v
  | .triple s p o =>
      tsTermToTurtleBy (fun s => "<" ++ s ++ ">") false ((Term.tripleTerm s p o).renameBnodes lab)
  | .list xs => "(" ++ String.join (xs.attach.map fun ⟨x, _⟩ => " " ++ x.key lab) ++ " )"
  | .graph ts =>
      if ts.isEmpty then tsLiteralToTurtleBy (fun s => "<" ++ s ++ ">") false trueLit
      else "{" ++ joinWith " . " (sortDedup (ts.attach.map fun ⟨(s, p, o), _h⟩ =>
        s.key lab ++ " " ++ p.key lab ++ " " ++ o.key lab)) ++ "}"
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  · have := List.sizeOf_lt_of_mem ‹_›; omega
  · exact sizeOf_lt_triple_s _h
  · exact sizeOf_lt_triple_p _h
  · exact sizeOf_lt_triple_o _h

/-- The blank-node labels of a term, at any depth, with repeats. -/
def N3Term.allBnodes : N3Term → List BNodeId
  | .bnode b => [b]
  | .triple s p o => (Term.tripleTerm s p o).bnodes
  | .list xs => (xs.attach.map fun ⟨x, _⟩ => x.allBnodes).flatten
  | .graph ts => (ts.attach.map fun ⟨(s, p, o), _h⟩ =>
      s.allBnodes ++ p.allBnodes ++ o.allBnodes).flatten
  | _ => []
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  · have := List.sizeOf_lt_of_mem ‹_›; omega
  · exact sizeOf_lt_triple_s _h
  · exact sizeOf_lt_triple_p _h
  · exact sizeOf_lt_triple_o _h

def tripleKey (lab : BNodeId → String) (t : N3Triple) : String :=
  t.1.key lab ++ " " ++ t.2.1.key lab ++ " " ++ t.2.2.key lab

def tripleBnodes (t : N3Triple) : List BNodeId :=
  t.1.allBnodes ++ t.2.1.allBnodes ++ t.2.2.allBnodes

/-- The labels of a graph, each once. -/
def graphBnodes (g : N3Graph) : List BNodeId :=
  sortDedup (g.map tripleBnodes).flatten

/-- For each label, the indices of the triples it occurs in (in any depth). -/
def occurrences (g : Array N3Triple) : Std.HashMap BNodeId (List Nat) :=
  (g.foldl (fun (acc : Std.HashMap BNodeId (List Nat) × Nat) t =>
    let (m, i) := acc
    (sortDedup (tripleBnodes t) |>.foldl (fun m b => m.insert b (i :: m.getD b [])) m, i + 1))
    ({}, 0)).1

/-- One refinement round (module header): a label's new colour is the hash of
its old colour and of the sorted keys of the triples it occurs in. -/
def refineRound (g : Array N3Triple) (occ : Std.HashMap BNodeId (List Nat)) (bs : List BNodeId)
    (col : Std.HashMap BNodeId String) : Std.HashMap BNodeId String :=
  let lab (me : BNodeId) (x : BNodeId) : String :=
    if x == me then "*" else col.getD x "_"
  bs.foldl (fun acc b =>
    let ts := (occ.getD b []).filterMap fun i => g[i]?
    let keys := sortDedup (ts.map (tripleKey (lab b)))
    acc.insert b ("_:c" ++ toString (hash (col.getD b "_" ++ "\n" ++ String.intercalate "\n" keys)))) {}

def refineN (g : Array N3Triple) (occ : Std.HashMap BNodeId (List Nat)) (bs : List BNodeId) :
    Nat → Std.HashMap BNodeId String → Std.HashMap BNodeId String
  | 0, col => col
  | n + 1, col => refineN g occ bs n (refineRound g occ bs col)

/-- A graph prepared for refinement: its triples and the label index. -/
structure Prepared where
  g   : Array N3Triple
  occ : Std.HashMap BNodeId (List Nat)
  bs  : List BNodeId

def prepare (g : N3Graph) : Prepared :=
  let a := g.toArray
  { g := a, occ := occurrences a, bs := graphBnodes g }

def refine (p : Prepared) (n : Nat) (col : Std.HashMap BNodeId String) : Std.HashMap BNodeId String :=
  refineN p.g p.occ p.bs n col

/-- The keys of a graph's triples, labels written by their colour. -/
def graphKeys (g : N3Graph) (col : Std.HashMap BNodeId String) : List String :=
  sortDedup (g.map (tripleKey fun b => col.getD b "_"))

/-- The colours of the labels, sorted, with repeats. -/
def colourList (bs : List BNodeId) (col : Std.HashMap BNodeId String) : List String :=
  (bs.map fun b => col.getD b "_").mergeSort (fun a b => decide (a ≤ b))

/-- The rounds of one refinement. -/
def refineRounds : Nat := 4

/-- Individualisation and refinement. With the colours of both graphs
refined: different colour lists mean different graphs; distinct colours
decide by the keys; otherwise take the first label `x` of `g1` whose colour
is shared, and try each label `y` of `g2` with that colour: give both one new
colour, refine, and search on. `fuel` bounds the number of labels
individualised on one path; the search stops at the first `equal` and at the
first `budgetExceeded`. -/
def isoSearch (p1 p2 : Prepared) :
    Nat → Std.HashMap BNodeId String → Std.HashMap BNodeId String → IsoOutcome
  | 0, _, _ => .budgetExceeded
  | fuel + 1, c1, c2 =>
    let b1 := p1.bs
    let b2 := p2.bs
    let g1 := p1.g.toList
    let g2 := p2.g.toList
    let l1 := colourList b1 c1
    if l1 != colourList b2 c2 then .notEqual
    else if (sortDedup l1).length == b1.length then
      if graphKeys g1 c1 == graphKeys g2 c2 then .equal else .notEqual
    else
      let counts : Std.HashMap String Nat :=
        b1.foldl (fun m x => let c := c1.getD x "_"; m.insert c (m.getD c 0 + 1)) {}
      match b1.find? (fun b => counts.getD (c1.getD b "_") 0 > 1) with
      | none => .budgetExceeded
      | some x =>
          let colour := c1.getD x "_"
          let mark := "!" ++ toString fuel
          let cands := b2.filter fun y => c2.getD y "_" == colour
          let step : IsoOutcome → BNodeId → IsoOutcome := fun acc y =>
            match acc with
            | .equal => .equal
            | .budgetExceeded => .budgetExceeded
            | .notEqual =>
                let r := isoSearch p1 p2 fuel
                  (refine p1 refineRounds (c1.insert x (colour ++ mark)))
                  (refine p2 refineRounds (c2.insert y (colour ++ mark)))
                r
          cands.foldl step .notEqual

/-- Whether two N3 graphs are isomorphic (module header). -/
def n3Isomorphic (g1 g2 : N3Graph) : IsoOutcome :=
  let b1 := graphBnodes g1
  let b2 := graphBnodes g2
  let blind1 := graphKeys g1 {}
  let blind2 := graphKeys g2 {}
  if b1.length != b2.length || blind1 != blind2 then .notEqual
  else
    let p1 := prepare g1
    let p2 := prepare g2
    isoSearch p1 p2 (min 64 b1.length + 1) (refine p1 refineRounds {}) (refine p2 refineRounds {})

/-! ## Labels in order of first occurrence

`relabel` names the blank nodes `b0`, `b1`, ... in the order in which they
first occur (triples in order; subject, predicate, object; list members and
graph-term triples in order). Two graphs that list the same triples in the
same order, up to the names of their blank nodes, relabel to equal values;
the writer keeps the order of triples and of terms, so a writer round trip is
checked with `relabel` and `==`, with no search. -/

structure RelabelSt where
  m : Std.HashMap BNodeId String := {}
  n : Nat := 0

def RelabelSt.get (st : RelabelSt) (b : BNodeId) : String × RelabelSt :=
  match st.m[b]? with
  | some l => (l, st)
  | none => let l := "b" ++ toString st.n; (l, { m := st.m.insert b l, n := st.n + 1 })

def N3Term.relabel (st : RelabelSt) : N3Term → N3Term × RelabelSt
  | .bnode b => let (l, st1) := st.get b; (.bnode l, st1)
  | .triple s p o =>
      let st1 := (Term.tripleTerm s p o).bnodes.foldl (fun acc b => (acc.get b).2) st
      let f := fun b => st1.m.getD b b
      (.triple (s.renameBnodes f) p (o.renameBnodes f), st1)
  | .list xs =>
      let (ys, st1) := xs.attach.foldl (fun (acc : List N3Term × RelabelSt) ⟨x, _⟩ =>
        let (y, s1) := x.relabel acc.2; (y :: acc.1, s1)) ([], st)
      (.list ys.reverse, st1)
  | .graph ts =>
      let (us, st1) := ts.attach.foldl (fun (acc : List N3Triple × RelabelSt) ⟨(s, p, o), _h⟩ =>
        let (s', s1) := s.relabel acc.2
        let (p', s2) := p.relabel s1
        let (o', s3) := o.relabel s2
        ((s', p', o') :: acc.1, s3)) ([], st)
      (.graph us.reverse, st1)
  | t => (t, st)
termination_by t => sizeOf t
decreasing_by
  all_goals simp_wf
  · have := List.sizeOf_lt_of_mem ‹_›; omega
  · exact sizeOf_lt_triple_s _h
  · exact sizeOf_lt_triple_p _h
  · exact sizeOf_lt_triple_o _h

def relabel (g : N3Graph) : N3Graph :=
  (g.foldl (fun (acc : List N3Triple × RelabelSt) (s, p, o) =>
    let (s', s1) := s.relabel acc.2
    let (p', s2) := p.relabel s1
    let (o', s3) := o.relabel s2
    ((s', p', o') :: acc.1, s3)) ([], {})).1.reverse

end L4Factoidal.N3
