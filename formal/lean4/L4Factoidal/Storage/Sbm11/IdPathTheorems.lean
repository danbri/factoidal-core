/-
L4Factoidal.Storage.Sbm11.IdPathTheorems — property paths on the SBM11 id
path (https://github.com/danbri/factoidal/issues/954): the decoding theorem
for the pair relation of a path over ids against the reference evaluator's
`SPARQL.evalPath` (SPARQL 1.1 sections 9 and 18.4), and for the rows of a
path pattern against `pathResultToSolutions` and `addConstantReflexivity`.

## Over ids

A graph is a list of id triples (subject, predicate, object), `G`; the
reference graph `g` is its decoding (`GraphDecodes`: per triple, the subject
and the object decode to the reference triple's terms, and the reference
predicate equals an IRI `i` exactly when `pid i` is the triple's predicate
id). `idEvalPath` is `evalPath` with `Term.eqb` replaced by id equality and the
literal test by `notLit`; the closures are the reference's own
`pathFixpoint` with the same fuel (the number of nodes of the graph).

* `evalPath_decode`: decoding `idEvalPath p G` gives `evalPath p g`, list for
  list, when `Term.eqb` of two decoded ids is id equality on the ids of the
  graph (`hdec`), and `notLit` agrees with `isNotLiteral` there (`hlit`).
* `pathRows_decode`: decoding the rows `idPathRows` builds from the pairs, after
  `idConstRefl` (the reflexive pair of each constant endpoint of `p*` and
  `p?` that the pairs lack), gives `pathResultToSolutions` after
  `addConstantReflexivity`, when the endpoint constants decode to the
  pattern's terms and are among the ids `hdec` covers.

Not proved here (open, the step of lemma L5g″ of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md): that
`IdQuery.evalIM` under a restriction (scans of PSO or POS with candidates,
the relation of a sequence restricted by the objects of its first part) gives
the pairs of `idEvalPath` whose subject (or object) is in the restriction, as
a multiset; and that the `Table` of `IdQuery.pathTableM` denotes the rows of
`idPathRows`. Tested by the gate queries `tests/sbm11/gate/ids-path-*.rq`
(with blocks of 2 rows and candidates in every scan, part (l1)) and by the
census (`tests/sbm11/census.sh`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.Storage.Sbm11.OptJoinTheorems
import L4Factoidal.SPARQL.Algebra

namespace L4Factoidal.Storage.Sbm11.IdPath

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.OptJoin (IdRow decRow filterMap_congr')

/-! ## The model over ids -/

/-- A triple of ids: subject, predicate, object. -/
abbrev IdTriple := UInt64 × UInt64 × UInt64

/-- A relation of id pairs, as a list. -/
abbrev IdPairs := List (UInt64 × UInt64)

/-- `pathPairEq` on ids. -/
def idPairEq (p q : UInt64 × UInt64) : Bool := p.1 == q.1 && p.2 == q.2

/-- `dedupPath` on ids: the last occurrence of each pair kept. -/
def idDedup : IdPairs → IdPairs
  | [] => []
  | x :: xs => if xs.any (idPairEq x) then idDedup xs else x :: idDedup xs

/-- `graphNodes` on ids. -/
def idGraphNodes (G : List IdTriple) : List UInt64 :=
  (idDedup ((G.map (·.1) ++ G.map (·.2.2)).map (fun n => (n, n)))).map Prod.fst

/-- `pathExtend` on ids. -/
def idExtend (step cur : IdPairs) : IdPairs :=
  let newPairs := cur.flatMap (fun p1 =>
    step.filterMap (fun p2 => if p1.2 == p2.1 then some (p1.1, p2.2) else none))
  idDedup (cur ++ newPairs)

/-- `pathFixpoint` on ids. -/
def idFixpoint (step : IdPairs) : IdPairs → Nat → IdPairs
  | cur, 0 => cur
  | cur, n + 1 =>
    let next := idExtend step cur
    if next.length == cur.length then cur else idFixpoint step next n

/-- The direct pairs of a negated property set on ids. -/
def idNpsDirect (pid : WfIri → Option UInt64) (ex : List WfIri) (G : List IdTriple) : IdPairs :=
  G.filterMap fun x => if ex.any (fun j => pid j == some x.2.1) then none else some (x.1, x.2.2)

/-- The inverse pairs of a negated property set on ids. -/
def idNpsInverse (pid : WfIri → Option UInt64) (ex : List WfIri) (G : List IdTriple) : IdPairs :=
  G.filterMap fun x => if ex.any (fun j => pid j == some x.2.1) then none else some (x.2.2, x.1)

/-- `evalPath` on ids: `pid i` the id of the IRI `i` (`none`: no triple has
    it), `notLit` the literal test of `^p`. -/
def idEvalPath (pid : WfIri → Option UInt64) (notLit : UInt64 → Bool) :
    PropertyPath → List IdTriple → IdPairs
  | .iri i, G => G.filterMap fun x => if pid i == some x.2.1 then some (x.1, x.2.2) else none
  | .inverse p, G =>
    (idEvalPath pid notLit p G).filterMap fun pr => if notLit pr.2 then some (pr.2, pr.1) else none
  | .sequence p1 p2, G =>
    let r1 := idEvalPath pid notLit p1 G
    let r2 := idEvalPath pid notLit p2 G
    r1.flatMap fun a => r2.filterMap fun b => if a.2 == b.1 then some (a.1, b.2) else none
  | .alternative p1 p2, G => idEvalPath pid notLit p1 G ++ idEvalPath pid notLit p2 G
  | .zeroOrOne p, G => idDedup ((idGraphNodes G).map (fun n => (n, n)) ++ idEvalPath pid notLit p G)
  | .zeroOrMore p, G =>
    let nodes := idGraphNodes G
    let step := idEvalPath pid notLit p G
    idFixpoint step (idDedup (nodes.map (fun n => (n, n)) ++ step)) nodes.length
  | .oneOrMore p, G =>
    let nodes := idGraphNodes G
    let step := idEvalPath pid notLit p G
    idFixpoint step (idDedup step) nodes.length
  | .negatedSet ps, G =>
    let exD := negatedDirectIris ps
    let exI := negatedInverseIris ps
    let hasDirect := !exD.isEmpty
    let hasInverse := !exI.isEmpty
    (if hasInverse && !hasDirect then [] else idNpsDirect pid exD G) ++
      (if hasDirect && !hasInverse then [] else idNpsInverse pid exI G)

/-! ## Decoding -/

/-- Decode a pair. -/
def decPair (dec : UInt64 → Term) (p : UInt64 × UInt64) : Term × Term := (dec p.1, dec p.2)

/-- Every id of a relation satisfies `ok`. -/
def PairsOk (ok : UInt64 → Prop) (l : IdPairs) : Prop := ∀ pr ∈ l, ok pr.1 ∧ ok pr.2

/-- One id triple decodes to one reference triple. -/
def TripleDecodes (dec : UInt64 → Term) (ok : UInt64 → Prop) (pid : WfIri → Option UInt64)
    (x : IdTriple) (t : Triple) : Prop :=
  dec x.1 = t.s.toTerm ∧ dec x.2.2 = t.o ∧ ok x.1 ∧ ok x.2.2 ∧
    ∀ i, (t.p == i) = (pid i == some x.2.1)

/-- The id graph decodes to the reference graph, triple for triple. -/
def GraphDecodes (dec : UInt64 → Term) (ok : UInt64 → Prop) (pid : WfIri → Option UInt64) :
    List IdTriple → Graph → Prop
  | [], [] => True
  | x :: xs, t :: ts => TripleDecodes dec ok pid x t ∧ GraphDecodes dec ok pid xs ts
  | _, _ => False

theorem any_congr' {α : Type} (f g : α → Bool) :
    ∀ (l : List α), (∀ y ∈ l, f y = g y) → l.any f = l.any g
  | [], _ => rfl
  | y :: ys, h => by
    simp only [List.any_cons, h y (List.mem_cons_self ..),
      any_congr' f g ys (fun z hz => h z (List.mem_cons_of_mem _ hz))]

section
variable (dec : UInt64 → Term) (ok : UInt64 → Prop)

theorem pairsOk_append {l1 l2 : IdPairs} (h1 : PairsOk ok l1) (h2 : PairsOk ok l2) :
    PairsOk ok (l1 ++ l2) := by
  intro pr hm
  rcases List.mem_append.mp hm with h | h
  · exact h1 pr h
  · exact h2 pr h

theorem pairsOk_sub {l1 l2 : IdPairs} (hs : ∀ x ∈ l1, x ∈ l2) (h2 : PairsOk ok l2) :
    PairsOk ok l1 := fun pr hm => h2 pr (hs pr hm)

theorem idDedup_mem : ∀ {l : IdPairs} {x}, x ∈ idDedup l → x ∈ l
  | [], _, h => by simp [idDedup] at h
  | y :: ys, x, h => by
    unfold idDedup at h
    split at h
    · exact List.mem_cons_of_mem _ (idDedup_mem h)
    · rcases List.mem_cons.mp h with h | h
      · exact h ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (idDedup_mem h)

theorem pairEq_decode (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (x y : UInt64 × UInt64) (hx : ok x.1 ∧ ok x.2) (hy : ok y.1 ∧ ok y.2) :
    pathPairEq (decPair dec x) (decPair dec y) = idPairEq x y := by
  simp only [pathPairEq, decPair, idPairEq, hdec _ _ hx.1 hy.1, hdec _ _ hx.2 hy.2]

theorem dedup_decode (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) :
    ∀ (l : IdPairs), PairsOk ok l →
    (idDedup l).map (decPair dec) = dedupPath (l.map (decPair dec))
  | [], _ => rfl
  | x :: xs, h => by
    have hx := h x (List.mem_cons_self ..)
    have hxs : PairsOk ok xs := fun pr hm => h pr (List.mem_cons_of_mem _ hm)
    have hany : (xs.map (decPair dec)).any (pathPairEq (decPair dec x)) = xs.any (idPairEq x) := by
      rw [List.any_map]
      exact any_congr' _ _ xs fun y hy => pairEq_decode dec ok hdec x y hx (hxs y hy)
    simp only [idDedup, List.map_cons, dedupPath, hany]
    split
    · exact dedup_decode hdec xs hxs
    · simp [dedup_decode hdec xs hxs]

theorem graph_ok (pid : WfIri → Option UInt64) :
    ∀ (G : List IdTriple) (g : Graph), GraphDecodes dec ok pid G g → ∀ x ∈ G, ok x.1 ∧ ok x.2.2
  | [], _, _, x, hx => by simp at hx
  | _ :: _, [], h, _, _ => by simp [GraphDecodes] at h
  | y :: ys, _ :: ts, h, x, hx => by
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨h.1.2.2.1, h.1.2.2.2.1⟩
    · exact graph_ok pid ys ts h.2 x hx

theorem graph_filterMap (pid : WfIri → Option UInt64) (f : IdTriple → Option (UInt64 × UInt64))
    (f' : Triple → Option (Term × Term))
    (hf : ∀ x t, TripleDecodes dec ok pid x t → (f x).map (decPair dec) = f' t) :
    ∀ (G : List IdTriple) (g : Graph), GraphDecodes dec ok pid G g →
      (G.filterMap f).map (decPair dec) = g.filterMap f'
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [GraphDecodes] at h
  | _ :: _, [], h => by simp [GraphDecodes] at h
  | x :: xs, t :: ts, h => by
    have ih := graph_filterMap pid f f' hf xs ts h.2
    have hx := hf x t h.1
    simp only [List.filterMap_cons]
    cases hfx : f x with
    | none =>
      rw [hfx] at hx
      simp only [Option.map_none] at hx
      rw [← hx]
      exact ih
    | some pr =>
      rw [hfx] at hx
      simp only [Option.map_some] at hx
      rw [← hx, List.map_cons, ih]

theorem graph_map_s (pid : WfIri → Option UInt64) :
    ∀ (G : List IdTriple) (g : Graph), GraphDecodes dec ok pid G g →
      (G.map (·.1)).map dec = g.map (fun t => t.s.toTerm)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [GraphDecodes] at h
  | _ :: _, [], h => by simp [GraphDecodes] at h
  | x :: xs, t :: ts, h => by
    simp only [List.map_cons, h.1.1, graph_map_s pid xs ts h.2]

theorem graph_map_o (pid : WfIri → Option UInt64) :
    ∀ (G : List IdTriple) (g : Graph), GraphDecodes dec ok pid G g →
      (G.map (·.2.2)).map dec = g.map (fun t => t.o)
  | [], [], _ => rfl
  | [], _ :: _, h => by simp [GraphDecodes] at h
  | _ :: _, [], h => by simp [GraphDecodes] at h
  | x :: xs, t :: ts, h => by
    simp only [List.map_cons, h.1.2.1, graph_map_o pid xs ts h.2]

theorem nodes_ok' (G : List IdTriple) (hG : ∀ x ∈ G, ok x.1 ∧ ok x.2.2) :
    ∀ n ∈ idGraphNodes G, ok n := by
  intro n hn
  unfold idGraphNodes at hn
  rcases List.mem_map.mp hn with ⟨pr, hpr, rfl⟩
  have hm := idDedup_mem hpr
  rcases List.mem_map.mp hm with ⟨k, hk, rfl⟩
  rcases List.mem_append.mp hk with hk | hk
  · rcases List.mem_map.mp hk with ⟨x, hx, rfl⟩
    exact (hG x hx).1
  · rcases List.mem_map.mp hk with ⟨x, hx, rfl⟩
    exact (hG x hx).2

theorem nodes_ok (pid : WfIri → Option UInt64) (G : List IdTriple) (g : Graph)
    (hG : GraphDecodes dec ok pid G g) : ∀ n ∈ idGraphNodes G, ok n :=
  nodes_ok' ok G (graph_ok dec ok pid G g hG)

theorem nodes_decode (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (pid : WfIri → Option UInt64) (G : List IdTriple) (g : Graph)
    (hG : GraphDecodes dec ok pid G g) :
    (idGraphNodes G).map dec = graphNodes g := by
  have hL : PairsOk ok ((G.map (·.1) ++ G.map (·.2.2)).map (fun n => (n, n))) := by
    intro pr hpr
    rcases List.mem_map.mp hpr with ⟨k, hk, rfl⟩
    rcases List.mem_append.mp hk with hk | hk
    · rcases List.mem_map.mp hk with ⟨x, hx, rfl⟩
      have := (graph_ok dec ok pid G g hG x hx).1
      exact ⟨this, this⟩
    · rcases List.mem_map.mp hk with ⟨x, hx, rfl⟩
      have := (graph_ok dec ok pid G g hG x hx).2
      exact ⟨this, this⟩
  unfold idGraphNodes graphNodes
  have hfst : ∀ l : IdPairs, (l.map Prod.fst).map dec = (l.map (decPair dec)).map Prod.fst := by
    intro l; simp [List.map_map, Function.comp_def, decPair]
  rw [hfst, dedup_decode dec ok hdec _ hL]
  have e : ((G.map (·.1) ++ G.map (·.2.2)).map (fun n => (n, n))).map (decPair dec) =
      (g.map (fun t => t.s.toTerm) ++ g.map (fun t => t.o)).map (fun n => (n, n)) := by
    rw [← graph_map_s dec ok pid G g hG, ← graph_map_o dec ok pid G g hG]
    simp [List.map_map, Function.comp_def, decPair]
  rw [e]

/-! ### Closures -/

theorem extend_ok (step cur : IdPairs) (hs : PairsOk ok step) (hc : PairsOk ok cur) :
    PairsOk ok (idExtend step cur) := by
  intro pr hpr
  have hm := idDedup_mem hpr
  rcases List.mem_append.mp hm with h | h
  · exact hc pr h
  · rcases List.mem_flatMap.mp h with ⟨p1, h1, h2⟩
    rcases List.mem_filterMap.mp h2 with ⟨p2, h3, h4⟩
    split at h4
    · cases h4
      exact ⟨(hc p1 h1).1, (hs p2 h3).2⟩
    · cases h4

theorem extend_decode (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (step cur : IdPairs) (hs : PairsOk ok step) (hc : PairsOk ok cur) :
    (idExtend step cur).map (decPair dec) = pathExtend (step.map (decPair dec)) (cur.map (decPair dec)) := by
  have hnew : (cur.flatMap (fun p1 =>
      step.filterMap (fun p2 => if p1.2 == p2.1 then some (p1.1, p2.2) else none))).map (decPair dec) =
      (cur.map (decPair dec)).flatMap (fun p1 => (step.map (decPair dec)).filterMap
        (fun p2 => if p1.2.eqb p2.1 then some (p1.1, p2.2) else none)) := by
    rw [List.map_flatMap, List.flatMap_map]
    apply L4Factoidal.Qlvr.flatMap_congr'
    intro p1 h1
    rw [List.filterMap_map, List.map_filterMap]
    apply filterMap_congr'
    intro p2 h2
    have e := hdec _ _ (hc p1 h1).2 (hs p2 h2).1
    simp only [Function.comp_def, decPair, e]
    split <;> simp_all [decPair]
  have hall : PairsOk ok (cur ++ cur.flatMap (fun p1 =>
      step.filterMap (fun p2 => if p1.2 == p2.1 then some (p1.1, p2.2) else none))) := by
    intro pr hpr
    rcases List.mem_append.mp hpr with h | h
    · exact hc pr h
    · rcases List.mem_flatMap.mp h with ⟨p1, h1, h2⟩
      rcases List.mem_filterMap.mp h2 with ⟨p2, h3, h4⟩
      split at h4
      · cases h4
        exact ⟨(hc p1 h1).1, (hs p2 h3).2⟩
      · cases h4
  unfold idExtend pathExtend
  rw [dedup_decode dec ok hdec _ hall, List.map_append, hnew]

theorem fixpoint_ok (step : IdPairs) (hs : PairsOk ok step) :
    ∀ (n : Nat) (cur : IdPairs), PairsOk ok cur → PairsOk ok (idFixpoint step cur n)
  | 0, _, hc => hc
  | n + 1, cur, hc => by
    unfold idFixpoint
    dsimp only
    split
    · exact hc
    · exact fixpoint_ok step hs n _ (extend_ok ok step cur hs hc)

theorem fixpoint_decode (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (step : IdPairs) (hs : PairsOk ok step) :
    ∀ (n : Nat) (cur : IdPairs), PairsOk ok cur →
      (idFixpoint step cur n).map (decPair dec) =
        pathFixpoint (step.map (decPair dec)) (cur.map (decPair dec)) n
  | 0, _, _ => rfl
  | n + 1, cur, hc => by
    simp only [idFixpoint, pathFixpoint]
    rw [← extend_decode dec ok hdec step cur hs hc, List.length_map, List.length_map]
    split
    · rfl
    · exact fixpoint_decode hdec step hs n _ (extend_ok ok step cur hs hc)

/-! ### The path relation -/

theorem eval_ok' (pid : WfIri → Option UInt64) (notLit : UInt64 → Bool) (G : List IdTriple)
    (hG : ∀ x ∈ G, ok x.1 ∧ ok x.2.2) : ∀ p, PairsOk ok (idEvalPath pid notLit p G)
  | .iri i => by
    intro pr hpr
    rcases List.mem_filterMap.mp hpr with ⟨x, hx, h⟩
    split at h
    · cases h; exact hG x hx
    · cases h
  | .inverse p => by
    intro pr hpr
    rcases List.mem_filterMap.mp hpr with ⟨q, hq, h⟩
    split at h
    · cases h; exact ⟨(eval_ok' pid notLit G hG p q hq).2, (eval_ok' pid notLit G hG p q hq).1⟩
    · cases h
  | .sequence p1 p2 => by
    intro pr hpr
    rcases List.mem_flatMap.mp hpr with ⟨a, ha, h⟩
    rcases List.mem_filterMap.mp h with ⟨b, hb, h⟩
    split at h
    · cases h; exact ⟨(eval_ok' pid notLit G hG p1 a ha).1, (eval_ok' pid notLit G hG p2 b hb).2⟩
    · cases h
  | .alternative p1 p2 => pairsOk_append ok (eval_ok' pid notLit G hG p1) (eval_ok' pid notLit G hG p2)
  | .zeroOrOne p => by
    have hn := nodes_ok' ok G hG
    apply pairsOk_sub ok (fun x hx => idDedup_mem hx)
    apply pairsOk_append ok
    · intro pr hpr
      rcases List.mem_map.mp hpr with ⟨n, hm, rfl⟩
      exact ⟨hn n hm, hn n hm⟩
    · exact eval_ok' pid notLit G hG p
  | .zeroOrMore p => by
    have hn := nodes_ok' ok G hG
    have hs := eval_ok' pid notLit G hG p
    apply fixpoint_ok ok _ hs
    apply pairsOk_sub ok (fun x hx => idDedup_mem hx)
    apply pairsOk_append ok _ hs
    intro pr hpr
    rcases List.mem_map.mp hpr with ⟨n, hm, rfl⟩
    exact ⟨hn n hm, hn n hm⟩
  | .oneOrMore p => by
    have hs := eval_ok' pid notLit G hG p
    exact fixpoint_ok ok _ hs _ _ (pairsOk_sub ok (fun x hx => idDedup_mem hx) hs)
  | .negatedSet ps => by
    apply pairsOk_append ok
    · split
      · intro pr hpr; simp at hpr
      · intro pr hpr
        rcases List.mem_filterMap.mp hpr with ⟨x, hx, h⟩
        split at h
        · cases h
        · cases h; exact hG x hx
    · split
      · intro pr hpr; simp at hpr
      · intro pr hpr
        rcases List.mem_filterMap.mp hpr with ⟨x, hx, h⟩
        split at h
        · cases h
        · cases h; exact ⟨(hG x hx).2, (hG x hx).1⟩

theorem eval_ok (pid : WfIri → Option UInt64) (notLit : UInt64 → Bool) (G : List IdTriple) (g : Graph)
    (hG : GraphDecodes dec ok pid G g) : ∀ p, PairsOk ok (idEvalPath pid notLit p G) :=
  eval_ok' ok pid notLit G (graph_ok dec ok pid G g hG)

theorem iriInList_decode (pid : WfIri → Option UInt64) (x : IdTriple) (t : Triple)
    (h : TripleDecodes dec ok pid x t) (ex : List WfIri) :
    iriInList t.p ex = ex.any (fun j => pid j == some x.2.1) := by
  unfold iriInList
  apply any_congr'
  intro j _
  rw [← h.2.2.2.2 j, Bool.eq_iff_iff]
  simp only [beq_iff_eq]
  exact ⟨Eq.symm, Eq.symm⟩

/-- Decoding the pair relation of a path over ids gives the reference
    evaluator's `evalPath` (SPARQL 1.1 sections 9 and 18.4), list for list. -/
theorem evalPath_decode (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (pid : WfIri → Option UInt64) (notLit : UInt64 → Bool)
    (hlit : ∀ x, ok x → notLit x = isNotLiteral (dec x))
    (G : List IdTriple) (g : Graph) (hG : GraphDecodes dec ok pid G g) :
    ∀ p, (idEvalPath pid notLit p G).map (decPair dec) = evalPath p g
  | .iri i => by
    simp only [idEvalPath, evalPath]
    apply graph_filterMap dec ok pid _ _ _ G g hG
    intro x t h
    rw [h.2.2.2.2 i]
    split
    · simp [decPair, h.1, h.2.1]
    · rfl
  | .inverse p => by
    simp only [idEvalPath, evalPath]
    rw [← evalPath_decode hdec pid notLit hlit G g hG p, List.filterMap_map, List.map_filterMap]
    apply filterMap_congr'
    intro pr hpr
    have e := hlit _ (eval_ok dec ok pid notLit G g hG p pr hpr).2
    simp only [Function.comp_def, decPair, e]
    split <;> simp_all [decPair]
  | .sequence p1 p2 => by
    simp only [idEvalPath, evalPath]
    rw [← evalPath_decode hdec pid notLit hlit G g hG p1, ← evalPath_decode hdec pid notLit hlit G g hG p2,
      List.map_flatMap, List.flatMap_map]
    apply L4Factoidal.Qlvr.flatMap_congr'
    intro a ha
    rw [List.filterMap_map, List.map_filterMap]
    apply filterMap_congr'
    intro b hb
    have e := hdec _ _ (eval_ok dec ok pid notLit G g hG p1 a ha).2 (eval_ok dec ok pid notLit G g hG p2 b hb).1
    simp only [Function.comp_def, decPair, e]
    split <;> simp_all [decPair]
  | .alternative p1 p2 => by
    simp only [idEvalPath, evalPath, List.map_append, evalPath_decode hdec pid notLit hlit G g hG p1,
      evalPath_decode hdec pid notLit hlit G g hG p2]
  | .zeroOrOne p => by
    have hn := nodes_ok dec ok pid G g hG
    have hall : PairsOk ok ((idGraphNodes G).map (fun n => (n, n)) ++ idEvalPath pid notLit p G) := by
      apply pairsOk_append ok _ (eval_ok dec ok pid notLit G g hG p)
      intro pr hpr
      rcases List.mem_map.mp hpr with ⟨n, hm, rfl⟩
      exact ⟨hn n hm, hn n hm⟩
    simp only [idEvalPath, evalPath]
    rw [dedup_decode dec ok hdec _ hall, List.map_append, evalPath_decode hdec pid notLit hlit G g hG p,
      ← nodes_decode dec ok hdec pid G g hG]
    simp [List.map_map, Function.comp_def, decPair]
  | .zeroOrMore p => by
    have hn := nodes_ok dec ok pid G g hG
    have hs := eval_ok dec ok pid notLit G g hG p
    have hall : PairsOk ok ((idGraphNodes G).map (fun n => (n, n)) ++ idEvalPath pid notLit p G) := by
      apply pairsOk_append ok _ hs
      intro pr hpr
      rcases List.mem_map.mp hpr with ⟨n, hm, rfl⟩
      exact ⟨hn n hm, hn n hm⟩
    have hseed : PairsOk ok (idDedup ((idGraphNodes G).map (fun n => (n, n)) ++ idEvalPath pid notLit p G)) :=
      pairsOk_sub ok (fun x hx => idDedup_mem hx) hall
    simp only [idEvalPath, evalPath]
    rw [fixpoint_decode dec ok hdec _ hs _ _ hseed, dedup_decode dec ok hdec _ hall, List.map_append,
      evalPath_decode hdec pid notLit hlit G g hG p, ← nodes_decode dec ok hdec pid G g hG, List.length_map]
    simp [List.map_map, Function.comp_def, decPair]
  | .oneOrMore p => by
    have hs := eval_ok dec ok pid notLit G g hG p
    have hseed : PairsOk ok (idDedup (idEvalPath pid notLit p G)) :=
      pairsOk_sub ok (fun x hx => idDedup_mem hx) hs
    simp only [idEvalPath, evalPath]
    rw [fixpoint_decode dec ok hdec _ hs _ _ hseed, dedup_decode dec ok hdec _ hs,
      evalPath_decode hdec pid notLit hlit G g hG p,
      ← nodes_decode dec ok hdec pid G g hG, List.length_map]
  | .negatedSet ps => by
    simp only [idEvalPath, evalPath, List.map_append]
    congr 1
    · split
      · rfl
      · apply graph_filterMap dec ok pid _ _ _ G g hG
        intro x t h
        rw [iriInList_decode dec ok pid x t h]
        split
        · rfl
        · simp [decPair, h.1, h.2.1]
    · split
      · rfl
      · apply graph_filterMap dec ok pid _ _ _ G g hG
        intro x t h
        rw [iriInList_decode dec ok pid x t h]
        split
        · rfl
        · simp [decPair, h.1, h.2.1]

/-! ### The rows of a path pattern -/

/-- A path endpoint over ids: a variable or the id of a constant. -/
inductive End where
  | var (v : String)
  | const (x : UInt64)

/-- The subject endpoint decodes to the pattern's subject. -/
def SubjDecodes : End → PatternSubject → Prop
  | .var v, .var w => v = w
  | .const x, .iri i => ok x ∧ dec x = .iri i
  | .const x, .bnode b => ok x ∧ dec x = .bnode b
  | _, _ => False

/-- The object endpoint decodes to the pattern's object. -/
def ObjDecodes : End → PatternTerm → Prop
  | .var v, .var w => v = w
  | .const x, .iri i => ok x ∧ dec x = .iri i
  | .const x, .bnode b => ok x ∧ dec x = .bnode b
  | .const x, .literal l => ok x ∧ dec x = .literal l
  | _, _ => False

/-- Whether a path admits the zero-length match: the paths
    `addConstantReflexivity` acts on (`IdQuery.isZeroLen`). -/
def pathZeroLen : PropertyPath → Bool
  | .zeroOrMore _ | .zeroOrOne _ => true
  | _ => false

/-- The test `IdQuery.pathTableM` reads (`RPath.zeroLen`) is this one. -/
theorem isZeroLen_eq : IdQuery.isZeroLen = pathZeroLen := by
  funext p
  cases p <;> rfl

/-- The ids of the constant endpoints, subject first. -/
def idConsts (s o : End) : List UInt64 :=
  (match s with | .const x => [x] | .var _ => []) ++ (match o with | .const x => [x] | .var _ => [])

/-- `addConstantReflexivity` on ids: for a zero-length path, the reflexive
    pair of each constant (once per occurrence in `consts`) that `pairs`
    lacks, appended. -/
def idConstRefl (zero : Bool) (consts : List UInt64) (pairs : IdPairs) : IdPairs :=
  if zero then
    pairs ++ (consts.filter fun c => !pairs.any (fun pr => pr.1 == c && pr.2 == c)).map (fun c => (c, c))
  else pairs

/-- `pathResultToSolutions` for one pair, on ids. -/
def idPathRow (s o : End) (pr : UInt64 × UInt64) : Option IdRow :=
  let muS : Option IdRow := match s with
    | .var v => some [(v, pr.1)]
    | .const c => if c == pr.1 then some [] else none
  match muS with
  | none => none
  | some bs =>
    match o with
    | .var w =>
      match OptJoin.idLookup w bs with
      | some x => if x == pr.2 then some bs else none
      | none => some ((w, pr.2) :: bs)
    | .const c => if c == pr.2 then some bs else none

/-- The rows of a path pattern on ids. -/
def idPathRows (s o : End) (pairs : IdPairs) : List IdRow := pairs.filterMap (idPathRow s o)

theorem consts_decode (s o : End) (ps : PatternSubject) (pt : PatternTerm)
    (hs : SubjDecodes dec ok s ps) (ho : ObjDecodes dec ok o pt) :
    (idConsts s o).map dec = pathPatternConstants ps pt ∧ ∀ c ∈ idConsts s o, ok c := by
  constructor
  · unfold idConsts pathPatternConstants
    rw [List.map_append]
    congr 1
    · match s, ps, hs with
      | .var _, .var _, _ => rfl
      | .const _, .iri _, h => simp [h.2]
      | .const _, .bnode _, h => simp [h.2]
    · match o, pt, ho with
      | .var _, .var _, _ => rfl
      | .const _, .iri _, h => simp [h.2]
      | .const _, .bnode _, h => simp [h.2]
      | .const _, .literal _, h => simp [h.2]
  · intro c hc
    unfold idConsts at hc
    rcases List.mem_append.mp hc with hc | hc
    · match s, ps, hs with
      | .var _, .var _, _ => simp at hc
      | .const _, .iri _, h => simp at hc; exact hc ▸ h.1
      | .const _, .bnode _, h => simp at hc; exact hc ▸ h.1
    · match o, pt, ho with
      | .var _, .var _, _ => simp at hc
      | .const _, .iri _, h => simp at hc; exact hc ▸ h.1
      | .const _, .bnode _, h => simp at hc; exact hc ▸ h.1
      | .const _, .literal _, h => simp at hc; exact hc ▸ h.1

theorem constRefl_ok (zero : Bool) (consts : List UInt64) (pairs : IdPairs) (hc : ∀ c ∈ consts, ok c)
    (hp : PairsOk ok pairs) : PairsOk ok (idConstRefl zero consts pairs) := by
  unfold idConstRefl
  split
  · apply pairsOk_append ok hp
    intro pr hpr
    rcases List.mem_map.mp hpr with ⟨c, hm, rfl⟩
    have := hc c (List.mem_filter.mp hm).1
    exact ⟨this, this⟩
  · exact hp

theorem constRefl_decode (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (s o : End) (ps : PatternSubject) (pt : PatternTerm)
    (hs : SubjDecodes dec ok s ps) (ho : ObjDecodes dec ok o pt) (path : PropertyPath)
    (pairs : IdPairs) (hp : PairsOk ok pairs) :
    (idConstRefl (pathZeroLen path) (idConsts s o) pairs).map (decPair dec) =
      addConstantReflexivity ps pt path (pairs.map (decPair dec)) := by
  obtain ⟨hcd, hcok⟩ := consts_decode dec ok s o ps pt hs ho
  have key : (((idConsts s o).filter fun c => !pairs.any (fun pr => pr.1 == c && pr.2 == c)).map
      (fun c => (c, c))).map (decPair dec) =
      ((pathPatternConstants ps pt).filter (fun t =>
        !(pairs.map (decPair dec)).any (fun pr => pr.1.eqb t && pr.2.eqb t))).map (fun n => (n, n)) := by
    rw [← hcd, List.filter_map, List.map_map, List.map_map]
    have hf : (idConsts s o).filter (fun c => !pairs.any (fun pr => pr.1 == c && pr.2 == c)) =
        (idConsts s o).filter ((fun t => !(pairs.map (decPair dec)).any
          (fun pr => pr.1.eqb t && pr.2.eqb t)) ∘ dec) := by
      apply List.filter_congr
      intro c hc
      simp only [Function.comp_def, List.any_map]
      congr 1
      apply any_congr'
      intro pr hpr
      simp only [decPair, hdec _ _ (hp pr hpr).1 (hcok c hc), hdec _ _ (hp pr hpr).2 (hcok c hc)]
    rw [hf]
    simp [Function.comp_def, decPair]
  cases path <;> simp only [pathZeroLen, idConstRefl, addConstantReflexivity, ite_true, ite_false,
    Bool.false_eq_true, List.map_append, key]

theorem rows_decode (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (s o : End) (ps : PatternSubject) (pt : PatternTerm)
    (hs : SubjDecodes dec ok s ps) (ho : ObjDecodes dec ok o pt)
    (pairs : IdPairs) (hp : PairsOk ok pairs) :
    (idPathRows s o pairs).map (decRow dec) = pathResultToSolutions ps pt (pairs.map (decPair dec)) := by
  unfold idPathRows pathResultToSolutions
  rw [List.map_filterMap, List.filterMap_map]
  apply filterMap_congr'
  intro pr hpr
  have h1 := (hp pr hpr).1
  have h2 := (hp pr hpr).2
  simp only [Function.comp_def, decPair]
  match s, ps, hs with
  | .var v, .var _, rfl =>
    match o, pt, ho with
    | .var w, .var _, rfl =>
      by_cases hvw : v = w
      · subst hvw
        simp [idPathRow, OptJoin.idLookup, Binding.lookup, hdec _ _ h1 h2]
        split <;> simp [decRow]
      · simp [idPathRow, OptJoin.idLookup, Binding.lookup, hvw, decRow]
    | .const c, .iri i, ⟨hc, hd⟩ =>
      simp only [idPathRow, ← hd, hdec _ _ hc h2]
      split <;> simp [decRow]
    | .const c, .bnode b, ⟨hc, hd⟩ =>
      simp only [idPathRow, ← hd, hdec _ _ hc h2]
      split <;> simp [decRow]
    | .const c, .literal l, ⟨hc, hd⟩ =>
      simp only [idPathRow, ← hd, hdec _ _ hc h2]
      split <;> simp [decRow]
  | .const c, .iri i, ⟨hc, hd⟩ =>
    simp only [idPathRow, ← hd, hdec _ _ hc h1]
    by_cases hc1 : (c == pr.1) = true
    · simp only [hc1, if_true]
      match o, pt, ho with
      | .var w, .var _, rfl => simp [OptJoin.idLookup, Binding.lookup, decRow]
      | .const d, .iri j, ⟨hd', hdd⟩ =>
        simp only [← hdd, hdec _ _ hd' h2]; split <;> simp [decRow]
      | .const d, .bnode j, ⟨hd', hdd⟩ =>
        simp only [← hdd, hdec _ _ hd' h2]; split <;> simp [decRow]
      | .const d, .literal j, ⟨hd', hdd⟩ =>
        simp only [← hdd, hdec _ _ hd' h2]; split <;> simp [decRow]
    · simp [hc1]
  | .const c, .bnode b, ⟨hc, hd⟩ =>
    simp only [idPathRow, ← hd, hdec _ _ hc h1]
    by_cases hc1 : (c == pr.1) = true
    · simp only [hc1, if_true]
      match o, pt, ho with
      | .var w, .var _, rfl => simp [OptJoin.idLookup, Binding.lookup, decRow]
      | .const d, .iri j, ⟨hd', hdd⟩ =>
        simp only [← hdd, hdec _ _ hd' h2]; split <;> simp [decRow]
      | .const d, .bnode j, ⟨hd', hdd⟩ =>
        simp only [← hdd, hdec _ _ hd' h2]; split <;> simp [decRow]
      | .const d, .literal j, ⟨hd', hdd⟩ =>
        simp only [← hdd, hdec _ _ hd' h2]; split <;> simp [decRow]
    · simp [hc1]

/-- Decoding the rows of a path pattern on ids (the pairs, the reflexive
    pairs of the constant endpoints of `p*` and `p?`, one row per accepted
    pair) gives the reference's solutions of the pattern
    (`pathResultToSolutions` after `addConstantReflexivity`, the arm
    `GraphPattern.evalIn` evaluates for `.propertyPath`), row for row. -/
theorem pathRows_decode (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (s o : End) (ps : PatternSubject) (pt : PatternTerm)
    (hs : SubjDecodes dec ok s ps) (ho : ObjDecodes dec ok o pt) (path : PropertyPath)
    (pairs : IdPairs) (hp : PairsOk ok pairs) :
    (idPathRows s o (idConstRefl (pathZeroLen path) (idConsts s o) pairs)).map (decRow dec) =
      pathResultToSolutions ps pt (addConstantReflexivity ps pt path (pairs.map (decPair dec))) := by
  have hc := (consts_decode dec ok s o ps pt hs ho).2
  rw [rows_decode dec ok hdec s o ps pt hs ho _ (constRefl_ok ok _ _ pairs hc hp),
    constRefl_decode dec ok hdec s o ps pt hs ho path pairs hp]

/-- The solutions of a property path pattern over a graph (the arm of
    `GraphPattern.evalIn` for `.propertyPath`): decoding the rows of the
    pattern over the id graph gives them. -/
theorem pathPattern_decode (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (pid : WfIri → Option UInt64) (notLit : UInt64 → Bool)
    (hlit : ∀ x, ok x → notLit x = isNotLiteral (dec x))
    (G : List IdTriple) (g : Graph) (hG : GraphDecodes dec ok pid G g)
    (s o : End) (ps : PatternSubject) (pt : PatternTerm)
    (hs : SubjDecodes dec ok s ps) (ho : ObjDecodes dec ok o pt) (path : PropertyPath) :
    (idPathRows s o (idConstRefl (pathZeroLen path) (idConsts s o)
        (idEvalPath pid notLit path G))).map (decRow dec) =
      pathResultToSolutions ps pt (addConstantReflexivity ps pt path (evalPath path g)) := by
  rw [pathRows_decode dec ok hdec s o ps pt hs ho path _ (eval_ok dec ok pid notLit G g hG path),
    evalPath_decode dec ok hdec pid notLit hlit G g hG path]

end

end L4Factoidal.Storage.Sbm11.IdPath
