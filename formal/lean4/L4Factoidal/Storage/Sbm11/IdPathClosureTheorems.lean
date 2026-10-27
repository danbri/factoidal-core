/-
L4Factoidal.Storage.Sbm11.IdPathClosureTheorems — the closures `p*` and `p+`
on the SBM11 id path (https://github.com/danbri/factoidal/issues/954, SPARQL
1.1 sections 9.1 and 18.4): what the reference's bounded fixpoint computes,
and that the worklist the id path runs per start node computes the same pairs
within its round bound.

`IdPathTheorems.evalPath_decode` shows that decoding `idEvalPath` gives the
reference's `evalPath` list for list; for a closure, `idEvalPath` is the
reference's own iteration (`pathFixpoint`, mirrored as `idFixpoint`) with the
reference's fuel, the number of nodes of the graph. This file shows what that
iteration computes, on ids (where `==` is equality).

## The reference's fixpoint

`Reach E b c`: `c` is reached from `b` in zero or more steps of the relation
`E`. `InClo S E (a, c)`: some `(a, b)` of `S` with `Reach E b c`.

* `fixpoint_mem`: for a seed `S` with no pair twice and an iteration fuel at
  least the length of a duplicate-free list `N` that holds the object of every
  pair of `S` and of `E`, the pairs of `idFixpoint E S fuel` are exactly
  `InClo S E`. The fuel suffices: per subject `a`, the objects reached grow by
  at least one each round until no new pair appears for `a`, and they stay in
  `N` (`fix_closed`). The early stop of the reference compares lengths; with a
  duplicate-free seed every round is duplicate-free and contains the round
  before, so equal lengths mean no new pair (`extend_len`).
* `fixpoint_nodup`: no pair twice in the result.
* `star_mem`: a pair `(a, c)` is in `idEvalPath (p*) G` if and only if `a` is
  a node of the graph and `Reach (idEvalPath p G) a c`; no pair twice
  (`star_nodup`).
* `plus_mem`: `(a, c)` is in `idEvalPath (p+) G` if and only if some step
  `(a, b)` has `Reach E b c`; no pair twice (`plus_nodup`). No hypothesis on
  the step relation: since https://github.com/danbri/factoidal/issues/955 the
  reference seeds the iteration with the step relation deduplicated
  (`dedupPath step`), so the length test is a fixpoint test also when `eval(p)`
  holds a pair twice. Before that fix the reference compared the deduplicated
  next round with the step list itself, stopped before the fixpoint (W3C pp12
  has such a step relation), and the id path refused those queries.

## The worklist of the id path

`reachModel E a fuel` is the list form of `IdPath.reachPlus (adjOf E) a fuel`:
a worklist that starts with `a`, takes one node per round, and appends each
successor not seen before to the output and to the worklist; `none` when the
rounds run out with work left.

* `reachModel_some`: with `fuel` at least the number of pairs of `E` plus
  two (the bound `IdQuery.closureM` passes), the rounds do not run out: each
  round takes one node, and only the start node and the nodes first seen enter
  the worklist, at most one per pair of `E`.
* `reachModel_mem`: the output holds `c` exactly when `c` is reached from `a`
  in one or more steps, each node once (`reachModel_nodup`).
* `starFrom_mem`, `plusFrom_mem`: the pairs the id path emits for a start
  node `a` (`IdQuery.closureM`: for `p*` `(a, a)` when `a` is a node of the
  graph, then `(a, c)` per node `c` of the output other than `a`; for `p+`
  `(a, c)` per node of the output) are the pairs of the reference's closure
  whose subject is `a`, each once.
* `reach_restrict`: reaching from `a` over a part `E'` of `E` that holds every
  pair of `E` whose subject is reached from `a` is reaching over `E`; the
  rounds of `closureM` collect the pairs of the step relation whose subject is
  reached from the start nodes.

`IdPathPureTheorems.reachPlus_eq` proves that `IdPath.reachPlus` over the
hash map of `adjOf` answers `reachModel`, list for list (the `#guard`s below
compare them on examples).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdPathTheorems

namespace L4Factoidal.Storage.Sbm11.IdPath

open L4Factoidal.RDF
open L4Factoidal.SPARQL

/-! ## Reachability -/

/-- `c` is reached from `b` in zero or more steps of `E`. -/
inductive Reach (E : IdPairs) : UInt64 → UInt64 → Prop where
  | refl (a : UInt64) : Reach E a a
  | tail {a b c : UInt64} : Reach E a b → (b, c) ∈ E → Reach E a c

theorem Reach.head {E : IdPairs} {a b c : UInt64} (h : (a, b) ∈ E) (r : Reach E b c) : Reach E a c := by
  induction r with
  | refl => exact .tail (.refl a) h
  | tail _ h2 ih => exact .tail ih h2

theorem Reach.trans {E : IdPairs} {a b c : UInt64} (r1 : Reach E a b) (r2 : Reach E b c) : Reach E a c := by
  induction r2 with
  | refl => exact r1
  | tail _ h ih => exact .tail ih h

/-- The pairs `(a, c)` with `(a, b)` in `S` and `c` reached from `b`. -/
def InClo (S E : IdPairs) (x : UInt64 × UInt64) : Prop := ∃ b, (x.1, b) ∈ S ∧ Reach E b x.2

/-! ## Deduplication on ids -/

theorem idPairEq_iff (x y : UInt64 × UInt64) : idPairEq x y = true ↔ x = y := by
  unfold idPairEq
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · rintro ⟨h1, h2⟩; exact Prod.ext h1 h2
  · rintro rfl; exact ⟨rfl, rfl⟩

theorem mem_idDedup : ∀ {l : IdPairs} {x}, x ∈ idDedup l ↔ x ∈ l
  | [], _ => by simp [idDedup]
  | y :: ys, x => by
    unfold idDedup
    split
    · rename_i h
      rw [mem_idDedup]
      constructor
      · exact List.mem_cons_of_mem _
      · intro hx
        rcases List.mem_cons.mp hx with rfl | hx
        · rcases List.any_eq_true.mp h with ⟨z, hz, he⟩
          exact ((idPairEq_iff _ _).mp he) ▸ hz
        · exact hx
    · simp only [List.mem_cons, mem_idDedup]

theorem nodup_idDedup : ∀ (l : IdPairs), (idDedup l).Nodup
  | [] => by simp [idDedup]
  | y :: ys => by
    unfold idDedup
    split
    · exact nodup_idDedup ys
    · rename_i h
      refine List.nodup_cons.mpr ⟨?_, nodup_idDedup ys⟩
      intro hy
      apply h
      exact List.any_eq_true.mpr ⟨y, mem_idDedup.mp hy, (idPairEq_iff _ _).mpr rfl⟩

/-! ## One round -/

theorem mem_extend (E l : IdPairs) (x : UInt64 × UInt64) :
    x ∈ idExtend E l ↔ x ∈ l ∨ ∃ b, (x.1, b) ∈ l ∧ (b, x.2) ∈ E := by
  unfold idExtend
  simp only [mem_idDedup, List.mem_append, List.mem_flatMap, List.mem_filterMap]
  constructor
  · rintro (h | ⟨p1, h1, p2, h2, h3⟩)
    · exact Or.inl h
    · split at h3
      · rename_i he
        cases h3
        refine Or.inr ⟨p1.2, h1, ?_⟩
        rw [beq_iff_eq] at he
        rw [he]
        exact h2
      · cases h3
  · rintro (h | ⟨b, h1, h2⟩)
    · exact Or.inl h
    · refine Or.inr ⟨(x.1, b), h1, (b, x.2), h2, ?_⟩
      simp

theorem extend_nodup (E l : IdPairs) : (idExtend E l).Nodup := nodup_idDedup _

theorem sub_extend (E l : IdPairs) : ∀ x ∈ l, x ∈ idExtend E l :=
  fun x h => (mem_extend E l x).mpr (Or.inl h)

/-- A round that adds nothing has the length of its input; any other round
    with a duplicate-free input is longer. -/
theorem extend_len (E l : IdPairs) (hl : l.Nodup) (x : UInt64 × UInt64)
    (hx : x ∈ idExtend E l) (hn : x ∉ l) : l.length + 1 ≤ (idExtend E l).length := by
  have h := List.Nodup.length_le_of_subset (l₁ := x :: l) (l₂ := idExtend E l)
    (List.nodup_cons.mpr ⟨hn, hl⟩) (by
      intro y hy
      rcases List.mem_cons.mp hy with rfl | hy
      · exact hx
      · exact sub_extend E l y hy)
  simpa using h

/-! ## The objects reached per subject -/

/-- The objects of the pairs of `l` whose subject is `a`. -/
def objs (l : IdPairs) (a : UInt64) : List UInt64 := (l.filter (fun p => p.1 == a)).map (·.2)

theorem mem_objs (l : IdPairs) (a c : UInt64) : c ∈ objs l a ↔ (a, c) ∈ l := by
  unfold objs
  simp only [List.mem_map, List.mem_filter, beq_iff_eq]
  constructor
  · rintro ⟨p, ⟨hp, rfl⟩, rfl⟩; exact hp
  · intro h; exact ⟨(a, c), ⟨h, rfl⟩, rfl⟩

theorem objs_nodup : ∀ (l : IdPairs) (a : UInt64), l.Nodup → (objs l a).Nodup
  | [], _, _ => by simp [objs]
  | p :: ps, a, h => by
    have ⟨hp, hps⟩ := List.nodup_cons.mp h
    have ih := objs_nodup ps a hps
    unfold objs at ih ⊢
    by_cases hpa : p.1 = a
    · rw [List.filter_cons_of_pos (by simp [hpa]), List.map_cons]
      refine List.nodup_cons.mpr ⟨?_, ih⟩
      intro hm
      rcases List.mem_map.mp hm with ⟨q, hq, hq2⟩
      rcases List.mem_filter.mp hq with ⟨hq1, hqa⟩
      rw [beq_iff_eq] at hqa
      apply hp
      have : q = p := Prod.ext (hqa.trans hpa.symm) hq2
      exact this ▸ hq1
    · rw [List.filter_cons_of_neg (by simp [hpa])]
      exact ih

/-- Every pair of `l` whose subject is `a` has its successors in `l`. -/
def Settled (E l : IdPairs) (a : UInt64) : Prop := ∀ b c, (a, b) ∈ l → (b, c) ∈ E → (a, c) ∈ l

theorem settled_extend (E l : IdPairs) (a : UInt64) (h : Settled E l a) : Settled E (idExtend E l) a := by
  have hsub : ∀ c, (a, c) ∈ idExtend E l → (a, c) ∈ l := by
    intro c hc
    rcases (mem_extend E l (a, c)).mp hc with hc | ⟨b, h1, h2⟩
    · exact hc
    · exact h b c h1 h2
  intro b c h1 h2
  exact sub_extend E l _ (h b c (hsub b h1) h2)

/-- The invariant of round `k`: per subject, settled, or at least `k + 1`
    objects. -/
def Inv (E l : IdPairs) (k : Nat) : Prop := ∀ a, Settled E l a ∨ k + 1 ≤ (objs l a).length

theorem inv_zero (E l : IdPairs) : Inv E l 0 := by
  intro a
  cases h : objs l a with
  | nil =>
    left
    intro b c hb _
    have := (mem_objs l a b).mpr hb
    rw [h] at this
    cases this
  | cons x xs => right; simp

theorem inv_step (E l : IdPairs) (hl : l.Nodup) (k : Nat) (h : Inv E l k) : Inv E (idExtend E l) (k + 1) := by
  intro a
  by_cases hs : Settled E l a
  · exact Or.inl (settled_extend E l a hs)
  · right
    rcases h a with h | h
    · exact absurd h hs
    · -- a pair (a, c) not in l, reached in one more step
      have : ∃ b c, (a, b) ∈ l ∧ (b, c) ∈ E ∧ (a, c) ∉ l := by
        apply Classical.byContradiction
        intro hne
        apply hs
        intro b c h1 h2
        apply Classical.byContradiction
        intro h3
        exact hne ⟨b, c, h1, h2, h3⟩
      rcases this with ⟨b, c, h1, h2, h3⟩
      have hc : (a, c) ∈ idExtend E l := (mem_extend E l (a, c)).mpr (Or.inr ⟨b, h1, h2⟩)
      have hlen := List.Nodup.length_le_of_subset (l₁ := c :: objs l a) (l₂ := objs (idExtend E l) a)
        (List.nodup_cons.mpr ⟨fun hm => h3 ((mem_objs l a c).mp hm), objs_nodup l a hl⟩) (by
          intro y hy
          rcases List.mem_cons.mp hy with rfl | hy
          · exact (mem_objs _ a _).mpr hc
          · exact (mem_objs _ a y).mpr (sub_extend E l _ ((mem_objs l a y).mp hy)))
      simp only [List.length_cons] at hlen
      omega

/-- Every object of `l` is in `N`. -/
def ObjsIn (l : IdPairs) (N : List UInt64) : Prop := ∀ p ∈ l, p.2 ∈ N

theorem objsIn_extend (E l : IdPairs) (N : List UInt64) (hE : ObjsIn E N) (hl : ObjsIn l N) :
    ObjsIn (idExtend E l) N := by
  intro p hp
  rcases (mem_extend E l p).mp hp with h | ⟨b, _, h2⟩
  · exact hl p h
  · exact hE (b, p.2) h2

theorem objs_len (l : IdPairs) (N : List UInt64) (hl : l.Nodup) (hN : ObjsIn l N) (a : UInt64) :
    (objs l a).length ≤ N.length :=
  List.Nodup.length_le_of_subset (objs_nodup l a hl) (fun c hc => hN (a, c) ((mem_objs l a c).mp hc))

/-- Every pair's successors are in the list. -/
def Closed (E l : IdPairs) : Prop := ∀ a, Settled E l a

/-- The result of the reference's iteration is closed when the fuel and the
    round already done add up to the length of `N`. -/
theorem fix_closed (E : IdPairs) (N : List UInt64) (hE : ObjsIn E N) :
    ∀ (n k : Nat) (l : IdPairs), l.Nodup → ObjsIn l N → Inv E l k → N.length ≤ k + n →
      Closed E (idFixpoint E l n)
  | 0, k, l, hl, hN, hI, hk => by
    intro a
    rcases hI a with h | h
    · exact h
    · have := objs_len l N hl hN a
      omega
  | n + 1, k, l, hl, hN, hI, hk => by
    simp only [idFixpoint]
    split
    · rename_i heq
      rw [beq_iff_eq] at heq
      intro a b c h1 h2
      apply Classical.byContradiction
      intro h3
      have := extend_len E l hl (a, c) ((mem_extend E l (a, c)).mpr (Or.inr ⟨b, h1, h2⟩)) h3
      omega
    · exact fix_closed E N hE n (k + 1) _ (extend_nodup E l) (objsIn_extend E l N hE hN)
        (inv_step E l hl k hI) (by omega)

theorem inClo_extend (E l : IdPairs) (x : UInt64 × UInt64) (h : InClo (idExtend E l) E x) : InClo l E x := by
  rcases h with ⟨b, hb, r⟩
  rcases (mem_extend E l (x.1, b)).mp hb with hb | ⟨b', h1, h2⟩
  · exact ⟨b, hb, r⟩
  · exact ⟨b', h1, Reach.head h2 r⟩

theorem fix_sub (E : IdPairs) :
    ∀ (n : Nat) (l : IdPairs), (∀ x ∈ l, x ∈ idFixpoint E l n) ∧ (∀ x ∈ idFixpoint E l n, InClo l E x)
  | 0, l => ⟨fun _ h => h, fun x h => ⟨x.2, h, .refl _⟩⟩
  | n + 1, l => by
    simp only [idFixpoint]
    split
    · exact ⟨fun _ h => h, fun x h => ⟨x.2, h, .refl _⟩⟩
    · have ih := fix_sub E n (idExtend E l)
      exact ⟨fun x h => ih.1 x (sub_extend E l x h), fun x h => inClo_extend E l x (ih.2 x h)⟩

theorem fixpoint_nodup (E : IdPairs) : ∀ (n : Nat) (l : IdPairs), l.Nodup → (idFixpoint E l n).Nodup
  | 0, _, h => h
  | n + 1, l, h => by
    simp only [idFixpoint]
    split
    · exact h
    · exact fixpoint_nodup E n _ (extend_nodup E l)

/-- What the reference's bounded fixpoint computes: with a seed that holds no
    pair twice and a fuel at least the length of a duplicate-free `N` that
    holds every object of the seed and of the step relation, the pairs of the
    result are those of `InClo S E`. -/
theorem fixpoint_mem (E S : IdPairs) (N : List UInt64) (hE : ObjsIn E N) (hS : S.Nodup)
    (hSN : ObjsIn S N) (n : Nat) (hn : N.length ≤ n) (x : UInt64 × UInt64) :
    x ∈ idFixpoint E S n ↔ InClo S E x := by
  have hc := fix_closed E N hE n 0 S hS hSN (inv_zero E S) (by omega)
  have hs := fix_sub E n S
  constructor
  · exact hs.2 x
  · rintro ⟨b, hb, r⟩
    obtain ⟨a, c⟩ := x
    simp only at hb r
    have : ∀ y, Reach E b y → (a, y) ∈ idFixpoint E S n := by
      intro y ry
      induction ry with
      | refl => exact hs.1 _ hb
      | tail _ h2 ih => exact hc a _ _ ih h2
    exact this c r

/-! ## The closures of `idEvalPath` -/

theorem mem_nodes (G : List IdTriple) (n : UInt64) :
    n ∈ idGraphNodes G ↔ ∃ x ∈ G, n = x.1 ∨ n = x.2.2 := by
  unfold idGraphNodes
  simp only [List.mem_map, mem_idDedup, List.mem_append]
  constructor
  · rintro ⟨pr, ⟨k, hk, rfl⟩, rfl⟩
    rcases hk with ⟨x, hx, rfl⟩ | ⟨x, hx, rfl⟩
    · exact ⟨x, hx, Or.inl rfl⟩
    · exact ⟨x, hx, Or.inr rfl⟩
  · rintro ⟨x, hx, rfl | rfl⟩
    · exact ⟨(x.1, x.1), ⟨x.1, Or.inl ⟨x, hx, rfl⟩, rfl⟩, rfl⟩
    · exact ⟨(x.2.2, x.2.2), ⟨x.2.2, Or.inr ⟨x, hx, rfl⟩, rfl⟩, rfl⟩

theorem nodes_nodup (G : List IdTriple) : (idGraphNodes G).Nodup := by
  unfold idGraphNodes
  have hd := nodup_idDedup ((G.map (·.1) ++ G.map (·.2.2)).map (fun n => (n, n)))
  have hdiag : ∀ p ∈ idDedup ((G.map (·.1) ++ G.map (·.2.2)).map (fun n => (n, n))), p.1 = p.2 := by
    intro p hp
    rcases List.mem_map.mp (mem_idDedup.mp hp) with ⟨k, _, rfl⟩
    rfl
  generalize idDedup ((G.map (·.1) ++ G.map (·.2.2)).map (fun n => (n, n))) = L at hd hdiag
  induction L with
  | nil => simp
  | cons p ps ih =>
    have ⟨hp, hps⟩ := List.nodup_cons.mp hd
    refine List.nodup_cons.mpr ⟨?_, ih hps (fun q hq => hdiag q (List.mem_cons_of_mem _ hq))⟩
    intro hm
    rcases List.mem_map.mp hm with ⟨q, hq, hq1⟩
    apply hp
    have e1 := hdiag p (List.mem_cons_self ..)
    have e2 := hdiag q (List.mem_cons_of_mem _ hq)
    have : q = p := Prod.ext hq1 (by rw [← e2, hq1, e1])
    exact this ▸ hq

/-- Every pair of a path relation is a pair of nodes of the graph. -/
theorem eval_nodes (pid : WfIri → Option UInt64) (G : List IdTriple)
    (p : PropertyPath) : ∀ pr ∈ idEvalPath pid p G,
      pr.1 ∈ idGraphNodes G ∧ pr.2 ∈ idGraphNodes G :=
  eval_ok' (fun n => n ∈ idGraphNodes G) pid G
    (fun x hx => ⟨(mem_nodes G x.1).mpr ⟨x, hx, Or.inl rfl⟩, (mem_nodes G x.2.2).mpr ⟨x, hx, Or.inr rfl⟩⟩) p

/-- `p*` over ids: `(a, c)` exactly when `a` is a node of the graph and `c`
    is reached from `a` in zero or more steps of `p`. -/
theorem star_mem (pid : WfIri → Option UInt64) (G : List IdTriple)
    (p : PropertyPath) (x : UInt64 × UInt64) :
    x ∈ idEvalPath pid (.zeroOrMore p) G ↔
      x.1 ∈ idGraphNodes G ∧ Reach (idEvalPath pid p G) x.1 x.2 := by
  let E := idEvalPath pid p G
  let N := idGraphNodes G
  have hEN := eval_nodes pid G p
  have hE : ObjsIn E N := fun pr h => (hEN pr h).2
  let S := idDedup (N.map (fun n => (n, n)) ++ E)
  have hS : S.Nodup := nodup_idDedup _
  have hSN : ObjsIn S N := by
    intro pr h
    rcases List.mem_append.mp (mem_idDedup.mp h) with h | h
    · rcases List.mem_map.mp h with ⟨n, hn, rfl⟩; exact hn
    · exact hE pr h
  show x ∈ idFixpoint E S N.length ↔ _
  rw [fixpoint_mem E S N hE hS hSN N.length (Nat.le_refl _) x]
  constructor
  · rintro ⟨b, hb, r⟩
    rcases List.mem_append.mp (mem_idDedup.mp hb) with h | h
    · rcases List.mem_map.mp h with ⟨n, hn, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨h1, h2⟩ := he
      subst h2
      exact ⟨h1 ▸ hn, h1 ▸ r⟩
    · exact ⟨(hEN _ h).1, Reach.head h r⟩
  · rintro ⟨hn, r⟩
    exact ⟨x.1, mem_idDedup.mpr (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨x.1, hn, rfl⟩))), r⟩

theorem star_nodup (pid : WfIri → Option UInt64) (G : List IdTriple)
    (p : PropertyPath) : (idEvalPath pid (.zeroOrMore p) G).Nodup :=
  fixpoint_nodup _ _ _ (nodup_idDedup _)

/-- `p+` over ids, when the step relation has no pair twice: `(a, c)` exactly
    when a step `(a, b)` of `p` has `c` reached from `b`. -/
theorem plus_mem (pid : WfIri → Option UInt64) (G : List IdTriple)
    (p : PropertyPath) (x : UInt64 × UInt64) :
    x ∈ idEvalPath pid (.oneOrMore p) G ↔
      ∃ b, (x.1, b) ∈ idEvalPath pid p G ∧ Reach (idEvalPath pid p G) b x.2 := by
  let E := idEvalPath pid p G
  have hE : ObjsIn E (idGraphNodes G) := fun pr h => (eval_nodes pid G p pr h).2
  have hS : ObjsIn (idDedup E) (idGraphNodes G) := fun pr h => hE pr (mem_idDedup.mp h)
  show x ∈ idFixpoint E (idDedup E) (idGraphNodes G).length ↔ _
  rw [fixpoint_mem E (idDedup E) (idGraphNodes G) hE (nodup_idDedup _) hS _ (Nat.le_refl _) x]
  constructor
  · rintro ⟨b, hb, r⟩; exact ⟨b, mem_idDedup.mp hb, r⟩
  · rintro ⟨b, hb, r⟩; exact ⟨b, mem_idDedup.mpr hb, r⟩

theorem plus_nodup (pid : WfIri → Option UInt64) (G : List IdTriple)
    (p : PropertyPath) :
    (idEvalPath pid (.oneOrMore p) G).Nodup :=
  fixpoint_nodup _ _ _ (nodup_idDedup _)

/-! ## The worklist, as a list model of `IdPath.reachPlus` -/

/-- `c` is reached from `a` in one or more steps of `E`. -/
def Reach1 (E : IdPairs) (a c : UInt64) : Prop := ∃ b, (a, b) ∈ E ∧ Reach E b c

theorem reach_cases {E : IdPairs} {a c : UInt64} (r : Reach E a c) : a = c ∨ Reach1 E a c := by
  induction r with
  | refl => exact Or.inl rfl
  | @tail b c' _ h ih =>
    right
    rcases ih with rfl | ⟨b', h1, r1⟩
    · exact ⟨c', h, .refl _⟩
    · exact ⟨b', h1, .tail r1 h⟩

theorem reach1_reach {E : IdPairs} {a c : UInt64} (h : Reach1 E a c) : Reach E a c := by
  rcases h with ⟨b, h1, r⟩
  exact Reach.head h1 r

/-- The successors of `x`, in the order of `E` (`IdPath.adjOf`). -/
def succs (E : IdPairs) (x : UInt64) : List UInt64 :=
  E.filterMap fun p => if p.1 == x then some p.2 else none

theorem mem_succs (E : IdPairs) (x y : UInt64) : y ∈ succs E x ↔ (x, y) ∈ E := by
  unfold succs
  simp only [List.mem_filterMap]
  constructor
  · rintro ⟨p, hp, h⟩
    split at h
    · rename_i he
      cases h
      rw [beq_iff_eq] at he
      rw [← he]
      exact hp
    · cases h
  · intro h
    exact ⟨(x, y), h, by simp⟩

/-- One node taken: each successor not yet in `out` appended to `out` and to
    the worklist. -/
def visit (out work : List UInt64) : List UInt64 → List UInt64 × List UInt64
  | [] => (out, work)
  | y :: ys => if y ∈ out then visit out work ys else visit (out ++ [y]) (work ++ [y]) ys

/-- The worklist loop of `IdPath.reachPlus`, at most `n` rounds. -/
def bfsGo (E : IdPairs) : Nat → List UInt64 → List UInt64 → Option (List UInt64)
  | 0, out, work => if work.isEmpty then some out else none
  | _ + 1, out, [] => some out
  | n + 1, out, x :: work =>
    let r := visit out work (succs E x)
    bfsGo E n r.1 r.2

/-- The list model of `IdPath.reachPlus (adjOf E) a fuel`. -/
def reachModel (E : IdPairs) (a : UInt64) (fuel : Nat) : Option (List UInt64) := bfsGo E fuel [] [a]

theorem visit_spec : ∀ (ys out work : List UInt64), out.Nodup →
    (visit out work ys).1.Nodup ∧ (∀ y ∈ ys, y ∈ (visit out work ys).1) ∧
    (∀ z ∈ (visit out work ys).1, z ∈ out ∨ z ∈ ys) ∧ (∀ z ∈ out, z ∈ (visit out work ys).1) ∧
    (∀ z ∈ work, z ∈ (visit out work ys).2) ∧
    (∀ z ∈ (visit out work ys).2, z ∈ work ∨ z ∈ (visit out work ys).1) ∧
    (∀ z ∈ (visit out work ys).1, z ∉ out → z ∈ (visit out work ys).2) ∧
    (visit out work ys).2.length + out.length = work.length + (visit out work ys).1.length
  | [], out, work, h => by
    simp only [visit]
    exact ⟨h, by simp, fun z hz => Or.inl hz, fun _ hz => hz, fun _ hz => hz, fun z hz => Or.inl hz,
      fun _ hz hn => absurd hz hn, trivial⟩
  | y :: ys, out, work, h => by
    simp only [visit]
    split
    · rename_i hy
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := visit_spec ys out work h
      refine ⟨h1, ?_, ?_, h4, h5, h6, h7, h8⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact h4 _ hy
        · exact h2 z hz
      · intro z hz
        rcases h3 z hz with h | h
        · exact Or.inl h
        · exact Or.inr (List.mem_cons_of_mem _ h)
    · rename_i hy
      have hn : (out ++ [y]).Nodup := by
        rw [List.nodup_append]
        refine ⟨h, by simp, ?_⟩
        intro a ha b hb
        simp at hb
        rintro rfl
        exact hy (hb ▸ ha)
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := visit_spec ys (out ++ [y]) (work ++ [y]) hn
      refine ⟨h1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro z hz
        rcases List.mem_cons.mp hz with rfl | hz
        · exact h4 _ (by simp)
        · exact h2 z hz
      · intro z hz
        rcases h3 z hz with h | h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · simp at h; exact Or.inr (h ▸ List.mem_cons_self ..)
        · exact Or.inr (List.mem_cons_of_mem _ h)
      · intro z hz; exact h4 z (List.mem_append_left _ hz)
      · intro z hz; exact h5 z (List.mem_append_left _ hz)
      · intro z hz
        rcases h6 z hz with h | h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inl h
          · simp at h; exact Or.inr (h ▸ h4 y (by simp))
        · exact Or.inr h
      · intro z hz hzo
        by_cases hzy : z = y
        · exact h5 z (by simp [hzy])
        · exact h7 z hz (by simp [hzo, hzy])
      · simp only [List.length_append, List.length_singleton] at h8
        omega

/-- What the worklist returns: each node once, every node reached in one or
    more steps, and the successors of the start node and of every node
    returned are returned. -/
theorem bfs_spec (E : IdPairs) (a : UInt64) :
    ∀ (n : Nat) (out work r : List UInt64), bfsGo E n out work = some r → out.Nodup →
      (∀ c ∈ out, Reach1 E a c) → (∀ x ∈ work, x = a ∨ x ∈ out) →
      (∀ x, (x = a ∨ x ∈ out) → x ∉ work → ∀ y ∈ succs E x, y ∈ out) →
      r.Nodup ∧ (∀ c ∈ r, Reach1 E a c) ∧ (∀ x, (x = a ∨ x ∈ r) → ∀ y ∈ succs E x, y ∈ r)
  | 0, out, work, r, h, hn, hs, _, hc => by
    simp only [bfsGo] at h
    split at h
    · rename_i he
      cases h
      have hw : work = [] := List.isEmpty_iff.mp he
      subst hw
      exact ⟨hn, hs, fun x hx => hc x hx (by simp)⟩
    · cases h
  | _ + 1, out, [], r, h, hn, hs, _, hc => by
    simp only [bfsGo] at h
    cases h
    exact ⟨hn, hs, fun x hx => hc x hx (by simp)⟩
  | n + 1, out, x :: work, r, h, hn, hs, hw, hc => by
    simp only [bfsGo] at h
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, _⟩ := visit_spec (succs E x) out work hn
    apply bfs_spec E a n _ _ r h h1
    · intro c hc'
      rcases h3 c hc' with h' | h'
      · exact hs c h'
      · have hxc := (mem_succs E x c).mp h'
        rcases hw x (List.mem_cons_self ..) with rfl | hx
        · exact ⟨c, hxc, .refl _⟩
        · rcases hs x hx with ⟨b, hb, rb⟩
          exact ⟨b, hb, .tail rb hxc⟩
    · intro z hz
      rcases h6 z hz with h' | h'
      · rcases hw z (List.mem_cons_of_mem _ h') with h'' | h''
        · exact Or.inl h''
        · exact Or.inr (h4 z h'')
      · exact Or.inr h'
    · intro z hz hzw y hy
      by_cases hzx : z = x
      · subst hzx; exact h2 y hy
      · have hz' : z = a ∨ z ∈ out := by
          rcases hz with hz | hz
          · exact Or.inl hz
          · by_cases hzo : z ∈ out
            · exact Or.inr hzo
            · exact absurd (h7 z hz hzo) hzw
        have hzw' : z ∉ x :: work := by
          intro hm
          rcases List.mem_cons.mp hm with hm | hm
          · exact hzx hm
          · exact hzw (h5 z hm)
        exact h4 y (hc z hz' hzw' y hy)

/-- The rounds suffice: with `n` above the length of the worklist plus the
    number of pairs of `E` not yet matched by an output node, the loop ends
    with an empty worklist. -/
theorem bfs_some (E : IdPairs) :
    ∀ (n : Nat) (out work : List UInt64), out.Nodup → (∀ c ∈ out, c ∈ E.map (·.2)) →
      work.length + (E.length - out.length) < n → ∃ r, bfsGo E n out work = some r
  | 0, _, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | _ + 1, out, [], _, _, _ => ⟨out, by simp [bfsGo]⟩
  | n + 1, out, x :: work, hn, ht, hlt => by
    simp only [bfsGo]
    obtain ⟨h1, _, h3, _, _, _, _, h8⟩ := visit_spec (succs E x) out work hn
    have ht' : ∀ c ∈ (visit out work (succs E x)).1, c ∈ E.map (·.2) := by
      intro c hc
      rcases h3 c hc with h | h
      · exact ht c h
      · exact List.mem_map.mpr ⟨(x, c), (mem_succs E x c).mp h, rfl⟩
    have hle := List.Nodup.length_le_of_subset h1 ht'
    simp only [List.length_map] at hle
    apply bfs_some E n _ _ h1 ht'
    simp only [List.length_cons] at hlt
    omega

theorem reachModel_some (E : IdPairs) (a : UInt64) (fuel : Nat) (h : E.length + 2 ≤ fuel) :
    ∃ r, reachModel E a fuel = some r :=
  bfs_some E fuel [] [a] (by simp) (by simp) (by simp; omega)

theorem reachModel_mem (E : IdPairs) (a : UInt64) (fuel : Nat) (r : List UInt64)
    (h : reachModel E a fuel = some r) : r.Nodup ∧ ∀ c, c ∈ r ↔ Reach1 E a c := by
  obtain ⟨hn, hs, hc⟩ := bfs_spec E a fuel [] [a] r h (by simp) (by simp)
    (by intro x hx; simp at hx; exact Or.inl hx) (by intro x hx hxw; simp at hx hxw; exact absurd hx hxw)
  refine ⟨hn, fun c => ⟨hs c, ?_⟩⟩
  rintro ⟨b, hb, rb⟩
  have : ∀ y, Reach E b y → y ∈ r := by
    intro y ry
    induction ry with
    | refl => exact hc a (Or.inl rfl) b ((mem_succs E a b).mpr hb)
    | tail _ h2 ih => exact hc _ (Or.inr ih) _ ((mem_succs E _ _).mpr h2)
  exact this c rb

/-! ## The pairs the id path emits per start node (`IdQuery.closureM`) -/

/-- `p*` from `a`: `(a, a)` when `a` is a node of the graph, then `(a, c)` per
    node `c` of the worklist output other than `a`. -/
def starFrom (E : IdPairs) (N : List UInt64) (a : UInt64) (fuel : Nat) : Option IdPairs :=
  (reachModel E a fuel).map fun out =>
    (if a ∈ N then [(a, a)] else []) ++ (out.filter (fun c => !(decide (a ∈ N) && c == a))).map (fun c => (a, c))

/-- `p+` from `a`: `(a, c)` per node of the worklist output. -/
def plusFrom (E : IdPairs) (a : UInt64) (fuel : Nat) : Option IdPairs :=
  (reachModel E a fuel).map fun out => out.map (fun c => (a, c))

theorem nodup_map_pair (a : UInt64) : ∀ (l : List UInt64), l.Nodup → (l.map (fun c => (a, c))).Nodup
  | [], _ => by simp
  | c :: cs, h => by
    have ⟨hc, hcs⟩ := List.nodup_cons.mp h
    simp only [List.map_cons]
    refine List.nodup_cons.mpr ⟨?_, nodup_map_pair a cs hcs⟩
    intro hm
    rcases List.mem_map.mp hm with ⟨d, hd, he⟩
    simp only [Prod.mk.injEq] at he
    exact hc (he.2 ▸ hd)

/-- The pairs the id path emits for `p*` from `a` are the pairs of the
    reference's closure (`idEvalPath (p*)`) whose subject is `a`, each once;
    with the round bound the id path passes, the worklist does not run out. -/
theorem starFrom_mem (pid : WfIri → Option UInt64) (G : List IdTriple)
    (p : PropertyPath) (a : UInt64) (fuel : Nat)
    (hf : (idEvalPath pid p G).length + 2 ≤ fuel) :
    ∃ l, starFrom (idEvalPath pid p G) (idGraphNodes G) a fuel = some l ∧ l.Nodup ∧
      ∀ x, x ∈ l ↔ x ∈ idEvalPath pid (.zeroOrMore p) G ∧ x.1 = a := by
  obtain ⟨r, hr⟩ := reachModel_some (idEvalPath pid p G) a fuel hf
  obtain ⟨hrn, hrm⟩ := reachModel_mem _ a fuel r hr
  refine ⟨_, by unfold starFrom; rw [hr]; rfl, ?_, ?_⟩
  · rw [List.nodup_append]
    refine ⟨by split <;> simp, nodup_map_pair a _ (List.Nodup.sublist (List.filter_sublist) hrn), ?_⟩
    intro x hx y hy
    split at hx
    · rename_i haN
      simp at hx
      rcases List.mem_map.mp hy with ⟨c, hc, rfl⟩
      rcases List.mem_filter.mp hc with ⟨_, hc2⟩
      simp [haN] at hc2
      rw [hx]
      intro he
      simp only [Prod.mk.injEq] at he
      exact hc2 he.2.symm
    · simp at hx
  · intro x
    rw [star_mem]
    constructor
    · intro hx
      rcases List.mem_append.mp hx with hx | hx
      · split at hx
        · rename_i haN; simp at hx; subst hx; exact ⟨⟨haN, .refl _⟩, rfl⟩
        · simp at hx
      · rcases List.mem_map.mp hx with ⟨c, hc, rfl⟩
        have hr1 := (hrm c).mp (List.mem_filter.mp hc).1
        rcases hr1 with ⟨b, hb, rb⟩
        exact ⟨⟨(eval_nodes pid G p _ hb).1, Reach.head hb rb⟩, rfl⟩
    · rintro ⟨⟨haN, r⟩, rfl⟩
      rcases reach_cases r with he | h1
      · apply List.mem_append_left
        rw [if_pos haN]
        exact List.mem_singleton.mpr (Prod.ext rfl he.symm)
      · by_cases hc : x.2 = x.1
        · apply List.mem_append_left
          rw [if_pos haN]
          exact List.mem_singleton.mpr (Prod.ext rfl hc)
        · apply List.mem_append_right
          refine List.mem_map.mpr ⟨x.2, List.mem_filter.mpr ⟨(hrm x.2).mpr h1, ?_⟩, rfl⟩
          simp [hc]

/-- The pairs the id path emits for `p+` from `a` are the pairs of the
    reference's closure (`idEvalPath (p+)`) whose subject is `a`, each once. -/
theorem plusFrom_mem (pid : WfIri → Option UInt64) (G : List IdTriple)
    (p : PropertyPath) (a : UInt64) (fuel : Nat)
    (hf : (idEvalPath pid p G).length + 2 ≤ fuel) :
    ∃ l, plusFrom (idEvalPath pid p G) a fuel = some l ∧ l.Nodup ∧
      ∀ x, x ∈ l ↔ x ∈ idEvalPath pid (.oneOrMore p) G ∧ x.1 = a := by
  obtain ⟨r, hr⟩ := reachModel_some (idEvalPath pid p G) a fuel hf
  obtain ⟨hrn, hrm⟩ := reachModel_mem _ a fuel r hr
  refine ⟨_, by unfold plusFrom; rw [hr]; rfl, nodup_map_pair a r hrn, ?_⟩
  intro x
  rw [plus_mem pid G p]
  constructor
  · intro hx
    rcases List.mem_map.mp hx with ⟨c, hc, rfl⟩
    exact ⟨(hrm c).mp hc, rfl⟩
  · rintro ⟨h1, rfl⟩
    exact List.mem_map.mpr ⟨x.2, (hrm x.2).mpr h1, rfl⟩

/-- Reaching from `a` over a part `E'` of `E` that holds every pair of `E`
    whose subject is reached from `a` is reaching over `E`. -/
theorem reach_restrict (E E' : IdPairs) (a : UInt64) (hsub : ∀ q ∈ E', q ∈ E)
    (hcov : ∀ x y, Reach E a x → (x, y) ∈ E → (x, y) ∈ E') (c : UInt64) :
    Reach E a c ↔ Reach E' a c := by
  constructor
  · intro r
    induction r with
    | refl => exact .refl _
    | tail r1 h ih => exact .tail ih (hcov _ _ r1 h)
  · intro r
    induction r with
    | refl => exact .refl _
    | tail _ h ih => exact .tail ih (hsub _ h)

/-- The converse relation (`IdPath.swap`): reaching `c` from `a` over it is
    reaching `a` from `c` over `E`; the object restriction of `closureM`. -/
theorem reach_swap (E : IdPairs) (a c : UInt64) :
    Reach (E.map (fun p => (p.2, p.1))) a c ↔ Reach E c a := by
  constructor
  · intro r
    induction r with
    | refl => exact .refl _
    | tail _ h ih =>
      rcases List.mem_map.mp h with ⟨q, hq, he⟩
      simp only [Prod.mk.injEq] at he
      obtain ⟨e1, e2⟩ := he
      exact Reach.head (by rw [← e1, ← e2]; exact hq) ih
  · intro r
    induction r with
    | refl => exact .refl _
    | @tail b c' _ h ih =>
      have h' : (c', b) ∈ E.map (fun p => (p.2, p.1)) := List.mem_map.mpr ⟨(b, c'), h, rfl⟩
      exact Reach.head h' ih

/-! The hash-map worklist (`IdPath.reachPlus`) against the list model. -/

#guard (IdPath.reachPlus (IdPath.adjOf #[(1, 2), (2, 3), (3, 1), (3, 4)]) 1 6).map Array.toList ==
  reachModel [(1, 2), (2, 3), (3, 1), (3, 4)] 1 6
#guard (IdPath.reachPlus (IdPath.adjOf #[(1, 2), (1, 3), (2, 3), (3, 2)]) 1 6).map Array.toList ==
  reachModel [(1, 2), (1, 3), (2, 3), (3, 2)] 1 6
#guard (IdPath.reachPlus (IdPath.adjOf #[(1, 2), (2, 3)]) 3 4).map Array.toList ==
  reachModel [(1, 2), (2, 3)] 3 4
#guard (IdPath.reachPlus (IdPath.adjOf #[(1, 2), (2, 1)]) 1 4).map Array.toList ==
  reachModel [(1, 2), (2, 1)] 1 4
#guard (IdPath.reachPlus (IdPath.adjOf #[(1, 2), (2, 3), (3, 1), (3, 4)]) 1 1).map Array.toList ==
  reachModel [(1, 2), (2, 3), (3, 1), (3, 4)] 1 1

end L4Factoidal.Storage.Sbm11.IdPath
