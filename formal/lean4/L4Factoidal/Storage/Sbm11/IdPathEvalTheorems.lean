/-
L4Factoidal.Storage.Sbm11.IdPathEvalTheorems — the path evaluator on ids
(`IdQuery.evalIM`) against the reference's path relation over ids
(`IdPath.idEvalPath`) (https://github.com/danbri/factoidal/issues/776; part
of lemma L4n of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

* `resolvePathM_ok`: over a store whose dictionary lookup is the function
  `cid`, `resolvePathM` answers a resolved path of the shape `IPathOk`
  (each IRI its id; a negated property set the ids of its members).
* `evalIM_spec`: over a store of `BgpStore` (the four permutations in
  memory, each listing of the graph a permutation of `T`), for every path
  and every direction and restriction whose values are increasing, `evalIM`
  answers, up to order, the pairs of `idEvalPath` (predicate ids by `cid`)
  that the restriction keeps. Every form: one step, `^p`, `p1 / p2` (both directions of the
  restriction), `p1 | p2`, `p?`, `p*`, `p+` (`IdPathClosureExec.closureM_spec`)
  and negated property sets.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdPathClosureExecTheorems

namespace L4Factoidal.Storage.Sbm11.IdPathEval

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdPath (IdTriple IdPairs Pairs idGraphNodes idEvalPath succs)
open L4Factoidal.Storage.Sbm11.IdPathScanTheorems (Restr contains_iff)
open L4Factoidal.Storage.Sbm11.IdPathClosureExec (RGood restr_some keyOf)
open L4Factoidal.Storage.Sbm11.BgpTableTheorems (BgpStore)

/-! ## Resolved paths -/

/-- A path with its IRIs resolved by the dictionary lookup `cid`
    (`resolvePathM`). -/
def IPathOk (cid : Term → Option UInt64) : PropertyPath → IPath → Prop
  | .iri i, .link x => x = cid (.iri i)
  | .inverse q, .inv iq => IPathOk cid q iq
  | .sequence a b, .seq ia ib => IPathOk cid a ia ∧ IPathOk cid b ib
  | .alternative a b, .alt ia ib => IPathOk cid a ia ∧ IPathOk cid b ib
  | .zeroOrMore q, .star iq => IPathOk cid q iq
  | .oneOrMore q, .plus iq => IPathOk cid q iq
  | .zeroOrOne q, .opt iq => IPathOk cid q iq
  | .negatedSet ps, .nps ds is hd hi =>
    (∀ x, ds.contains x = true ↔ ∃ j ∈ negatedDirectIris ps, cid (.iri j) = some x) ∧
    (∀ x, is.contains x = true ↔ ∃ j ∈ negatedInverseIris ps, cid (.iri j) = some x) ∧
    hd = !(negatedDirectIris ps).isEmpty ∧ hi = !(negatedInverseIris ps).isEmpty
  | _, _ => False

theorem mem_iris (d : List WfIri) (t : Term) : t ∈ (d.toArray.map Term.iri).toList ↔ ∃ j ∈ d, t = .iri j := by
  simp only [Array.toList_map, List.mem_map, List.toList_toArray]
  constructor
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩
  · rintro ⟨j, hj, rfl⟩; exact ⟨j, hj, rfl⟩

/-- One term of `idsOfM`: its id appended when it has one not yet there. -/
def idsStep (cid : Term → Option UInt64) (r : Array UInt64) (t : Term) : Array UInt64 :=
  match cid t with
  | some x => if r.contains x then r else r.push x
  | none => r

theorem idsStep_mem (cid : Term → Option UInt64) (l : List Term) :
    ∀ (out : Array UInt64) (x : UInt64), (l.foldl (idsStep cid) out).contains x = true ↔
      out.contains x = true ∨ ∃ t ∈ l, cid t = some x := by
  induction l with
  | nil => intro out x; simp
  | cons t l ih =>
    intro out x
    rw [List.foldl_cons, ih]
    unfold idsStep
    cases hc : cid t with
    | none =>
      simp only [List.mem_cons]
      constructor
      · rintro (h | ⟨t', ht', h⟩); exact .inl h; exact .inr ⟨t', .inr ht', h⟩
      · rintro (h | ⟨t', rfl | ht', h⟩)
        · exact .inl h
        · rw [hc] at h; cases h
        · exact .inr ⟨t', ht', h⟩
    | some y =>
      simp only []
      by_cases hy : out.contains y = true
      · rw [if_pos hy]
        simp only [List.mem_cons]
        constructor
        · rintro (h | ⟨t', ht', h⟩); exact .inl h; exact .inr ⟨t', .inr ht', h⟩
        · rintro (h | ⟨t', rfl | ht', h⟩)
          · exact .inl h
          · rw [hc] at h; cases h; exact .inl hy
          · exact .inr ⟨t', ht', h⟩
      · rw [if_neg hy]
        rw [Array.contains_push]
        simp only [Bool.or_eq_true, beq_iff_eq, List.mem_cons]
        constructor
        · rintro ((h | h) | ⟨t', ht', h⟩)
          · exact .inl h
          · exact .inr ⟨t, .inl rfl, by rw [hc, h]⟩
          · exact .inr ⟨t', .inr ht', h⟩
        · rintro (h | ⟨t', rfl | ht', h⟩)
          · exact .inl (.inl h)
          · rw [hc] at h; cases h; exact .inl (.inr rfl)
          · exact .inr ⟨t', ht', h⟩

/-- A loop whose every step yields is a fold. -/
theorem forIn_yield_eq {α β : Type} (l : List α) (b : β) (f : α → β → ExceptT String Id (ForInStep β))
    (gf : β → α → β) (hf : ∀ a b, f a b = pure (.yield (gf b a))) : forIn l b f = pure (l.foldl gf b) := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih => rw [List.forIn_cons, hf, pure_bind]; exact ih _

section
variable (st : Store Id) (cid : Term → Option UInt64) (hid : ∀ t, st.idOf t = pure (cid t))
include hid

theorem idsOfM_spec (ts : Array Term) :
    ∃ out, idsOfM st ts = pure out ∧ ∀ x, out.contains x = true ↔ ∃ t ∈ ts.toList, cid t = some x := by
  refine ⟨ts.toList.foldl (idsStep cid) #[], ?_, fun x => by rw [idsStep_mem]; simp⟩
  unfold idsOfM
  simp only [← Array.forIn_toList]
  rw [forIn_yield_eq _ _ _ (idsStep cid) (fun t r => by
    simp only [hid, pure_bind, idsStep]
    cases cid t with
    | none => rfl
    | some x =>
      simp only []
      by_cases h : r.contains x = true
      · rw [if_pos h, if_neg (by rw [h]; decide)]
      · rw [if_neg h, if_pos (by simpa using h)])]
  rfl

/-- **`resolvePathM`** answers a path of the shape `IPathOk`. -/
theorem resolvePathM_ok : ∀ (path : PropertyPath), ∃ ip, resolvePathM st path = pure ip ∧ IPathOk cid path ip
  | .iri i => ⟨.link (cid (.iri i)), by simp [resolvePathM, hid], rfl⟩
  | .inverse q => by
    obtain ⟨iq, h1, h2⟩ := resolvePathM_ok q
    exact ⟨.inv iq, by simp only [resolvePathM, h1]; rfl, h2⟩
  | .sequence a b => by
    obtain ⟨ia, h1, h2⟩ := resolvePathM_ok a
    obtain ⟨ib, h3, h4⟩ := resolvePathM_ok b
    exact ⟨.seq ia ib, by simp only [resolvePathM, h1, h3]; rfl, h2, h4⟩
  | .alternative a b => by
    obtain ⟨ia, h1, h2⟩ := resolvePathM_ok a
    obtain ⟨ib, h3, h4⟩ := resolvePathM_ok b
    exact ⟨.alt ia ib, by simp only [resolvePathM, h1, h3]; rfl, h2, h4⟩
  | .zeroOrMore q => by
    obtain ⟨iq, h1, h2⟩ := resolvePathM_ok q
    exact ⟨.star iq, by simp only [resolvePathM, h1]; rfl, h2⟩
  | .oneOrMore q => by
    obtain ⟨iq, h1, h2⟩ := resolvePathM_ok q
    exact ⟨.plus iq, by simp only [resolvePathM, h1]; rfl, h2⟩
  | .zeroOrOne q => by
    obtain ⟨iq, h1, h2⟩ := resolvePathM_ok q
    exact ⟨.opt iq, by simp only [resolvePathM, h1]; rfl, h2⟩
  | .negatedSet ps => by
    obtain ⟨ds, h1, h2⟩ := idsOfM_spec st cid hid ((negatedDirectIris ps).toArray.map Term.iri)
    obtain ⟨is, h3, h4⟩ := idsOfM_spec st cid hid ((negatedInverseIris ps).toArray.map Term.iri)
    refine ⟨.nps ds is (!(negatedDirectIris ps).isEmpty) (!(negatedInverseIris ps).isEmpty), ?_, ?_, ?_, rfl, rfl⟩
    · simp only [resolvePathM, h1, h3]; rfl
    · intro x; rw [h2]
      constructor
      · rintro ⟨t, ht, hx⟩; obtain ⟨j, hj, rfl⟩ := (mem_iris _ t).mp ht; exact ⟨j, hj, hx⟩
      · rintro ⟨j, hj, hx⟩; exact ⟨_, (mem_iris _ _).mpr ⟨j, hj, rfl⟩, hx⟩
    · intro x; rw [h4]
      constructor
      · rintro ⟨t, ht, hx⟩; obtain ⟨j, hj, rfl⟩ := (mem_iris _ t).mp ht; exact ⟨j, hj, hx⟩
      · rintro ⟨j, hj, hx⟩; exact ⟨_, (mem_iris _ _).mpr ⟨j, hj, rfl⟩, hx⟩

end

/-! ## `evalIM`, form by form -/

/-- What `evalIM` answers for a resolved path: for every direction and
    restriction with increasing values, up to order, the pairs of `L` the
    restriction keeps. -/
def Spec (st : Store Id) (g : UInt64) (ip : IPath) (L : IdPairs) : Prop :=
  ∀ fwd R, RGood R → ∃ e s, evalIM st (some g) fwd ip R = pure (e, s) ∧ e.toList.Perm (L.filter (Restr fwd R))

theorem rgood_sorted {R : Option (Array UInt64)} (h : RGood R) : ∀ cs, R = some cs → Sip.Sorted cs :=
  fun cs hc => IdPath.sorted_of_pairwise cs (h cs hc)

theorem rgood_sd (xs : Array UInt64) : RGood (some (IdPath.sortedDistinct xs)) := by
  intro cs h; cases h; exact (IdPath.sortedDistinct_spec xs).1

section
variable (st : Store Id) (g : UInt64) (T : List IdTriple) (hst : BgpStore st g T)
include hst

theorem spec_link (x : Option UInt64) :
    Spec st g (.link x) (T.filterMap fun t => if x == some t.2.1 then some (t.1, t.2.2) else none) := by
  intro fwd R hR
  cases x with
  | none =>
    refine ⟨#[], {}, rfl, ?_⟩
    have : (T.filterMap fun t => if (none : Option UInt64) == some t.2.1 then some (t.1, t.2.2) else none) = [] := by
      rw [List.filterMap_eq_nil_iff]; intro t _; rfl
    rw [this]; exact List.Perm.refl _
  | some p =>
    obtain ⟨t, s, he, hp⟩ := IdPathScanTheorems.pathScan_link st g p T hst fwd R (rgood_sorted hR)
    refine ⟨IdQuery.pairsOf t "s" "o", s, ?_, ?_⟩
    · show (do
        let (t, s) ← pathScanM st g (some p) (if R.isNone || fwd then 0 else 1) R
        return (IdQuery.pairsOf t "s" "o", s) : ExceptT String Id _) = _
      rw [he]; rfl
    · have : (fun t : IdTriple => if (some p == some t.2.1) = true then some (t.1, t.2.2) else none) =
          (fun t => if (p == t.2.1) = true then some (t.1, t.2.2) else none) := by
        funext t; simp
      rw [this]; exact hp

end

theorem spec_alt (st : Store Id) (g : UInt64) (ia ib : IPath) (La Lb : IdPairs) (ha : Spec st g ia La)
    (hb : Spec st g ib Lb) : Spec st g (.alt ia ib) (La ++ Lb) := by
  intro fwd R hR
  obtain ⟨r1, s1, he1, hp1⟩ := ha fwd R hR
  obtain ⟨r2, s2, he2, hp2⟩ := hb fwd R hR
  refine ⟨r1 ++ r2, s1.add s2, ?_, ?_⟩
  · show (do
      let (r1, s1) ← evalIM st (some g) fwd ia R
      let (r2, s2) ← evalIM st (some g) fwd ib R
      return (r1 ++ r2, s1.add s2) : ExceptT String Id _) = _
    rw [he1]; simp only [pure_bind]; rw [he2]; rfl
  · rw [Array.toList_append, List.filter_append]
    exact hp1.append hp2

theorem restr_inv (fwd : Bool) (R : Option (Array UInt64)) (a b : UInt64) :
    Restr fwd R (b, a) = Restr (R.isSome && !fwd) R (a, b) := by
  cases R <;> cases fwd <;> rfl

theorem spec_inv (st : Store Id) (g : UInt64) (iq : IPath) (L : IdPairs)
    (hq : Spec st g iq L) :
    Spec st g (.inv iq) (L.map (fun pr => (pr.2, pr.1))) := by
  intro fwd R hR
  obtain ⟨r, s, he, hp⟩ := hq (R.isSome && !fwd) R hR
  refine ⟨IdPath.swap r, s, ?_, ?_⟩
  · show (do
      let (r, s) ← evalIM st (some g) (R.isSome && !fwd) iq R
      return (IdPath.swap r, s) : ExceptT String Id _) = _
    rw [he]; rfl
  · rw [IdPathClosureExec.swap_toList]
    unfold IdPathClosureExec.swapL
    refine (hp.map _).trans ?_
    rw [List.filter_map]
    apply List.Perm.of_eq
    congr 2
    funext pr
    show _ = Restr fwd R (pr.2, pr.1)
    rw [restr_inv fwd R pr.1 pr.2]

/-! ## Sequences -/

theorem succs_perm {l1 l2 : IdPairs} (h : l1.Perm l2) (x : UInt64) : (succs l1 x).Perm (succs l2 x) :=
  h.filterMap _

theorem succs_filter_key (l : IdPairs) (S : Array UInt64) (m : UInt64) (hm : S.contains m = true) :
    succs (l.filter (fun q => S.contains q.1)) m = succs l m := by
  unfold succs
  rw [List.filterMap_filter]
  congr 1
  funext q
  by_cases h : q.1 = m
  · rw [h, hm]; rfl
  · have : (q.1 == m) = false := by simpa using h
    simp [this]

theorem succs_filter_obj (l : IdPairs) (rs : Array UInt64) (m : UInt64) :
    succs (l.filter (fun q => rs.contains q.2)) m = (succs l m).filter (fun c => rs.contains c) := by
  unfold succs
  rw [List.filterMap_filter, List.filter_filterMap]
  congr 1
  funext q
  by_cases h : (q.1 == m) = true
  · simp only [h, if_true, Option.filter_some]
  · simp only [Bool.not_eq_true] at h
    simp [h]

theorem flatMap_if_filter {α β : Type} (P : α → Bool) (G : α → List β) :
    ∀ (l : List α), l.flatMap (fun a => if P a then G a else []) = (l.filter P).flatMap G
  | [] => rfl
  | a :: l => by
    rw [List.flatMap_cons, List.filter_cons, flatMap_if_filter P G l]
    by_cases h : P a = true <;> simp [h]

/-- The pairs of a sequence from a pair `p` of the first relation. -/
def seqG (Lb : IdPairs) (p : UInt64 × UInt64) : IdPairs := (succs Lb p.2).map (fun c => (p.1, c))

theorem spec_seq (st : Store Id) (g : UInt64) (ia ib : IPath) (La Lb : IdPairs) (ha : Spec st g ia La)
    (hb : Spec st g ib Lb) :
    Spec st g (.seq ia ib) (La.flatMap fun a => Lb.filterMap fun b => if a.2 == b.1 then some (a.1, b.2) else none) := by
  intro fwd R hR
  rw [IdPath.compose_eq_model]
  by_cases hdir : (R.isNone || fwd) = true
  · obtain ⟨r1, s1, he1, hp1⟩ := ha true R hR
    obtain ⟨r2, s2, he2, hp2⟩ := hb true (some (IdPath.seconds r1)) (rgood_sd _)
    refine ⟨IdPath.compose r1 r2, s1.add s2, ?_, ?_⟩
    · show (if R.isNone || fwd then do
          let (r1, s1) ← evalIM st (some g) true ia R
          let (r2, s2) ← evalIM st (some g) true ib (some (IdPath.seconds r1))
          return (IdPath.compose r1 r2, s1.add s2)
        else do
          let (r2, s2) ← evalIM st (some g) false ib R
          let (r1, s1) ← evalIM st (some g) false ia (some (IdPath.firsts r2))
          return (IdPath.compose r1 r2, s1.add s2) : ExceptT String Id _) = _
      rw [if_pos hdir, he1]; simp only [pure_bind]; rw [he2]; rfl
    · rw [IdPath.compose_toList]
      -- the successors over `r2` are those over `Lb` for the objects of `r1`
      have step1 : (r1.toList.flatMap fun p => (succs r2.toList p.2).map fun c => (p.1, c)).Perm
          (r1.toList.flatMap (seqG Lb)) := by
        apply IdGroup.perm_flatMap_left
        intro p hp
        apply List.Perm.map
        refine (succs_perm hp2 p.2).trans (List.Perm.of_eq ?_)
        apply succs_filter_key Lb (IdPath.seconds r1) p.2
        exact (contains_iff _ _).mpr ((IdPath.seconds_mem r1 p.2).mpr ⟨p, hp, rfl⟩)
      refine step1.trans ((List.Perm.flatMap_right _ hp1).trans (List.Perm.of_eq ?_))
      rw [List.filter_flatMap, ← flatMap_if_filter]
      congr 1
      funext p
      unfold seqG
      rw [List.filter_map]
      have hr : ∀ c, Restr fwd R (p.1, c) = Restr true R p := by
        intro c
        cases R with
        | none => rfl
        | some rs =>
          have : fwd = true := by simpa using hdir
          subst this; rfl
      by_cases h : Restr true R p = true
      · rw [if_pos h, List.filter_eq_self.mpr (fun c _ => by simp only [Function.comp]; rw [hr]; exact h)]
      · rw [if_neg h, eq_comm, List.map_eq_nil_iff, List.filter_eq_nil_iff]
        intro c _ hc
        simp only [Function.comp] at hc
        rw [hr] at hc
        exact h hc
  · cases R with
    | none => exact absurd rfl hdir
    | some rs =>
      have hf : fwd = false := by simpa using hdir
      subst hf
      obtain ⟨r2, s2, he2, hp2⟩ := hb false (some rs) hR
      obtain ⟨r1, s1, he1, hp1⟩ := ha false (some (IdPath.firsts r2)) (rgood_sd _)
      refine ⟨IdPath.compose r1 r2, s1.add s2, ?_, ?_⟩
      · show (if (some rs).isNone || false then do
            let (r1, s1) ← evalIM st (some g) true ia (some rs)
            let (r2, s2) ← evalIM st (some g) true ib (some (IdPath.seconds r1))
            return (IdPath.compose r1 r2, s1.add s2)
          else do
            let (r2, s2) ← evalIM st (some g) false ib (some rs)
            let (r1, s1) ← evalIM st (some g) false ia (some (IdPath.firsts r2))
            return (IdPath.compose r1 r2, s1.add s2) : ExceptT String Id _) = _
        rw [if_neg hdir, he2]; simp only [pure_bind]; rw [he1]; rfl
      · rw [IdPath.compose_toList]
        -- the successors over `r2` are those over `Lb` restricted to the objects in `rs`
        let Lb' := Lb.filter (fun q => rs.contains q.2)
        have step1 : (r1.toList.flatMap fun p => (succs r2.toList p.2).map fun c => (p.1, c)).Perm
            (r1.toList.flatMap (seqG Lb')) := by
          apply IdGroup.perm_flatMap_left
          intro p _
          exact List.Perm.map _ (succs_perm hp2 p.2)
        refine step1.trans ((List.Perm.flatMap_right _ hp1).trans (List.Perm.of_eq ?_))
        -- a pair of `La` whose object is not a subject of `r2` gives no pair
        have hdrop : (La.filter (Restr false (some (IdPath.firsts r2)))).flatMap (seqG Lb') = La.flatMap (seqG Lb') := by
          rw [← flatMap_if_filter]
          congr 1
          funext p
          by_cases h : Restr false (some (IdPath.firsts r2)) p = true
          · rw [if_pos h]
          · rw [if_neg h, eq_comm]
            unfold seqG
            rw [List.map_eq_nil_iff, List.eq_nil_iff_forall_not_mem]
            intro c hc
            rw [IdPath.mem_succs] at hc
            have hq : (p.2, c) ∈ r2.toList := hp2.mem_iff.mpr hc
            apply h
            show (IdPath.firsts r2).contains p.2 = true
            exact (contains_iff _ _).mpr ((IdPath.firsts_mem r2 p.2).mpr ⟨_, hq, rfl⟩)
        rw [hdrop, List.filter_flatMap]
        congr 1
        funext p
        unfold seqG
        rw [List.filter_map, succs_filter_obj]
        rfl

/-! ## `p?`, `p*`, `p+` -/

section
variable (st : Store Id) (g : UInt64) (T : List IdTriple) (hst : BgpStore st g T)
include hst

theorem spec_opt (iq : IPath) (L : IdPairs) (hq : Spec st g iq L) :
    Spec st g (.opt iq) (IdPath.idDedup ((idGraphNodes T).map (fun n => (n, n)) ++ L)) := by
  intro fwd R hR
  obtain ⟨e, s1, he, hp⟩ := hq fwd R hR
  -- the reflexive pairs
  obtain ⟨nodes, s0, hn, hnm⟩ : ∃ nodes s0, (match R with
      | some rs => nodesAmongM st (some g) rs
      | none => allNodesM st (some g) : ExceptT String Id (Array UInt64 × ScanStats)) = pure (nodes, s0) ∧
      ∀ n, n ∈ nodes.toList ↔ n ∈ idGraphNodes T ∧ Restr fwd R (n, n) = true := by
    cases R with
    | none =>
      obtain ⟨ns, s0, h1, _, h3⟩ := IdPathScanTheorems.allNodes_spec st g T hst
      exact ⟨ns, s0, h1, fun n => by rw [h3]; simp [Restr]⟩
    | some rs =>
      obtain ⟨ns, s0, h1, _, h3⟩ := IdPathScanTheorems.nodesAmong_spec st g T hst rs (rgood_sorted hR rs rfl)
      refine ⟨ns, s0, h1, fun n => ?_⟩
      rw [h3, restr_some, contains_iff]
      have : keyOf fwd (n, n) = n := by cases fwd <;> rfl
      rw [this, and_comm]
  refine ⟨IdPath.dedupPairs (nodes.map (fun n => (n, n)) ++ e), s0.add s1, ?_, ?_⟩
  · cases R <;> (rw [evalIM]; dsimp only at hn; rw [hn]; simp only [pure_bind]; rw [he]; rfl)
  · apply (List.perm_ext_iff_of_nodup (IdPath.dedupPairs_spec _).1 ((IdPath.nodup_idDedup _).filter _)).mpr
    intro x
    rw [(IdPath.dedupPairs_spec _).2, List.mem_filter, IdPath.mem_idDedup]
    simp only [Array.toList_append, Array.toList_map, List.mem_append, List.mem_map]
    rw [hp.mem_iff, List.mem_filter]
    constructor
    · rintro (⟨n, hn, rfl⟩ | ⟨hx, hr⟩)
      · obtain ⟨h1, h2⟩ := (hnm n).mp hn
        exact ⟨.inl ⟨n, h1, rfl⟩, h2⟩
      · exact ⟨.inr hx, hr⟩
    · rintro ⟨⟨n, hn, rfl⟩ | hx, hr⟩
      · exact .inl ⟨n, (hnm n).mpr ⟨hn, hr⟩, rfl⟩
      · exact .inr ⟨hx, hr⟩

theorem spec_star (pid : WfIri → Option UInt64) (q : PropertyPath) (iq : IPath)
    (hq : Spec st g iq (idEvalPath pid q T)) :
    Spec st g (.star iq) (idEvalPath pid (.zeroOrMore q) T) := by
  intro fwd R hR
  obtain ⟨out, s, he, hnd, hm⟩ := IdPathClosureExec.closureM_spec st g T hst (idEvalPath pid q T)
    (IdPath.eval_nodes pid T q) (fun f r => evalIM st (some g) f iq r) (fun f R hR => hq f R hR)
    fwd R hR true
  refine ⟨out, s, he, ?_⟩
  apply (List.perm_ext_iff_of_nodup hnd ((IdPath.star_nodup pid T q).filter _)).mpr
  intro x
  rw [hm, List.mem_filter, IdPath.star_mem]
  rfl

theorem spec_plus (pid : WfIri → Option UInt64) (q : PropertyPath) (iq : IPath)
    (hq : Spec st g iq (idEvalPath pid q T)) :
    Spec st g (.plus iq) (idEvalPath pid (.oneOrMore q) T) := by
  intro fwd R hR
  obtain ⟨out, s, he, hnd, hm⟩ := IdPathClosureExec.closureM_spec st g T hst (idEvalPath pid q T)
    (IdPath.eval_nodes pid T q) (fun f r => evalIM st (some g) f iq r) (fun f R hR => hq f R hR)
    fwd R hR false
  refine ⟨out, s, he, ?_⟩
  apply (List.perm_ext_iff_of_nodup hnd ((IdPath.plus_nodup pid T q).filter _)).mpr
  intro x
  rw [hm, List.mem_filter, IdPath.plus_mem]
  rfl

end

/-! ## Negated property sets -/

theorem filter_map_filter_map {β γ : Type} (A : IdTriple → Bool) (row : IdTriple → β) (q : β → Bool)
    (proj : β → γ) : ∀ (l : List IdTriple),
    (((l.filter A).map row).filter q).map proj =
      l.filterMap (fun t => if A t && q (row t) then some (proj (row t)) else none)
  | [] => rfl
  | t :: l => by
    rw [List.filter_cons, List.filterMap_cons, ← filter_map_filter_map A row q proj l]
    by_cases ha : A t = true <;> by_cases hq : q (row t) = true <;> simp [ha, hq]

theorem any_eq_contains (ex : Array UInt64) (exL : List WfIri) (pid : WfIri → Option UInt64)
    (hex : ∀ p, ex.contains p = true ↔ ∃ j ∈ exL, pid j = some p) (p : UInt64) :
    (exL.any fun j => pid j == some p) = ex.contains p := by
  apply Bool.eq_iff_iff.mpr
  rw [List.any_eq_true, hex]
  simp only [beq_iff_eq]

theorem restr_inv_byS (fwd : Bool) (R : Option (Array UInt64)) (a b : UInt64) :
    Restr (!(R.isNone || fwd)) R (a, b) = Restr fwd R (b, a) := by
  cases R <;> cases fwd <;> rfl

theorem nps_direct (T : List IdTriple) (fwd : Bool) (R : Option (Array UInt64)) (ex : Array UInt64)
    (exL : List WfIri) (pid : WfIri → Option UInt64) (hex : ∀ p, ex.contains p = true ↔ ∃ j ∈ exL, pid j = some p) :
    ((IdPathScanTheorems.allRows T (R.isNone || fwd) R).filter
        (fun r => !ex.contains ((OptJoin.idLookup "p" r).getD 0))).map (IdPathScanTheorems.proj2 "s" "o") =
      (IdPath.idNpsDirect pid exL T).filter (Restr fwd R) := by
  unfold IdPathScanTheorems.allRows IdPath.idNpsDirect
  rw [filter_map_filter_map, List.filter_filterMap]
  congr 1
  funext t
  rw [any_eq_contains ex exL pid hex]
  have hr := congrFun (IdPathScanTheorems.restr_isNone fwd R) (t.1, t.2.2)
  by_cases hc : t.2.1 ∈ ex
  · simp [hc, OptJoin.idLookup]
  · simp [hc, hr, OptJoin.idLookup, IdPathScanTheorems.proj2, Option.filter_some]

theorem nps_inverse (T : List IdTriple) (fwd : Bool) (R : Option (Array UInt64)) (ex : Array UInt64)
    (exL : List WfIri) (pid : WfIri → Option UInt64) (hex : ∀ p, ex.contains p = true ↔ ∃ j ∈ exL, pid j = some p) :
    ((IdPathScanTheorems.allRows T (!(R.isNone || fwd)) R).filter
        (fun r => !ex.contains ((OptJoin.idLookup "p" r).getD 0))).map (IdPathScanTheorems.proj2 "o" "s") =
      (IdPath.idNpsInverse pid exL T).filter (Restr fwd R) := by
  unfold IdPathScanTheorems.allRows IdPath.idNpsInverse
  rw [filter_map_filter_map, List.filter_filterMap]
  congr 1
  funext t
  rw [any_eq_contains ex exL pid hex]
  have hr := restr_inv fwd R t.1 t.2.2
  by_cases hc : t.2.1 ∈ ex
  · simp [hc, OptJoin.idLookup]
  · simp [hc, hr, OptJoin.idLookup, IdPathScanTheorems.proj2, Option.filter_some]

section
variable (st : Store Id) (g : UInt64) (T : List IdTriple) (hst : BgpStore st g T)
include hst

theorem spec_nps (cid : Term → Option UInt64) (ps : List PropertyPath)
    (ds is : Array UInt64) (hd hi : Bool) (hok : IPathOk cid (.negatedSet ps) (.nps ds is hd hi)) :
    Spec st g (.nps ds is hd hi) (idEvalPath (fun i => cid (.iri i)) (.negatedSet ps) T) := by
  obtain ⟨hD, hI, hhd, hhi⟩ := hok
  intro fwd R hR
  obtain ⟨t1, s1, he1, hnd1, hnu1, M1, hpw1, hp1⟩ :=
    IdPathScanTheorems.pathScan_all st g T hst (R.isNone || fwd) R (rgood_sorted hR)
  obtain ⟨t2, s2, he2, hnd2, hnu2, M2, hpw2, hp2⟩ :=
    IdPathScanTheorems.pathScan_all st g T hst (!(R.isNone || fwd)) R (rgood_sorted hR)
  have he2' : pathScanM st g none (if (R.isNone || fwd) = true then 3 else 2) R = pure (t2, s2) := by
    rw [show (if (R.isNone || fwd) = true then 3 else 2) = (if (!(R.isNone || fwd)) = true then 2 else 3) by
      cases (R.isNone || fwd) <;> rfl]
    exact he2
  have hDp : (npsPairs t1 ds false).toList.Perm
      ((IdPath.idNpsDirect (fun i => cid (.iri i)) (negatedDirectIris ps) T).filter (Restr fwd R)) := by
    rw [IdPathScanTheorems.npsPairs_eq t1 hnd1 hnu1 M1 hpw1 ds false
      (fun r hr => IdPathScanTheorems.allRows_lookups _ _ _ r (hp1.mem_iff.mp hr))]
    simp only [Bool.false_eq_true, if_false]
    rw [← nps_direct T fwd R ds (negatedDirectIris ps) (fun i => cid (.iri i)) hD]
    exact (hp1.filter _).map _
  have hIp : (npsPairs t2 is true).toList.Perm
      ((IdPath.idNpsInverse (fun i => cid (.iri i)) (negatedInverseIris ps) T).filter (Restr fwd R)) := by
    rw [IdPathScanTheorems.npsPairs_eq t2 hnd2 hnu2 M2 hpw2 is true
      (fun r hr => IdPathScanTheorems.allRows_lookups _ _ _ r (hp2.mem_iff.mp hr))]
    simp only [if_true]
    rw [← nps_inverse T fwd R is (negatedInverseIris ps) (fun i => cid (.iri i)) hI]
    exact (hp2.filter _).map _
  show ∃ e s, evalIM st (some g) fwd (.nps ds is hd hi) R = pure (e, s) ∧ e.toList.Perm
    (((if (!(negatedInverseIris ps).isEmpty && !!(negatedDirectIris ps).isEmpty) = true then []
        else IdPath.idNpsDirect (fun i => cid (.iri i)) (negatedDirectIris ps) T) ++
      (if (!(negatedDirectIris ps).isEmpty && !!(negatedInverseIris ps).isEmpty) = true then []
        else IdPath.idNpsInverse (fun i => cid (.iri i)) (negatedInverseIris ps) T)).filter (Restr fwd R))
  rw [← hhd, ← hhi, List.filter_append]
  generalize IdPath.idNpsDirect (fun i => cid (.iri i)) (negatedDirectIris ps) T = LD at hDp
  generalize IdPath.idNpsInverse (fun i => cid (.iri i)) (negatedInverseIris ps) T = LI at hIp
  rw [evalIM]
  cases hd <;> cases hi
  · refine ⟨npsPairs t1 ds false ++ npsPairs t2 is true, s1.add s2, ?_, ?_⟩
    · simp only [Bool.not_false, Bool.and_true, Bool.and_false, Bool.not_true, if_true, Bool.false_eq_true,
        if_false]
      rw [he1]; simp only [pure_bind]; rw [he2']; rfl
    · simp only [Bool.not_false, Bool.and_true, Bool.and_false, Bool.false_eq_true, if_false, Array.toList_append]
      exact hDp.append hIp
  · refine ⟨#[] ++ npsPairs t2 is true, ({} : ScanStats).add s2, ?_, ?_⟩
    · simp only [Bool.not_false, Bool.and_true, Bool.and_false, Bool.not_true, if_true, Bool.false_eq_true,
        if_false, Bool.true_and]
      simp only [pure_bind]; rw [he2']; rfl
    · simp only [Bool.not_false, Bool.and_true, Bool.true_and, Bool.false_eq_true, if_false, if_true,
        Array.toList_append, Bool.and_false, Bool.not_true]
      simpa using hIp
  · refine ⟨npsPairs t1 ds false ++ #[], s1.add {}, ?_, ?_⟩
    · simp only [Bool.not_false, Bool.and_true, Bool.and_false, Bool.not_true, if_true, Bool.false_eq_true,
        if_false, Bool.true_and]
      rw [he1]; simp only [pure_bind]
    · simp only [Bool.not_false, Bool.and_true, Bool.true_and, Bool.false_eq_true, if_false, if_true,
        Array.toList_append, Bool.and_false, Bool.not_true]
      simpa using hDp
  · refine ⟨npsPairs t1 ds false ++ npsPairs t2 is true, s1.add s2, ?_, ?_⟩
    · simp only [Bool.not_false, Bool.and_true, Bool.and_false, Bool.not_true, if_true, Bool.false_eq_true,
        if_false]
      rw [he1]; simp only [pure_bind]; rw [he2']; rfl
    · simp only [Bool.not_false, Bool.and_true, Bool.and_false, Bool.not_true, Bool.false_eq_true, if_false,
        Array.toList_append]
      exact hDp.append hIp

end

/-! ## The path evaluator -/

/-- **`evalIM` against `idEvalPath`.** Over a store of `BgpStore` (each
    permutation in memory, each listing of the graph `g` a permutation of
    `T`), for every path resolved by the dictionary lookup `cid`
    (`IPathOk`, what `resolvePathM` answers by `resolvePathM_ok`), every
    direction and every restriction whose values are increasing, `evalIM`
    answers, up to order, the pairs of `idEvalPath` (predicate ids by `cid`)
    over `T` that the restriction keeps. -/
theorem evalIM_spec (st : Store Id) (g : UInt64) (T : List IdTriple) (hst : BgpStore st g T)
    (cid : Term → Option UInt64) :
    ∀ (path : PropertyPath) (ip : IPath), IPathOk cid path ip →
      Spec st g ip (idEvalPath (fun i => cid (.iri i)) path T)
  | .iri i, ip, h => by
    cases ip <;> try exact (show False from h).elim
    rename_i x
    have hx : x = cid (.iri i) := h
    subst hx
    exact spec_link st g T hst _
  | .inverse q, ip, h => by
    cases ip <;> try exact (show False from h).elim
    rename_i iq
    exact spec_inv st g iq _ (evalIM_spec st g T hst cid q iq h)
  | .sequence a b, ip, h => by
    cases ip <;> try exact (show False from h).elim
    rename_i ia ib
    exact spec_seq st g ia ib _ _ (evalIM_spec st g T hst cid a ia h.1)
      (evalIM_spec st g T hst cid b ib h.2)
  | .alternative a b, ip, h => by
    cases ip <;> try exact (show False from h).elim
    rename_i ia ib
    exact spec_alt st g ia ib _ _ (evalIM_spec st g T hst cid a ia h.1)
      (evalIM_spec st g T hst cid b ib h.2)
  | .zeroOrMore q, ip, h => by
    cases ip <;> try exact (show False from h).elim
    rename_i iq
    exact spec_star st g T hst _ q iq (evalIM_spec st g T hst cid q iq h)
  | .oneOrMore q, ip, h => by
    cases ip <;> try exact (show False from h).elim
    rename_i iq
    exact spec_plus st g T hst _ q iq (evalIM_spec st g T hst cid q iq h)
  | .zeroOrOne q, ip, h => by
    cases ip <;> try exact (show False from h).elim
    rename_i iq
    exact spec_opt st g T hst iq _ (evalIM_spec st g T hst cid q iq h)
  | .negatedSet ps, ip, h => by
    cases ip <;> try exact (show False from h).elim
    rename_i ds is hd hi
    exact spec_nps st g T hst cid ps ds is hd hi h

end L4Factoidal.Storage.Sbm11.IdPathEval

#print axioms L4Factoidal.Storage.Sbm11.IdPathEval.evalIM_spec
#print axioms L4Factoidal.Storage.Sbm11.IdPathEval.resolvePathM_ok
