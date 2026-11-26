import L4Factoidal.JS.FuelMono

/-!
# Tier 2 of BubblePopJS: the inline cache for property reads against the reference

Tier 2 (issue 471, https://github.com/danbri/factoidal-core/issues/471) is one guarded fast path in
the register machine's `getMember` (`vmLoop`, `JS/Interp.lean`): with the run's `Mode` having
`tier2`, the read first asks the site's entry of the inline cache (`HeapOf.icache`,
`Tier2.getMember?`). The machine fills the cache in every mode, the same way (`Tier2.memberGen`).

Proved here:

- `icGet_sound`: an answer of the cache (not `.hole`) is the answer of `fastGetV`, the read the
  arm's own code makes. The entry's proofs (`IC`) say where the key is, so the cache does not scan.
- `icSet_hit`: on such an answer, the fill writes the entry that is already there, so the heap is
  unchanged.
- `getMember_site`: in the form the walk of `JS/FuelMono.lean` leaves at a site (`Le.withFast`):
  the arm's own code is `Le` the fast path followed by the arm's own code.

`JS/FuelMonoAll.lean` composes it with tier 1 over the whole block (`IH_all`): a run with both tiers
on ends as the reference run does, in the same heap, whenever the reference does not run out of
fuel.

Does not say: anything about speed, or how often the cache answers.
-/

namespace L4Factoidal.JS.Tier2Proofs
open L4Factoidal.JS FuelMono

variable {H : Type}

theorem sameKeys_eq {a b : Array String} (h : sameKeys a b = true) : a = b := by
  unfold sameKeys at h
  rw [withPtrEq] at h
  exact beq_iff_eq.mp h

theorem kindOk_of_icOk (kd : Kind) (k : String) (h : kd.icOk = true) :
    (match kd with
      | .proxy .. | .typed .. | .prim _ => false
      | .array _ => k != "length" && !k.front.isDigit
      | _ => true) = true := by
  cases kd <;> first | rfl | exact absurd h Bool.false_ne_true

theorem fastGet_succ (h : HeapOf H) (id : Nat) (key : String) (fuel : Nat) :
    h.fastGet id key (fuel + 1) = (
      let o := h.objs.getD id default
      let kindOk := match o.kind with
        | .proxy .. | .typed .. | .prim _ => false
        | .array _ => key != "length" && !key.front.isDigit
        | _ => true
      if !kindOk then .hole else
      match o.props.get? key with
      | some (.data v ..) => v
      | some _ => .hole
      | none =>
        if isPrivKey key then .hole else
        match o.proto with
        | .obj p => h.fastGet p key fuel
        | _ => .hole) := by
  rfl

theorem get?_small (m : PropMap PropV) (k : String) (hb : m.big = none) :
    m.get? k = (let i := PropMap.scan m.ks k 0; if i == m.ks.size then none else m.vs[i]?) := by
  unfold PropMap.get?; rw [hb]

/-- What one object contributes to `fastGet` when its kind keeps every property in `props`, its map
is small, and `scan` finds `k` at `slot`. -/
theorem fastGet_own (h : HeapOf H) (id : Nat) (k : String) (fuel slot : Nat) (o : Obj)
    (ho : h.objs.getD id default = o) (hk : o.kind.icOk = true) (hb : o.props.big = none)
    (hs : PropMap.scan o.props.ks k 0 = slot) (hl : slot < o.props.ks.size) :
    h.fastGet id k (fuel + 1) =
      match o.props.vs[slot]? with
      | some (.data v ..) => v
      | some _ => .hole
      | none => if isPrivKey k then .hole else
        match o.proto with
        | .obj p => h.fastGet p k fuel
        | _ => .hole := by
  rw [fastGet_succ]; simp only [ho]
  rw [get?_small _ _ hb, hs]
  have : (slot == o.props.ks.size) = false := by simp; omega
  simp only [this]
  cases hkd : o.kind <;> rw [hkd] at hk <;> first | exact absurd hk Bool.false_ne_true | rfl

theorem fastGet_miss (h : HeapOf H) (id : Nat) (k : String) (fuel : Nat) (o : Obj)
    (ho : h.objs.getD id default = o) (hk : o.kind.icOk = true) (hb : o.props.big = none)
    (hs : PropMap.scan o.props.ks k 0 = o.props.ks.size) (hp : isPrivKey k = false) :
    h.fastGet id k (fuel + 1) =
      match o.proto with
      | .obj p => h.fastGet p k fuel
      | _ => .hole := by
  rw [fastGet_succ]; simp only [ho]
  rw [get?_small _ _ hb, hs]
  simp only [beq_self_eq_true, ↓reduceIte, hp, Bool.false_eq_true]
  cases hkd : o.kind <;> rw [hkd] at hk <;> first | exact absurd hk Bool.false_ne_true | rfl

theorem isNone_eq {α} {o : Option α} (h : o.isNone = true) : o = none := by
  cases o <;> simp_all

/-- **Kind: refinement.** A value of the inline cache that is not `.hole` is the value `fastGetV`
gives: the same read, without its scan of the keys. Says: for every heap, entry, value and key.
Does not say: anything about speed, or that an entry is ever filled. -/
theorem icGet_sound (h : HeapOf H) (e : IC) (b : Value) (k : String)
    (hn : h.icGet e b k ≠ .hole) : h.fastGetV b k = h.icGet e b k := by
  cases b with
  | obj id =>
    cases e with
    | none => exact absurd rfl hn
    | own key ks slot hs hl hkn =>
      simp only [HeapOf.icGet] at hn ⊢
      by_cases hkey : (key == k) = true
      · have hk : key = k := beq_iff_eq.mp hkey
        subst hk
        simp only [hkey, ↓reduceIte] at hn ⊢
        by_cases hc : ((h.objs.getD id default).kind.icOk && (h.objs.getD id default).props.big.isNone &&
            sameKeys (h.objs.getD id default).props.ks ks) = true
        · simp only [hc, ↓reduceIte] at hn ⊢
          simp only [Bool.and_eq_true] at hc
          obtain ⟨⟨hk1, hb1⟩, hs1⟩ := hc
          have hks := sameKeys_eq hs1
          unfold HeapOf.fastGetV
          simp only [hkn, Bool.false_eq_true, ↓reduceIte]
          rw [fastGet_own h id key 999 slot _ rfl hk1 (isNone_eq hb1) (by rw [hks]; exact hs) (by rw [hks]; exact hl)]
          split at hn <;> simp_all
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hn; exact absurd rfl hn
      · simp only [hkey, Bool.false_eq_true, ↓reduceIte] at hn; exact absurd rfl hn
    | proto key ks pks slot h0 hs hl hp hkn =>
      simp only [HeapOf.icGet] at hn ⊢
      by_cases hkey : (key == k) = true
      · have hk : key = k := beq_iff_eq.mp hkey
        subst hk
        simp only [hkey, ↓reduceIte] at hn ⊢
        by_cases hc : ((h.objs.getD id default).kind.icOk && (h.objs.getD id default).props.big.isNone &&
            sameKeys (h.objs.getD id default).props.ks ks) = true
        · simp only [hc, ↓reduceIte] at hn ⊢
          simp only [Bool.and_eq_true] at hc
          obtain ⟨⟨hk1, hb1⟩, hs1⟩ := hc
          have hks := sameKeys_eq hs1
          unfold HeapOf.fastGetV
          simp only [hkn, Bool.false_eq_true, ↓reduceIte]
          rw [fastGet_miss h id key 999 _ rfl hk1 (isNone_eq hb1) (by rw [hks]; exact h0) hp]
          cases hpr : (h.objs.getD id default).proto with
          | obj p =>
            simp only [hpr] at hn ⊢
            by_cases hc2 : ((h.objs.getD p default).kind.icOk && (h.objs.getD p default).props.big.isNone &&
                sameKeys (h.objs.getD p default).props.ks pks) = true
            · simp only [hc2, ↓reduceIte] at hn ⊢
              simp only [Bool.and_eq_true] at hc2
              obtain ⟨⟨hk2, hb2⟩, hs2⟩ := hc2
              have hks2 := sameKeys_eq hs2
              rw [fastGet_own h p key 998 slot _ rfl hk2 (isNone_eq hb2) (by rw [hks2]; exact hs) (by rw [hks2]; exact hl)]
              split at hn <;> simp_all
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hn; exact absurd rfl hn
          | _ => simp only [hpr] at hn; exact absurd rfl hn
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hn; exact absurd rfl hn
      · simp only [hkey, Bool.false_eq_true, ↓reduceIte] at hn; exact absurd rfl hn
  | _ => exact absurd rfl hn

/-- **Kind: invariant of the cache.** On a hit, the entry the fill makes (`icMake`) is the entry
the read used: a hit leaves nothing for the fill to change. -/
theorem icMake_of_hit (h : HeapOf H) (e : IC) (b : Value) (k : String)
    (hn : h.icGet e b k ≠ .hole) : h.icMake b k = e := by
  cases b with
  | obj id =>
    cases e with
    | none => exact absurd rfl hn
    | own key ks slot hs hl hkn =>
      simp only [HeapOf.icGet] at hn
      by_cases hkey : (key == k) = true
      · have hk : key = k := beq_iff_eq.mp hkey
        subst hk
        simp only [hkey, ↓reduceIte] at hn
        by_cases hc : ((h.objs.getD id default).kind.icOk && (h.objs.getD id default).props.big.isNone &&
            sameKeys (h.objs.getD id default).props.ks ks) = true
        · simp only [Bool.and_eq_true] at hc
          obtain ⟨⟨hk1, hb1⟩, hs1⟩ := hc
          have hks := sameKeys_eq hs1
          subst hks; subst hs
          unfold HeapOf.icMake
          simp only [hkn, hk1, hb1, Bool.and_self, ↓reduceIte, dif_pos, hl]
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hn; exact absurd rfl hn
      · simp only [hkey, Bool.false_eq_true, ↓reduceIte] at hn; exact absurd rfl hn
    | proto key ks pks slot h0 hs hl hp hkn =>
      simp only [HeapOf.icGet] at hn
      by_cases hkey : (key == k) = true
      · have hk : key = k := beq_iff_eq.mp hkey
        subst hk
        simp only [hkey, ↓reduceIte] at hn
        by_cases hc : ((h.objs.getD id default).kind.icOk && (h.objs.getD id default).props.big.isNone &&
            sameKeys (h.objs.getD id default).props.ks ks) = true
        · simp only [hc, ↓reduceIte] at hn
          simp only [Bool.and_eq_true] at hc
          obtain ⟨⟨hk1, hb1⟩, hs1⟩ := hc
          have hks := sameKeys_eq hs1
          subst hks
          cases hpr : (h.objs.getD id default).proto with
          | obj p =>
            simp only [hpr] at hn
            by_cases hc2 : ((h.objs.getD p default).kind.icOk && (h.objs.getD p default).props.big.isNone &&
                sameKeys (h.objs.getD p default).props.ks pks) = true
            · simp only [Bool.and_eq_true] at hc2
              obtain ⟨⟨hk2, hb2⟩, hs2⟩ := hc2
              have hks2 := sameKeys_eq hs2
              subst hks2; subst hs
              have hnl : ¬ PropMap.scan (h.objs.getD id default).props.ks key 0 < (h.objs.getD id default).props.ks.size := by
                rw [h0]; exact Nat.lt_irrefl _
              unfold HeapOf.icMake
              simp only [hkn, hk1, hb1, Bool.and_self, ↓reduceIte, dif_pos, hnl, dif_neg, not_false_eq_true,
                hp, hpr, hk2, hb2, hl]
            · simp only [hc2, Bool.false_eq_true, ↓reduceIte] at hn; exact absurd rfl hn
          | _ => simp only [hpr] at hn; exact absurd rfl hn
        · simp only [hc, Bool.false_eq_true, ↓reduceIte] at hn; exact absurd rfl hn
      · simp only [hkey, Bool.false_eq_true, ↓reduceIte] at hn; exact absurd rfl hn
  | _ => exact absurd rfl hn

theorem setIfInBounds_self {α} [Inhabited α] (a : Array α) (i : Nat) : a.setIfInBounds i a[i]! = a := by
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi, Array.setIfInBounds, dif_pos hi]; exact Array.set_getElem_self hi
  · exact Array.setIfInBounds_eq_of_size_le (Nat.le_of_not_lt hi)

/-- So a hit's fill leaves the heap as it was. -/
theorem icSet_hit (h : HeapOf H) (site : Nat) (b : Value) (k : String)
    (hn : h.icGet h.icache[site]! b k ≠ .hole) : h.icSet site (h.icMake b k) = h := by
  rw [HeapOf.icSet_eq, icMake_of_hit h _ b k hn, setIfInBounds_self]


/-- **Tier 2, the `getMember` site.** For every slow path, and continuations `c1` (the reference's)
and `c2` (the tier's) with `c1 v` `Le` `c2 v`: the arm's own code is `Le` trying the cache first.
In words: from every heap, either the arm's code runs out of fuel, or asking the cache first ends
exactly as the arm's code does, with the same value and heap. -/
theorem getMember_site {α : Type} (site : Nat) (b : Value) (k : String) (slow : JSM H α)
    (c1 c2 : Value → JSM H α) (hc : ∀ v, Le (c1 v) (c2 v)) (t : Bool) :
    t = false → Le (Tier2.memberGen site b k slow c1)
      (Tier1.attempt (Tier2.getMember? site b k) c2 (Tier2.memberGen site b k slow c1)) := by
  intro _
  unfold Le
  intro s
  by_cases hh : s.icGet s.icache[site]! b k = .hole
  · right
    unfold Tier1.attempt Tier2.getMember?
    simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hh, pure, EStateM.pure]
  · have hf := icGet_sound s _ b k hh
    have hset := icSet_hit s site b k hh
    have hcv := hc (s.icGet s.icache[site]! b k)
    unfold Le at hcv
    rcases hcv s with ho | he
    · left
      unfold Tier2.memberGen
      simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hf]
      have hm : modify (σ := HeapOf H) (m := EStateM Abrupt (HeapOf H)) (fun h => h.icSet site (h.icMake b k)) s
          = EStateM.Result.ok () s := by
        simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, hset]
      split
      · rename_i heq; rw [hm] at heq; cases heq; exact ho
      · rename_i heq; rw [hm] at heq; cases heq
    · right
      unfold Tier2.memberGen Tier1.attempt Tier2.getMember?
      simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, hf, pure, EStateM.pure]
      have hm : modify (σ := HeapOf H) (m := EStateM Abrupt (HeapOf H)) (fun h => h.icSet site (h.icMake b k)) s
          = EStateM.Result.ok () s := by
        simp only [modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, hset]
      split
      · rename_i heq; rw [hm] at heq; cases heq; exact he
      · rename_i heq; rw [hm] at heq; cases heq

#print axioms icGet_sound
#print axioms icSet_hit
#print axioms getMember_site

end L4Factoidal.JS.Tier2Proofs
