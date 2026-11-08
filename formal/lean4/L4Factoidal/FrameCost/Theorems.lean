import L4Factoidal.FrameCost.Model

/-! # Cost theorems of frame scheduling

The lemmas first, then the section `Ratchet`. -/
namespace L4Factoidal.FrameCost

/-! ## Lemmas -/

theorem margin_spec (v : Nat) :
    margin v ≤ 512 ∧ margin v ≤ (4096-v)/2 ∧ (margin v = 512 ∨ margin v = (4096-v)/2) := by
  unfold margin bandMargin maxLayerRows
  rw [Nat.min_def]
  split <;> omega

theorem band_keepFrom (c v : Nat) (tall : v ≤ 3840) : (band c v).keepFrom ≤ c-reach v := by
  have hm := margin_spec v
  unfold Band.keepFrom band reach refreshMargin
  generalize margin v = m at *
  rw [Nat.min_def]
  split <;> (dsimp only; split <;> omega)

theorem band_keepTo (c v : Nat) (tall : v ≤ 3840) : c+reach v ≤ (band c v).keepTo v := by
  have hm := margin_spec v
  unfold Band.keepTo band reach refreshMargin
  generalize margin v = m at *
  rw [Nat.min_def]
  split <;> (dsimp only; omega)

/-- A band made at `c` keeps every scroll within `reach v` rows of `c`. -/
theorem keeps_near (c v s : Nat) (tall : v ≤ 3840) (near : dist s c ≤ reach v) :
    (band c v).keeps v s = true := by
  have lo := band_keepFrom c v tall
  have hi := band_keepTo c v tall
  unfold dist at near
  simp only [Band.keeps, Bool.and_eq_true, decide_eq_true_eq]
  omega

/-- A scroll that a band made at `c` does not keep is more than `reach v` rows from `c`. -/
theorem far_of_not_keeps (c v s : Nat) (tall : v ≤ 3840) (out : (band c v).keeps v s = false) :
    reach v+1 ≤ dist s c := by
  apply Nat.lt_of_not_le
  intro near
  rw [keeps_near c v s tall near] at out
  exact Bool.noConfusion out

theorem keeps_top (b : Band) (v s : Nat) (kept : b.keeps v s = true) : b.top ≤ s := by
  simp only [Band.keeps,Bool.and_eq_true,decide_eq_true_eq] at kept
  have h := kept.1
  unfold Band.keepFrom at h
  split at h <;> omega

theorem keepsFor_some {o : Option (Shown × Band)} {st : Shown} {v s : Nat} (h : keepsFor o st v s = true) :
    ∃ b, o = some (st,b) ∧ b.keeps v s = true := by
  unfold keepsFor at h
  split at h
  · next k b =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨b,by rw [h.1],h.2⟩
  · exact Bool.noConfusion h

/-- Events other than a prefetch leave the bands and the kept layouts as they were. -/
theorem apply_shown (s : Session) (e : Event) : (apply s e).shown = s.shown := by cases e <;> rfl
theorem apply_kept (s : Session) (e : Event) : (apply s e).kept = s.kept := by cases e <;> rfl
theorem apply_prefetched (s : Session) (e : Event) : (apply s e).prefetched = s.prefetched := by cases e <;> rfl

/-- The scroll is not in the key: a scroll leaves the key and the paint as they were. -/
theorem apply_scroll_key (s : Session) (d : Int) : (apply s (.scroll d)).key = s.key := rfl
theorem apply_scroll_state (s : Session) (d : Int) : (apply s (.scroll d)).state = s.state := rfl

/-- A hover whose styles are colours only leaves the key as it was, when no geometry
hover is in it. -/
theorem apply_hover_key (s : Session) (e : Nat) (none : s.key.pointer = 0) : (apply s (.hover e false)).key = s.key := by
  show {s.key with pointer := 0} = s.key
  cases h : s.key; simp_all

theorem commit_key (s : Session) (d : Decision) : (commit s d).key = s.key := by cases d <;> rfl
theorem commit_scroll (s : Session) (d : Decision) : (commit s d).scroll = s.scroll := by cases d <;> rfl
theorem commit_paint (s : Session) (d : Decision) : (commit s d).paint = s.paint := by cases d <;> rfl

/-- Every band on screen or drawn ahead is for a key that is kept, and the memo is a
memo: no key twice, at most `layoutSlots` entries. -/
def Coherent (s : Session) : Prop :=
  (∀ st b, s.shown = some (st,b) → st.1 ∈ Lru.keys s.kept) ∧
  (∀ st b, s.prefetched = some (st,b) → st.1 ∈ Lru.keys s.kept) ∧
  (Lru.keys s.kept).Nodup ∧ s.kept.length ≤ layoutSlots ∧
  (∀ x ∈ Lru.keys s.kept, ∀ y ∈ Lru.keys s.kept, x.page = y.page)

/-- A layout of the current key is kept. -/
def Warm (s : Session) : Prop := s.key ∈ Lru.keys s.kept

theorem warmFor_iff (s : Session) (k : Key) : s.warmFor k = true ↔ k ∈ Lru.keys s.kept := Lru.find?_isSome

theorem start_coherent (key : Key) (limit : Nat) : Coherent (Session.start key limit) :=
  ⟨fun _ _ h => by simp [Session.start] at h,fun _ _ h => by simp [Session.start] at h,
   by simp [Session.start,Lru.keys],by simp [Session.start],by simp [Session.start,Lru.keys]⟩

/-- A step for any event but a prefetch: apply, decide, commit. -/
theorem step_other (s : Session) (e : Event) (p : ¬ ∃ t, e = .prefetch t) :
    step s e = (commit (apply s e) (decideFrame (apply s e)),decideFrame (apply s e),cost (apply s e) (decideFrame (apply s e))) := by
  cases e <;> first | rfl | exact absurd ⟨_,rfl⟩ p

theorem step_prefetch (s : Session) (t : Nat) :
    step s (.prefetch t) = if s.warmFor s.key then ({s with prefetched := some (s.state,band t s.view)},.render,⟨0,1,0⟩) else (s,.shift,0) := rfl

/-- A prefetch keeps the kept layouts, and costs no layout. -/
theorem step_prefetch_kept (s : Session) (t : Nat) :
    (step s (.prefetch t)).1.kept = s.kept ∧ (step s (.prefetch t)).2.2.layouts = 0 := by
  cases hw : s.warmFor s.key <;> simp [step_prefetch,hw]

theorem apply_coherent (s : Session) (e : Event) (h : Coherent s) : Coherent (apply s e) := by
  unfold Coherent
  rw [apply_shown,apply_kept,apply_prefetched]
  exact h

theorem slots_pos : 0 < layoutSlots := by decide

theorem putIn_samePage (m : Lru Key Unit) (k : Key) :
    ∀ x ∈ Lru.keys (Lru.putIn Key.page layoutSlots m k ()), ∀ y ∈ Lru.keys (Lru.putIn Key.page layoutSlots m k ()), x.page = y.page :=
  fun x mx y my => by rw [Lru.scope_putIn Key.page _ _ _ _ x mx,Lru.scope_putIn Key.page _ _ _ _ y my]

theorem commit_coherent (s : Session) (h : Coherent s) : Coherent (commit s (decideFrame s)) := by
  obtain ⟨hs,hp,nd,small,pages⟩ := h
  unfold decideFrame
  split
  · exact ⟨hs,hp,nd,small,pages⟩
  · split
    · exact ⟨fun k b e => hp k b e,fun _ _ e => by simp [commit] at e,nd,small,pages⟩
    · split
      · next warm =>
        have hit := (warmFor_iff s s.key).mp warm
        refine ⟨fun k b e => ?_,fun k b e => ?_,Lru.nodup_putIn _ _ _ nd _ _,Lru.length_putIn_le _ _ _ _ _,putIn_samePage _ _⟩
        · simp only [commit,Option.some.injEq,Prod.mk.injEq] at e
          rw [← e.1]; exact Lru.mem_keys_putIn _ _ slots_pos _ _ _
        · exact Lru.mem_keys_touchIn _ _ _ nd small _ _ hit _ (hp k b e) (pages _ (hp k b e) _ hit)
      · refine ⟨fun k b e => ?_,fun _ _ e => by simp [commit] at e,Lru.nodup_putIn _ _ _ nd _ _,Lru.length_putIn_le _ _ _ _ _,putIn_samePage _ _⟩
        simp only [commit,Option.some.injEq,Prod.mk.injEq] at e
        rw [← e.1]; exact Lru.mem_keys_putIn _ _ slots_pos _ _ _

theorem commit_warm (s : Session) (h : Coherent s) : Warm (commit s (decideFrame s)) := by
  obtain ⟨hs,hp,_,_,_⟩ := h
  unfold Warm
  rw [commit_key]
  unfold decideFrame
  split
  · next free =>
    obtain ⟨b,e,_⟩ := keepsFor_some free
    exact hs _ _ e
  · split
    · next ready =>
      obtain ⟨b,e,_⟩ := keepsFor_some ((Bool.and_eq_true _ _).mp ready).2
      exact hp _ _ e
    · split
      · exact Lru.mem_keys_putIn _ _ slots_pos _ _ _
      · exact Lru.mem_keys_putIn _ _ slots_pos _ _ _

theorem step_coherent (s : Session) (e : Event) (h : Coherent s) : Coherent (step s e).1 := by
  by_cases p : ∃ t, e = .prefetch t
  · obtain ⟨t,rfl⟩ := p
    by_cases warm : s.warmFor s.key = true
    · simp only [step,prefetchStep,warm,↓reduceIte]
      refine ⟨fun k b e => h.1 k b e,fun k b e => ?_,h.2.2.1,h.2.2.2.1,h.2.2.2.2⟩
      simp only [Option.some.injEq,Prod.mk.injEq] at e
      rw [← e.1]
      exact (warmFor_iff s s.key).mp warm
    · simp only [step,prefetchStep,warm,Bool.false_eq_true,↓reduceIte]
      exact h
  · rw [step_other s e p]
    exact commit_coherent _ (apply_coherent _ _ h)

theorem step_warm (s : Session) (e : Event) (h : Coherent s) (w : Warm s) : Warm (step s e).1 := by
  by_cases p : ∃ t, e = .prefetch t
  · obtain ⟨t,rfl⟩ := p
    have warm : s.warmFor s.key = true := (warmFor_iff s s.key).mpr w
    simp only [step,prefetchStep,warm,↓reduceIte]
    exact w
  · rw [step_other s e p]
    exact commit_warm _ (apply_coherent _ _ h)

/-- The cost of a step that is not a layout has no layout in it. -/
theorem cost_layouts (s : Session) (d : Decision) (no : d ≠ .layout) : (cost s d).layouts = 0 := by
  cases d <;> first | rfl | exact absurd rfl no

theorem decide_not_layout (s : Session) (w : Warm s) : decideFrame s ≠ .layout := by
  have warm : s.warmFor s.key = true := (warmFor_iff s s.key).mpr w
  unfold decideFrame
  simp only [warm,↓reduceIte]
  split
  · exact Decision.noConfusion
  · split <;> exact Decision.noConfusion

theorem commit_layouts_le (s s' : Session) (w : Warm s) (kept : s'.kept = s.kept) :
    (cost s' (decideFrame s')).layouts ≤ (if s'.key = s.key then 0 else 1) := by
  by_cases same : s'.key = s.key
  · rw [if_pos same]
    have : Warm s' := by unfold Warm; rw [kept,same]; exact w
    rw [cost_layouts _ _ (decide_not_layout _ this)]
    exact Nat.le_refl 0
  · rw [if_neg same]
    cases decideFrame s' <;> simp [cost]

/-- A step from a warm session lays out only when the event changed the key. -/
theorem step_layouts_le (s : Session) (e : Event) (w : Warm s) :
    (step s e).2.2.layouts ≤ (if (step s e).1.key = s.key then 0 else 1) := by
  by_cases p : ∃ t, e = .prefetch t
  · obtain ⟨t,rfl⟩ := p
    have warm : s.warmFor s.key = true := (warmFor_iff s s.key).mpr w
    simp only [step,prefetchStep,warm,↓reduceIte]
    exact Nat.zero_le _
  · rw [step_other s e p]
    simp only [commit_key]
    exact commit_layouts_le s _ w (apply_kept _ _)

theorem step_layouts_le_one (s : Session) (e : Event) : (step s e).2.2.layouts ≤ 1 := by
  by_cases p : ∃ t, e = .prefetch t
  · obtain ⟨t,rfl⟩ := p
    rw [(step_prefetch_kept s t).2]; exact Nat.zero_le _
  · rw [step_other s e p]
    cases decideFrame (apply s e) <;> simp [cost]

/-- A layout puts a key that was not kept; every other step leaves the kept keys as a
superset (in a window that fits, nothing is dropped). -/
theorem step_window (W : List Key) (fits : W.length ≤ layoutSlots) (page : Nat) (onePage : ∀ x ∈ W, x.page = page)
    (s : Session) (e : Event)
    (h : Coherent s) (sub : ∀ x ∈ Lru.keys s.kept, x ∈ W) (kw : (step s e).1.key ∈ W) :
    (∀ x ∈ Lru.keys (step s e).1.kept, x ∈ W) ∧
    (∀ x ∈ Lru.keys s.kept, x ∈ Lru.keys (step s e).1.kept) ∧
    ((step s e).2.2.layouts = 1 → (step s e).1.key ∉ Lru.keys s.kept ∧ (step s e).1.key ∈ Lru.keys (step s e).1.kept) := by
  obtain ⟨_,_,nd,_,_⟩ := h
  by_cases p : ∃ t, e = .prefetch t
  · obtain ⟨t,rfl⟩ := p
    obtain ⟨kept,zero⟩ := step_prefetch_kept s t
    rw [kept,zero]
    exact ⟨sub,fun _ m => m,fun h => absurd h (by decide)⟩
  · rw [step_other s e p] at kw ⊢
    rw [commit_key] at kw ⊢
    generalize hs' : apply s e = s' at kw ⊢
    have kept' : s'.kept = s.kept := by rw [← hs']; exact apply_kept _ _
    have putSub : ∀ x ∈ Lru.keys (Lru.putIn Key.page layoutSlots s.kept s'.key ()), x ∈ W := by
      intro x mx
      unfold Lru.putIn Lru.put Lru.keys at mx
      rw [List.map_take] at mx
      have mx := List.mem_of_mem_take mx
      simp only [List.map_cons,List.mem_cons] at mx
      rcases mx with e | e
      · exact e ▸ kw
      · apply sub
        have : x ∈ Lru.keys (Lru.without (Lru.inScope Key.page s.kept s'.key) s'.key) := e
        rw [Lru.keys_without,List.mem_filter] at this
        exact ((Lru.mem_keys_inScope Key.page).mp this.1).1
    have keep : ∀ x ∈ Lru.keys s.kept, x ∈ Lru.keys (Lru.putIn Key.page layoutSlots s.kept s'.key ()) :=
      fun x m => Lru.mem_keys_putIn_window Key.page _ W fits page onePage _ nd sub _ _ kw x m
    unfold decideFrame
    split
    · exact ⟨kept' ▸ sub,fun x m => kept' ▸ m,fun h => absurd h (by simp [cost])⟩
    · split
      · exact ⟨by simp only [commit]; exact kept' ▸ sub,fun x m => by simp only [commit]; exact kept' ▸ m,
          fun h => absurd h (by simp [cost])⟩
      · split
        · refine ⟨by simp only [commit,kept']; exact putSub,fun x m => by simp only [commit,kept']; exact keep x m,
            fun h => absurd h (by simp [cost])⟩
        · next cold =>
          refine ⟨by simp only [commit,kept']; exact putSub,fun x m => by simp only [commit,kept']; exact keep x m,
            fun _ => ⟨?_,?_⟩⟩
          · intro m; apply cold; rw [warmFor_iff,kept']; exact m
          · simp only [commit,kept']; exact Lru.mem_keys_putIn _ _ slots_pos _ _ _

/-- `W.countP` of the kept keys goes up by one at a key that comes in. -/
theorem countP_grow (W : List Key) (p q : Key → Bool) (mono : ∀ x ∈ W, p x = true → q x = true)
    (k : Key) (kw : k ∈ W) (np : p k = false) (hq : q k = true) : W.countP p+1 ≤ W.countP q := by
  induction W with
  | nil => simp at kw
  | cons a rest ih =>
    simp only [List.countP_cons]
    have mono' : ∀ x ∈ rest, p x = true → q x = true := fun x m => mono x (List.mem_cons_of_mem _ m)
    have le := List.countP_mono_left mono'
    by_cases ka : k = a
    · subst ka
      simp only [np,hq,Bool.false_eq_true,↓reduceIte]
      omega
    · have := ih mono' (by rcases List.mem_cons.mp kw with h | h; exact absurd h ka; exact h)
      have pa := mono a (List.mem_cons_self ..)
      by_cases ha : p a = true
      · simp only [ha,pa ha,↓reduceIte]; omega
      · simp only [Bool.not_eq_true] at ha
        simp only [ha,Bool.false_eq_true,↓reduceIte]
        split <;> omega

/-- The composite shader: `WebDocument.composite` is this definition (`FrameCost.Band`). -/
example : @composite = @L4Factoidal.FrameCost.composite := rfl

/-! ## Ratchet

These theorems are performance contracts. Each says how much work the hosts do for
an event: Lean layouts, Lean band renders, bytes uploaded. A change that breaks one
must either keep the cost bound, or change the theorem on purpose and say so in the
commit message. A slower path that still gives the right picture is a regression
these theorems are there to stop; `composite_correct` is there so that the cheap path
never gives a different picture. The hosts check the same bounds at run time:
`labs/demos/foafnaut/frame_cost_test.ts` replays the cases of `frame-cost-cases`
through the host functions, `run_html.ts --scroll-sweep` counts Lean calls, and
`frame_work_test.ts` counts the engine's layouts for hover and the request bytes of
held images. -/
section Ratchet

/-- A scroll that keeps the view in the band on screen costs no layout, no render and
no upload: the composite runs at a new offset. -/
theorem scroll_in_band_free (s : Session) (d : Int)
    (inside : keepsFor s.shown s.state s.view (clampScroll s.limit s.scroll d) = true) :
    (step s (.scroll d)).2.2 = 0 := by
  simp only [step,decideFrame]
  have : keepsFor (apply s (.scroll d)).shown (apply s (.scroll d)).state (apply s (.scroll d)).view
      (apply s (.scroll d)).scroll = true := inside
  simp only [this,↓reduceIte]
  rfl

/-- No scroll, of any size, lays the page out, once a layout is kept for the key:
the scroll is not in the key (`apply_scroll_key`; `WebDocument.LayoutKey` has no
scroll field, `WebDocument.layoutKey_scroll`), so the kept layout is the layout of the
key (`WebDocument.lookupLayout_eq`, an instance of `Lru.lookup_eq`). At most a band
is drawn from it. -/
theorem scroll_never_layouts (s : Session) (d : Int) (w : Warm s) :
    (step s (.scroll d)).2.2.layouts = 0 := by
  have := step_layouts_le s (.scroll d) w
  simp only [step,commit_key,apply_scroll_key,↓reduceIte] at this ⊢
  omega

/-- Every session after its first frame is warm, so in any sequence that starts with a
frame no scroll event lays out. -/
theorem run_scrolls_never_layout (es : List Event) :
    ∀ s : Session, Coherent s → Warm s → (∀ e ∈ es, ∃ d, e = .scroll d) → (run s es).2.layouts = 0 := by
  induction es with
  | nil => intro _ _ _ _; rfl
  | cons e es ih =>
    intro s h w all
    obtain ⟨d,rfl⟩ := all _ (List.mem_cons_self ..)
    simp only [run,Cost.add_layouts]
    rw [scroll_never_layouts s d w,ih _ (step_coherent _ _ h) (step_warm _ _ h w)
      (fun e m => all e (List.mem_cons_of_mem _ m))]

/-- Hover and `:active` repaint only: a pointer state whose styles change colours
only (`geometry = false`; `WebRepaint.restyle` answers a scene) costs no layout from a
warm session. The pointer state is not in the key (`WebDocument.layoutKey_pointer`);
the kept layout is restyled and one band is drawn. -/
theorem hover_never_layouts (s : Session) (e : Nat) (w : Warm s) (none : s.key.pointer = 0) :
    (step s (.hover e false)).2.2.layouts = 0 := by
  have := step_layouts_le s (.hover e false) w
  have key : (step s (.hover e false)).1.key = s.key := by
    rw [step_other s _ (by intro ⟨_,h⟩; cases h),commit_key]; exact apply_hover_key s e none
  rw [key] at this
  simp only [↓reduceIte] at this
  omega

/-- The other case, said as such: a pointer state with a style that changes geometry
(`geometry = true`) is in the key, and costs one layout unless a layout of that key is
kept (`layout_once_per_distinct_key` bounds a hover on and off by one). -/
theorem hover_geometry_layouts (s : Session) (e : Nat) :
    (step s (.hover e true)).2.2.layouts ≤
      (if s.warmFor {s.key with pointer := e} then 0 else 1) := by
  rw [step_other s _ (by intro ⟨_,h⟩; cases h)]
  generalize hs' : apply s (.hover e true) = s'
  have key' : s'.key = {s.key with pointer := e} := by rw [← hs']; rfl
  have kept' : s'.kept = s.kept := by rw [← hs']; rfl
  split
  · next warm =>
    have : Warm s' := by unfold Warm; rw [kept',key']; exact (warmFor_iff s _).mp warm
    rw [cost_layouts _ _ (decide_not_layout _ this)]
    exact Nat.le_refl 0
  · cases decideFrame s' <;> simp [cost]

/-- Memo soundness: from a warm session, the layouts of any sequence of events are at
most the events that changed the key. -/
theorem layout_once_per_key (es : List Event) :
    ∀ s : Session, Coherent s → Warm s → (run s es).2.layouts ≤ keyChanges s es := by
  induction es with
  | nil => intro _ _ _; exact Nat.le_refl 0
  | cons e es ih =>
    intro s h w
    simp only [run,keyChanges,Cost.add_layouts]
    have one := step_layouts_le s e w
    have rest := ih (step s e).1 (step_coherent s e h) (step_warm s e h w)
    omega

/-- From any coherent session, the first frame included: at most one more layout. -/
theorem layout_once_per_key_from_start (es : List Event) :
    ∀ s : Session, Coherent s → (run s es).2.layouts ≤ keyChanges s es+1 := by
  induction es with
  | nil => intro _ _; exact Nat.zero_le _
  | cons e es ih =>
    intro s h
    simp only [run,keyChanges,Cost.add_layouts]
    by_cases w : Warm s
    · have := layout_once_per_key (e :: es) s h w
      simp only [run,keyChanges,Cost.add_layouts] at this
      omega
    · by_cases p : ∃ t, e = .prefetch t
      · obtain ⟨t,rfl⟩ := p
        have cold : s.warmFor s.key = false := by
          cases hw : s.warmFor s.key
          · rfl
          · exact absurd ((warmFor_iff s s.key).mp hw) w
        have same : step s (.prefetch t) = (s,.shift,0) := by
          simp only [step,prefetchStep,cold,Bool.false_eq_true,↓reduceIte]
        rw [same]
        have := ih s h
        simp only [↓reduceIte,Cost.zero_layouts]
        omega
      · have one := step_layouts_le_one s e
        have rest := layout_once_per_key es _ (step_coherent s e h) (by
          rw [step_other s e p]; exact commit_warm _ (apply_coherent _ _ h))
        split <;> omega

/-- The memo holds `layoutSlots` layouts, so the bound is by distinct keys, not by key
changes: over any sequence whose keys stay in a window `W` of at most `layoutSlots`
keys of one page (the memo keeps the layouts of one document), each key of `W` is laid out at most once, and not at all when it is kept at the
start. A hover on and off, or a zoom step and back, is one layout. -/
theorem layout_once_per_distinct_key (W : List Key) (fits : W.length ≤ layoutSlots) (page : Nat)
    (onePage : ∀ x ∈ W, x.page = page) (es : List Event) :
    ∀ s : Session, Coherent s → (∀ x ∈ Lru.keys s.kept, x ∈ W) → KeysIn W s es →
      (run s es).2.layouts+W.countP (fun x => decide (x ∈ Lru.keys s.kept)) ≤ W.length := by
  induction es with
  | nil => intro s _ _ _; simp only [run,Cost.zero_layouts,Nat.zero_add]; exact List.countP_le_length
  | cons e es ih =>
    intro s h sub keys
    obtain ⟨kw,rest⟩ := keys
    obtain ⟨sub',keep,lays⟩ := step_window W fits page onePage s e h sub kw
    have more := ih (step s e).1 (step_coherent s e h) sub' rest
    simp only [run,Cost.add_layouts]
    have mono : ∀ x ∈ W, decide (x ∈ Lru.keys s.kept) = true → decide (x ∈ Lru.keys (step s e).1.kept) = true := by
      intro x _ m; simp only [decide_eq_true_eq] at m ⊢; exact keep x m
    have one := step_layouts_le_one s e
    by_cases laid : (step s e).2.2.layouts = 1
    · obtain ⟨out,inn⟩ := lays laid
      have grow := countP_grow W _ _ mono _ kw (by simpa using out) (by simpa using inn)
      omega
    · have := List.countP_mono_left mono
      omega

/-- A scroll-only sequence from a session whose band on screen was made at row `c`,
with no band drawn ahead: the band renders times `reach view + 1` are at most the rows
travelled plus the distance from `c`. -/
theorem band_render_bound_aux (es : List Event) :
    ∀ (s : Session) (c : Nat), (∀ e ∈ es, ∃ d, e = .scroll d) → s.view ≤ 3840 →
      s.shown = some (s.state,band c s.view) → s.prefetched = none → Warm s →
      (run s es).2.renders*(reach s.view+1) ≤ travelled s es+dist s.scroll c := by
  induction es with
  | nil => intro _ _ _ _ _ _ _; simp [run]
  | cons e es ih =>
    intro s c all tall shown none w
    obtain ⟨d,rfl⟩ := all _ (List.mem_cons_self ..)
    have rest_all : ∀ e ∈ es, ∃ d, e = .scroll d := fun e m => all e (List.mem_cons_of_mem _ m)
    simp only [run,travelled,Cost.add_renders,Nat.add_mul]
    -- The session after the scroll, before the decision.
    obtain ⟨s',hs'⟩ : ∃ s', apply s (.scroll d) = s' := ⟨_,rfl⟩
    have key' : s'.key = s.key := by rw [← hs']; rfl
    have state' : s'.state = s.state := by rw [← hs']; rfl
    have shown' : s'.shown = s.shown := by rw [← hs']; exact apply_shown _ _
    have kept' : s'.kept = s.kept := by rw [← hs']; exact apply_kept _ _
    have pre' : s'.prefetched = s.prefetched := by rw [← hs']; exact apply_prefetched _ _
    have view' : s'.view = s.view := by unfold Session.view; rw [key']
    have stepEq : step s (.scroll d) = (commit s' (decideFrame s'),decideFrame s',cost s' (decideFrame s')) := by
      rw [← hs']; rfl
    rw [stepEq]
    have tall' : s'.view ≤ 3840 := view' ▸ tall
    by_cases keep : (band c s.view).keeps s.view s'.scroll = true
    · -- The band on screen keeps the scroll: a shift, and the same band stays.
      have hk : keepsFor s'.shown s'.state s'.view s'.scroll = true := by
        rw [shown',shown,state',view']; simp [keepsFor,keep]
      have free : decideFrame s' = .shift := by
        simp only [decideFrame,hk,↓reduceIte]
      rw [free]
      have := ih s' c rest_all tall' (by rw [shown',state',view']; exact shown) (pre'.trans none)
        (by unfold Warm; rw [kept',key']; exact w)
      simp only [commit,cost,Cost.zero_renders,Nat.zero_mul,view'] at this ⊢
      have tri : dist s'.scroll c ≤ dist s.scroll s'.scroll+dist s.scroll c := by unfold dist; omega
      omega
    · -- A new band, drawn from the kept layout at the new scroll.
      have far := far_of_not_keeps c s.view s'.scroll tall (by simpa using keep)
      have hk : keepsFor s'.shown s'.state s'.view s'.scroll = false := by
        rw [shown',shown,state',view']; simpa [keepsFor] using keep
      have hp : (shownFor s'.shown s'.state && keepsFor s'.prefetched s'.state s'.view s'.scroll) = false := by
        rw [pre',none]; simp [keepsFor]
      have hw : s'.warmFor s'.key = true := by rw [warmFor_iff,kept',key']; exact w
      have drawn : decideFrame s' = .render := by
        simp only [decideFrame,hk,hp,hw,Bool.false_eq_true,↓reduceIte]
      rw [drawn]
      have := ih (commit s' .render) s'.scroll rest_all tall' rfl (pre'.trans none)
        (by unfold Warm; simp only [commit]; exact Lru.mem_keys_putIn _ _ slots_pos _ _ _)
      have zero : dist (commit s' .render).scroll s'.scroll = 0 := by
        rw [commit_scroll]; unfold dist; omega
      have v : (commit s' .render).view = s.view := by
        unfold Session.view; rw [commit_key]; exact view'
      rw [zero,v] at this
      simp only [cost,Nat.one_mul,commit_scroll] at this ⊢
      have tri : dist s'.scroll c ≤ dist s.scroll s'.scroll+dist s.scroll c := by unfold dist; omega
      omega

/-- Band renders per row of scroll: a scroll-only sequence that starts on a band made at
its own scroll draws at most `travelled / (reach view + 1)` new bands, each from the
kept layout. For a view of up to 3072 rows the reach is 384: at most one band per 385
rows. With the prefetch, bands are 768 rows apart (`prefetch_band_spacing`). -/
theorem band_render_bound (s : Session) (es : List Event) (all : ∀ e ∈ es, ∃ d, e = .scroll d)
    (tall : s.view ≤ 3840) (shown : s.shown = some (s.state,band s.scroll s.view))
    (none : s.prefetched = none) (w : Warm s) :
    (run s es).2.renders ≤ travelled s es/(reach s.view+1) := by
  have := band_render_bound_aux es s s.scroll all tall shown none w
  have zero : dist s.scroll s.scroll = 0 := by unfold dist; omega
  rw [zero,Nat.add_zero] at this
  exact (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr this

/-- The prefetch rule makes bands `2 * reach` rows apart, 768 rows for a view of up to
3072 rows: a band made at `c` (at least a margin from the top) keeps the scrolls up to
`c + reach`; when the scroll comes within `prefetchMargin` rows of that, the rule asks
for the band at `c + 2 * reach`, whose keep range starts where this one ends and ends
`2 * reach` rows further. So a steady scroll draws one band per 768 rows, each ahead of
time, and none on demand. -/
theorem prefetch_band_spacing (c v scroll limit : Nat) (tall : v ≤ 3072) (low : 512 < c)
    (near : (band c v).keepTo v-prefetchMargin ≤ scroll) (inside : scroll ≤ (band c v).keepTo v)
    (room : c+2*reach v ≤ limit) :
    prefetchTarget (band c v) v scroll limit true = some (c+2*reach v) ∧
    (band (c+2*reach v) v).keepFrom = (band c v).keepTo v ∧
    (band (c+2*reach v) v).keepTo v = (band c v).keepTo v+2*reach v ∧
    reach v = 384 := by
  have m : margin v = 512 := by unfold margin bandMargin maxLayerRows; rw [Nat.min_def]; split <;> omega
  have r : reach v = 384 := by unfold reach refreshMargin; rw [m]
  have kt : (band c v).keepTo v = c+384 := by
    unfold Band.keepTo band refreshMargin; rw [m]; dsimp only; rw [Nat.min_def]; split <;> omega
  have kf : (band c v).keepFrom = c-384 := by
    unfold Band.keepFrom band refreshMargin; rw [m]; dsimp only; rw [Nat.min_def]; split <;> split <;> omega
  rw [kt] at near inside ⊢
  rw [r] at room ⊢
  refine ⟨?_,?_,?_,rfl⟩
  · unfold prefetchTarget
    rw [kf,kt,r]
    have a : ¬ (scroll < c-384 ∨ c+384 < scroll ∨ (384:Nat) = 0) := by unfold prefetchMargin at near; omega
    have b : ¬ (limit ≤ c+384 ∨ prefetchMargin < c+384-scroll) := by unfold prefetchMargin at near ⊢; omega
    simp only [a,b,↓reduceIte,Option.some.injEq]
    omega
  · unfold Band.keepFrom band refreshMargin; rw [m]; dsimp only; rw [Nat.min_def]; split <;> split <;> omega
  · unfold Band.keepTo band refreshMargin; rw [m]; dsimp only; rw [Nat.min_def]; split <;> omega

/-- The chain of prefetched bands of a steady scroll down from a band at `c`: the
`n`-th is made at `c + 768 n` and keeps the scrolls up to `c + 384 + 768 n`; each
starts its keep range where the one before ends. -/
theorem prefetch_chain (c v n : Nat) (tall : v ≤ 3072) (low : 512 ≤ c) :
    (band (c+768*n) v).keepTo v = c+384+768*n ∧
    (band (c+768*(n+1)) v).keepFrom = (band (c+768*n) v).keepTo v := by
  have m : margin v = 512 := by unfold margin bandMargin maxLayerRows; rw [Nat.min_def]; split <;> omega
  constructor
  · unfold Band.keepTo band refreshMargin; rw [m]; dsimp only; rw [Nat.min_def]; split <;> omega
  · unfold Band.keepFrom Band.keepTo band refreshMargin; rw [m]; dsimp only
    rw [Nat.min_def,Nat.min_def]; split <;> split <;> split <;> omega

/-- The cheap path gives the picture of the expensive one: for every scroll that the
band on screen keeps, the composite at offset `scroll - band.top` is the frame that a
full render at `scroll` describes. -/
theorem composite_correct {α : Type} (image chrome : Nat → Nat → α) (b : Band) (top view scroll x y : Nat)
    (kept : b.keeps view scroll = true) :
    composite chrome (fun x row => image x (row+b.top)) top (scroll-b.top) x y =
      if y < top then chrome x y else image x (y-top+scroll) :=
  composite_eq_frame image chrome b top scroll x y (keeps_top b view scroll kept)

/-- A timer tick with no DOM change costs nothing when the band on screen keeps the
scroll (after any frame of a view of up to 3840 rows it does). -/
theorem tick_free (s : Session) (kept : keepsFor s.shown s.state s.view s.scroll = true) :
    step s .tick = (s,.shift,0) := by
  have free : decideFrame s = .shift := by simp only [decideFrame,kept,↓reduceIte]
  show (commit s (decideFrame s),decideFrame s,cost s (decideFrame s)) = (s,.shift,0)
  rw [free]; rfl

/-- A prefetch never lays out: it draws one band from the kept layout, or nothing. -/
theorem prefetch_never_layouts (s : Session) (t : Nat) : (step s (.prefetch t)).2.2.layouts = 0 :=
  (step_prefetch_kept s t).2

end Ratchet

/-! ## The costs that the ratchet of 2026-11-08 lowered

Before: a hover change was a layout (`hover`, `active` were in
`WebDocument.layoutFields`), and the kept layout was one entry, so a hover on and off
was two layouts. Now both are zero for a colour-only hover, and one for a hover that
changes geometry. -/

/-- A colour-only hover on and off, from a warm session: no layout, two renders. -/
theorem hover_on_off_paint :
    let k : Key := ⟨0,800,600,80,100,0,0,0⟩
    let s : Session := {key := k, paint := 0, scroll := 0, limit := 4000, shown := some ((k,0),band 0 520), kept := [(k,())], prefetched := none}
    (run s [.hover 1 false,.hover 0 false]).2 = ⟨0,2,2*bandBytes 800 (band 0 520)⟩ := by
  decide

/-- A hover that changes geometry, on and off: one layout (the memo keeps both keys). -/
theorem hover_on_off_geometry :
    let k : Key := ⟨0,800,600,80,100,0,0,0⟩
    let s : Session := {key := k, paint := 0, scroll := 0, limit := 4000, shown := some ((k,0),band 0 520), kept := [(k,())], prefetched := none}
    (run s [.hover 1 true,.hover 0 false,.hover 1 true]).2.layouts = 1 := by
  decide

end L4Factoidal.FrameCost
