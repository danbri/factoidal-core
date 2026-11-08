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

theorem keepsFor_some {o : Option (Key × Band)} {k : Key} {v s : Nat} (h : keepsFor o k v s = true) :
    ∃ b, o = some (k,b) ∧ b.keeps v s = true := by
  unfold keepsFor at h
  split at h
  · next k' b =>
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨b,by rw [h.1],h.2⟩
  · exact Bool.noConfusion h

/-- Events other than a prefetch leave the bands and the kept entry as they were. -/
theorem apply_shown (s : Session) (e : Event) : (apply s e).shown = s.shown := by cases e <;> rfl
theorem apply_kept (s : Session) (e : Event) : (apply s e).kept = s.kept := by cases e <;> rfl
theorem apply_prefetched (s : Session) (e : Event) : (apply s e).prefetched = s.prefetched := by cases e <;> rfl

/-- The scroll is not in the key: a scroll leaves the key as it was. -/
theorem apply_scroll_key (s : Session) (d : Int) : (apply s (.scroll d)).key = s.key := rfl

theorem commit_key (s : Session) (d : Decision) : (commit s d).key = s.key := by cases d <;> rfl
theorem commit_scroll (s : Session) (d : Decision) : (commit s d).scroll = s.scroll := by cases d <;> rfl

/-- Every band on screen or drawn ahead is for the key of the kept layout. -/
def Coherent (s : Session) : Prop :=
  (∀ k b, s.shown = some (k,b) → s.kept = some k) ∧ (∀ k b, s.prefetched = some (k,b) → s.kept = some k)

/-- The kept layout is the layout of the current key. -/
def Warm (s : Session) : Prop := s.kept = some s.key

theorem start_coherent (key : Key) (limit : Nat) : Coherent (Session.start key limit) :=
  ⟨fun _ _ h => by simp [Session.start] at h,fun _ _ h => by simp [Session.start] at h⟩

/-- A step for any event but a prefetch: apply, decide, commit. -/
theorem step_other (s : Session) (e : Event) (p : ¬ ∃ t, e = .prefetch t) :
    step s e = (commit (apply s e) (decideFrame (apply s e)),decideFrame (apply s e),cost (apply s e) (decideFrame (apply s e))) := by
  cases e <;> first | rfl | exact absurd ⟨_,rfl⟩ p

theorem apply_coherent (s : Session) (e : Event) (h : Coherent s) : Coherent (apply s e) := by
  unfold Coherent
  rw [apply_shown,apply_kept,apply_prefetched]
  exact h

theorem commit_coherent (s : Session) (h : Coherent s) : Coherent (commit s (decideFrame s)) := by
  obtain ⟨hs,hp⟩ := h
  unfold decideFrame
  split
  · exact ⟨hs,hp⟩
  · split
    · exact ⟨fun k b e => hp k b e,fun _ _ e => by simp [commit] at e⟩
    · split
      · next warm =>
        refine ⟨fun k b e => ?_,hp⟩
        simp only [commit,Option.some.injEq,Prod.mk.injEq] at e
        rw [← e.1]; exact warm
      · refine ⟨fun k b e => ?_,fun _ _ e => by simp [commit] at e⟩
        simp only [commit,Option.some.injEq,Prod.mk.injEq] at e
        simp only [commit,e.1]

theorem commit_warm (s : Session) (h : Coherent s) : Warm (commit s (decideFrame s)) := by
  obtain ⟨hs,hp⟩ := h
  unfold Warm
  rw [commit_key]
  unfold decideFrame
  split
  · next free =>
    obtain ⟨b,e,_⟩ := keepsFor_some free
    exact hs _ _ e
  · split
    · next ready =>
      obtain ⟨b,e,_⟩ := keepsFor_some ready
      exact hp _ _ e
    · split
      · next warm => exact warm
      · rfl

theorem step_coherent (s : Session) (e : Event) (h : Coherent s) : Coherent (step s e).1 := by
  by_cases p : ∃ t, e = .prefetch t
  · obtain ⟨t,rfl⟩ := p
    by_cases warm : s.kept = some s.key
    · simp only [step,prefetchStep,if_pos warm]
      refine ⟨fun k b e => h.1 k b e,fun k b e => ?_⟩
      simp only [Option.some.injEq,Prod.mk.injEq] at e
      obtain ⟨rfl,-⟩ := e
      exact warm
    · simp only [step,prefetchStep,if_neg warm]
      exact h
  · rw [step_other s e p]
    exact commit_coherent _ (apply_coherent _ _ h)

theorem step_warm (s : Session) (e : Event) (h : Coherent s) (w : Warm s) : Warm (step s e).1 := by
  by_cases p : ∃ t, e = .prefetch t
  · obtain ⟨t,rfl⟩ := p
    simp only [step,prefetchStep,if_pos (show s.kept = some s.key from w)]
    exact w
  · rw [step_other s e p]
    exact commit_warm _ (apply_coherent _ _ h)

/-- The cost of a step that is not a layout has no layout in it. -/
theorem cost_layouts (s : Session) (d : Decision) (no : d ≠ .layout) : (cost s d).layouts = 0 := by
  cases d <;> first | rfl | exact absurd rfl no

theorem decide_not_layout (s : Session) (w : Warm s) : decideFrame s ≠ .layout := by
  unfold decideFrame
  split
  · exact Decision.noConfusion
  · split
    · exact Decision.noConfusion
    · split
      · exact Decision.noConfusion
      · next cold => exact absurd w cold

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
    simp only [step,prefetchStep,if_pos (show s.kept = some s.key from w)]
    exact Nat.zero_le _
  · rw [step_other s e p]
    simp only [commit_key]
    exact commit_layouts_le s _ w (apply_kept _ _)

theorem step_layouts_le_one (s : Session) (e : Event) : (step s e).2.2.layouts ≤ 1 := by
  by_cases p : ∃ t, e = .prefetch t
  · obtain ⟨t,rfl⟩ := p
    by_cases warm : s.kept = some s.key
    · simp only [step,prefetchStep,if_pos warm]; exact Nat.zero_le _
    · simp only [step,prefetchStep,if_neg warm]; exact Nat.zero_le _
  · rw [step_other s e p]
    cases decideFrame (apply s e) <;> simp [cost]

/-- The composite shader: `WebDocument.composite`. -/
def composite {α : Type} (chrome page : Nat → Nat → α) (top offset x y : Nat) : α :=
  if y < top then chrome x y else page x (y-top+offset)

/-- `WebDocument.composite_eq_frame`, the same statement and proof. -/
theorem composite_eq_frame {α : Type} (image chrome : Nat → Nat → α) (b : Band) (top scroll x y : Nat)
    (inside : b.top ≤ scroll) :
    composite chrome (fun x row => image x (row+b.top)) top (scroll-b.top) x y =
      if y < top then chrome x y else image x (y-top+scroll) := by
  unfold composite
  split
  · rfl
  · dsimp only
    rw [show y-top+(scroll-b.top)+b.top = y-top+scroll by omega]

/-! ## Ratchet

These theorems are performance contracts. Each says how much work the hosts do for
an event: Lean layouts, Lean band renders, bytes uploaded. A change that breaks one
must either keep the cost bound, or change the theorem on purpose and say so in the
commit message. A slower path that still gives the right picture is a regression
these theorems are there to stop; `composite_correct` is there so that the cheap path
never gives a different picture. The hosts check the same bounds at run time:
`labs/demos/foafnaut/frame_cost_test.ts` replays the cases of `frame-cost-cases`
through the host functions, and `run_html.ts --scroll-sweep` counts Lean calls. -/
section Ratchet

/-- A scroll that keeps the view in the band on screen costs no layout, no render and
no upload: the composite runs at a new offset. -/
theorem scroll_in_band_free (s : Session) (d : Int)
    (inside : keepsFor s.shown s.key s.view (clampScroll s.limit s.scroll d) = true) :
    (step s (.scroll d)).2.2 = 0 := by
  simp only [step,decideFrame]
  have : keepsFor (apply s (.scroll d)).shown (apply s (.scroll d)).key (apply s (.scroll d)).view
      (apply s (.scroll d)).scroll = true := inside
  simp only [this,↓reduceIte]
  rfl

/-- No scroll, of any size, lays the page out, once a layout is kept for the key:
the scroll is not in the key (`apply_scroll_key`; `WebDocument.LayoutKey` has no
scroll field), so the kept layout is the layout of the key (`WebDocument.lookupLayout_eq`
is the same statement for the engine's cache). At most a band is drawn from it. -/
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

/-- Memo soundness: from a warm session, the layouts of any sequence of events are at
most the events that changed the key. The cache holds one entry, so this is a bound
by key changes, not by distinct keys: `one_entry_relayouts` shows a key seen before
is laid out again. -/
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
        have same : step s (.prefetch t) = (s,.shift,0) := by
          simp only [step,prefetchStep,if_neg (show ¬ s.kept = some s.key from w)]
        rw [same]
        have := ih s h
        simp only [↓reduceIte,Cost.zero_layouts]
        omega
      · have one := step_layouts_le_one s e
        have rest := layout_once_per_key es _ (step_coherent s e h) (by
          rw [step_other s e p]; exact commit_warm _ (apply_coherent _ _ h))
        split <;> omega

/-- A scroll-only sequence from a session whose band on screen was made at row `c`,
with no band drawn ahead: the band renders times `reach view + 1` are at most the rows
travelled plus the distance from `c`. -/
theorem band_render_bound_aux (es : List Event) :
    ∀ (s : Session) (c : Nat), (∀ e ∈ es, ∃ d, e = .scroll d) → s.view ≤ 3840 →
      s.shown = some (s.key,band c s.view) → s.prefetched = none → Warm s →
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
    have shown' : s'.shown = s.shown := by rw [← hs']; exact apply_shown _ _
    have kept' : s'.kept = s.kept := by rw [← hs']; exact apply_kept _ _
    have pre' : s'.prefetched = s.prefetched := by rw [← hs']; exact apply_prefetched _ _
    have view' : s'.view = s.view := by unfold Session.view; rw [key']
    have stepEq : step s (.scroll d) = (commit s' (decideFrame s'),decideFrame s',cost s' (decideFrame s')) := by
      rw [← hs']; rfl
    rw [stepEq]
    have tri : dist s'.scroll c ≤ dist s.scroll s'.scroll+dist s.scroll c := by unfold dist; omega
    have tall' : s'.view ≤ 3840 := view' ▸ tall
    by_cases keep : (band c s.view).keeps s.view s'.scroll = true
    · -- The band on screen keeps the scroll: a shift, and the same band stays.
      have hk : keepsFor s'.shown s'.key s'.view s'.scroll = true := by
        rw [shown',shown,key',view']; simp [keepsFor,keep]
      have free : decideFrame s' = .shift := by
        simp only [decideFrame,hk,↓reduceIte]
      rw [free]
      have := ih s' c rest_all tall' (by rw [shown',key',view']; exact shown) (pre'.trans none)
        (by unfold Warm; rw [kept',key']; exact w)
      simp only [commit,cost,Cost.zero_renders,Nat.zero_mul,view'] at this ⊢
      omega
    · -- A new band, drawn from the kept layout at the new scroll.
      have far := far_of_not_keeps c s.view s'.scroll tall (by simpa using keep)
      have hk : keepsFor s'.shown s'.key s'.view s'.scroll = false := by
        rw [shown',shown,key',view']; simpa [keepsFor] using keep
      have hp : keepsFor s'.prefetched s'.key s'.view s'.scroll = false := by
        rw [pre',none]; rfl
      have hw : s'.kept = some s'.key := by rw [kept',key']; exact w
      have drawn : decideFrame s' = .render := by
        simp only [decideFrame,hk,hp,hw,Bool.false_eq_true,↓reduceIte]
      rw [drawn]
      have := ih (commit s' .render) s'.scroll rest_all tall' rfl (pre'.trans none)
        (show s'.kept = some s'.key by rw [kept',key']; exact w)
      have zero : dist (commit s' .render).scroll s'.scroll = 0 := by
        rw [commit_scroll]; unfold dist; omega
      have v : (commit s' .render).view = s.view := by
        unfold Session.view; rw [commit_key]; exact view'
      rw [zero,v] at this
      simp only [cost,Nat.one_mul,commit_scroll] at this ⊢
      omega

/-- Band renders per row of scroll: a scroll-only sequence that starts on a band made at
its own scroll draws at most `travelled / (reach view + 1)` new bands, each from the
kept layout. For a view of up to 3072 rows the reach is 384: at most one band per 385
rows. (A band is `view + 1024` rows, but the host asks for a new one when the view is
128 rows from an edge, and a band drawn on demand is centred on the scroll, so the
rows between two such bands are `reach + 1`, not the band height less the view.) -/
theorem band_render_bound (s : Session) (es : List Event) (all : ∀ e ∈ es, ∃ d, e = .scroll d)
    (tall : s.view ≤ 3840) (shown : s.shown = some (s.key,band s.scroll s.view))
    (none : s.prefetched = none) (w : Warm s) :
    (run s es).2.renders ≤ travelled s es/(reach s.view+1) := by
  have := band_render_bound_aux es s s.scroll all tall shown none w
  have zero : dist s.scroll s.scroll = 0 := by unfold dist; omega
  rw [zero,Nat.add_zero] at this
  exact (Nat.le_div_iff_mul_le (Nat.succ_pos _)).mpr this

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
theorem tick_free (s : Session) (kept : keepsFor s.shown s.key s.view s.scroll = true) :
    step s .tick = (s,.shift,0) := by
  have free : decideFrame s = .shift := by simp only [decideFrame,kept,↓reduceIte]
  show (commit s (decideFrame s),decideFrame s,cost s (decideFrame s)) = (s,.shift,0)
  rw [free]; rfl

/-- A prefetch never lays out: it draws one band from the kept layout, or nothing. -/
theorem prefetch_never_layouts (s : Session) (t : Nat) : (step s (.prefetch t)).2.2.layouts = 0 := by
  by_cases warm : s.kept = some s.key
  · simp only [step,prefetchStep,if_pos warm]
  · simp only [step,prefetchStep,if_neg warm]; rfl

end Ratchet

/-! ## Costs today that a later ratchet is to lower

These say what the hosts do now, so that the change that makes them cheaper must
change the theorem. -/

/-- A hover, active or visited change lays the page out again today: those fields are
in `WebDocument.layoutFields`. The next ratchet is a repaint with no layout. -/
theorem element_change_lays_out (s : Session) (e : Nat) (h : Coherent s) (w : Warm s)
    (other : e ≠ s.key.element) : (step s (.element e)).2.2.layouts = 1 := by
  simp only [step]
  have new : (apply s (.element e)).key ≠ s.key := by
    intro same
    exact other (congrArg Key.element same)
  have lay : decideFrame (apply s (.element e)) = .layout := by
    unfold decideFrame
    rw [apply_shown,apply_prefetched,apply_kept,w]
    have notFor : ∀ o : Option (Key × Band), (∀ k b, o = some (k,b) → s.kept = some k) →
        ∀ v r, keepsFor o (apply s (.element e)).key v r = false := by
      intro o ho v r
      unfold keepsFor
      split
      · next k b =>
        have := ho k b rfl
        rw [w,Option.some.injEq] at this
        rw [← this]
        simp [Ne.symm new]
      · rfl
    rw [notFor _ h.1,notFor _ h.2]
    simp only [Bool.false_eq_true,↓reduceIte,Option.some.injEq]
    rw [if_neg (Ne.symm new)]
  rw [lay]
  rfl

/-- The kept layout is one entry: going to a key and back lays out twice. A memo of
more entries would make this one layout; `layout_once_per_key` would then become a
bound by distinct keys. -/
theorem one_entry_relayouts :
    let k : Key := ⟨0,800,600,80,100,0,0⟩
    let s : Session := {key := k, scroll := 0, limit := 4000, shown := some (k,band 0 520), kept := some k, prefetched := none}
    (run s [.element 1,.element 0]).2.layouts = 2 := by
  decide

end L4Factoidal.FrameCost
