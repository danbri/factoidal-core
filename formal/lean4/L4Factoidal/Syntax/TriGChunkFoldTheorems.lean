/-
L4Factoidal.Syntax.TriGChunkFoldTheorems — what is proved about the TriG
chunk walk (https://github.com/danbri/factoidal/issues/769).

PROVED here:

1. `feed_split`: feeding two chunks one after the other is the same as feeding
   their concatenation, for EVERY state and EVERY cut of the input. This is the
   chunk-boundary half that `Syntax.TurtleChunkFold` states only in prose.
2. Graph-block state: the block flag of the fold equals the brace depth of the
   scanner at every chunk boundary (`feed_inv`), and braces open and close in
   strict alternation (`scan_events_sim`); an input that ends inside a block is
   refused by `finish` (`finish_unterminated`).
3. Graph label: inside a block, every step call of a statement carries the
   label fixed when the block opened (`consumeBlock_graphs`,
   `applyEvent_stmt_graphs`, `applyEvent_close_graphs`), and a statement unit
   leaves the block state unchanged (`applyEvent_stmt_block`).

NOT proved: that the walk returns `parseTriG`'s quads (that the scanner units
agree with the statements of `readTriGStatement`). Tracked in
https://github.com/danbri/factoidal/issues/836; the agreement is MEASURED
(`docs/designissues/2026-09-03-rdf-parsing-strategy.md`).
-/
import L4Factoidal.Syntax.TriGChunkFold

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## The inner scanner: completed candidates are write-only -/

/-- `StatementScan.feedChar` never reads `completedRev`: the fields other than
`completedRev` are those of the same step from a cleared queue, and the queue
grows by exactly what that step completes. -/
theorem StatementScan.feedChar_cleared (i : StatementScan) (c : Char) :
    (i.feedChar c).completedRev = ({ i with completedRev := [] }.feedChar c).completedRev ++ i.completedRev
    ∧ (i.feedChar c).mode = ({ i with completedRev := [] }.feedChar c).mode
    ∧ (i.feedChar c).pendingDot = ({ i with completedRev := [] }.feedChar c).pendingDot
    ∧ (i.feedChar c).currentRev = ({ i with completedRev := [] }.feedChar c).currentRev
    ∧ (i.feedChar c).head = ({ i with completedRev := [] }.feedChar c).head := by
  unfold StatementScan.feedChar
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-! ## The TriG scanner: pending units and the cleared scanner -/

/-- All units the scanner holds and has not handed over, newest first. -/
def TriGScan.pend (s : TriGScan) : List TriGEvent :=
  s.inner.completedRev.map TriGEvent.stmt ++ s.eventsRev

/-- The scanner with nothing pending. -/
def TriGScan.clear (s : TriGScan) : TriGScan :=
  { s with inner := { s.inner with completedRev := [] }, eventsRev := [] }

theorem TriGScan.pend_clear (s : TriGScan) : s.clear.pend = [] := by
  simp [TriGScan.pend, TriGScan.clear]

theorem TriGScan.clear_clear (s : TriGScan) : s.clear.clear = s.clear := rfl

theorem TriGScan.inBlock_clear (s : TriGScan) : s.clear.inBlock = s.inBlock := rfl

theorem TriGScan.drain_eq (s : TriGScan) : s.drain = (s.pend.reverse, s.clear) := by
  simp [TriGScan.drain, TriGScan.flushInner, TriGScan.pend, TriGScan.clear]

theorem TriGScan.feedChar_split (s : TriGScan) (c : Char) :
    (s.feedChar c).pend = (s.clear.feedChar c).pend ++ s.pend
    ∧ (s.feedChar c).clear = (s.clear.feedChar c).clear := by
  obtain ⟨h1, hm, hp, hc, hh⟩ := StatementScan.feedChar_cleared s.inner c
  unfold TriGScan.feedChar
  by_cases he : s.escaped = true
  · simp only [he, if_true, TriGScan.pend, TriGScan.clear]
    simp [h1, hc, hh]
  · by_cases hb : (s.inner.mode == ScanMode.normal) = true ∧
        ((c = '{' ∧ s.inBlock = false) ∨ (c = '}' ∧ s.inBlock = true))
    · simp [he, hb, TriGScan.pend, TriGScan.clear, TriGScan.flushInner]
    · simp [he, hb, TriGScan.pend, TriGScan.clear, h1, hm, hp, hc, hh]

theorem TriGScan.feedChars_split (cs : List Char) :
    ∀ s : TriGScan, (s.feedChars cs).pend = (s.clear.feedChars cs).pend ++ s.pend
      ∧ (s.feedChars cs).clear = (s.clear.feedChars cs).clear := by
  induction cs with
  | nil => intro s; simp [TriGScan.feedChars, TriGScan.pend_clear, TriGScan.clear_clear]
  | cons c cs ih =>
      intro s
      obtain ⟨hp, hc⟩ := TriGScan.feedChar_split s c
      obtain ⟨ip, ic⟩ := ih (s.feedChar c)
      obtain ⟨jp, jc⟩ := ih (s.clear.feedChar c)
      simp only [TriGScan.feedChars]
      have hcl : (s.feedChar c).clear.feedChars cs = (s.clear.feedChar c).clear.feedChars cs := by
        rw [hc]
      refine ⟨?_, ?_⟩
      · rw [ip, hcl, jp, hp]
        simp [List.append_assoc]
      · rw [ic, hcl, jc]

theorem TriGScan.feedChars_append (s : TriGScan) (xs ys : List Char) :
    s.feedChars (xs ++ ys) = (s.feedChars xs).feedChars ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons c xs ih => exact ih (s.feedChar c)

theorem TriGScan.feed_append (s : TriGScan) (a b : String) :
    s.feed (a ++ b) = (s.feed a).feed b := by
  simp [TriGScan.feed, String.toList_append, TriGScan.feedChars_append]

/-- Draining after two chunks, with a drain in between, hands over the same
units in the same order as one drain after the concatenation, and leaves the
same scanner. -/
theorem TriGScan.drain_feed_split (s : TriGScan) (a b : String) :
    (s.feed (a ++ b)).drain =
      ((s.feed a).drain.1 ++ (((s.feed a).drain.2).feed b).drain.1,
       (((s.feed a).drain.2).feed b).drain.2) := by
  have h : ((s.feed a).feed b).pend = ((s.feed a).clear.feed b).pend ++ (s.feed a).pend
      ∧ ((s.feed a).feed b).clear = ((s.feed a).clear.feed b).clear :=
    TriGScan.feedChars_split b.toList (s.feed a)
  rw [TriGScan.feed_append, TriGScan.drain_eq, TriGScan.drain_eq, TriGScan.drain_eq, h.1, h.2]
  simp [List.reverse_append]

/-! ## The fold: applying units -/

theorem applyEvents_append (step : α → Option Subject → List Triple → α) :
    ∀ (xs ys : List TriGEvent) (st : TriGChunkFoldState α),
      applyEvents step st (xs ++ ys) = (applyEvents step st xs).bind (fun s => applyEvents step s ys) := by
  intro xs
  induction xs with
  | nil => intro ys st; rfl
  | cons e es ih =>
      intro ys st
      simp only [List.cons_append, applyEvents]
      cases applyEvent step st e with
      | error x => rfl
      | ok s0 => exact ih ys s0

/-- A unit does not read the scanner of the state. -/
theorem applyEvent_withScanner (step : α → Option Subject → List Triple → α)
    (st : TriGChunkFoldState α) (sc : TriGScan) (ev : TriGEvent) :
    applyEvent step { st with scanner := sc } ev =
      (applyEvent step st ev).map (fun s => { s with scanner := sc }) := by
  rcases st with ⟨t, a, p, b, sc0⟩
  cases ev with
  | stmt text =>
      cases b <;> simp only [applyEvent] <;> split <;> rfl
  | blockOpen header =>
      simp only [applyEvent]; split <;> rfl
  | blockClose rest =>
      cases b <;> simp only [applyEvent]
      · rfl
      · split <;> rfl

theorem applyEvent_scanner (step : α → Option Subject → List Triple → α)
    (st s : TriGChunkFoldState α) (ev : TriGEvent)
    (h : applyEvent step st ev = .ok s) : s.scanner = st.scanner := by
  rcases st with ⟨t, a, p, b, sc0⟩
  cases ev with
  | stmt text =>
      cases b <;> simp only [applyEvent] at h <;> split at h <;>
        first | (injection h with h; subst h; rfl) | (cases h)
  | blockOpen header =>
      simp only [applyEvent] at h; split at h <;>
        first | (injection h with h; subst h; rfl) | (cases h)
  | blockClose rest =>
      cases b <;> simp only [applyEvent] at h
      · cases h
      · split at h <;> first | (injection h with h; subst h; rfl) | (cases h)

theorem applyEvents_withScanner (step : α → Option Subject → List Triple → α) :
    ∀ (evs : List TriGEvent) (st : TriGChunkFoldState α) (sc : TriGScan),
      applyEvents step { st with scanner := sc } evs =
        (applyEvents step st evs).map (fun s => { s with scanner := sc }) := by
  intro evs
  induction evs with
  | nil => intro st sc; rfl
  | cons e es ih =>
      intro st sc
      simp only [applyEvents, applyEvent_withScanner]
      cases hr : applyEvent step st e with
      | error x => rfl
      | ok s0 => exact ih s0 sc

theorem applyEvents_scanner (step : α → Option Subject → List Triple → α) :
    ∀ (evs : List TriGEvent) (st s : TriGChunkFoldState α),
      applyEvents step st evs = .ok s → s.scanner = st.scanner := by
  intro evs
  induction evs with
  | nil => intro st s h; injection h with h; subst h; rfl
  | cons e es ih =>
      intro st s h
      simp only [applyEvents] at h
      cases hr : applyEvent step st e with
      | error x => rw [hr] at h; cases h
      | ok s0 =>
          rw [hr] at h
          rw [ih s0 s h, applyEvent_scanner step st s0 e hr]

/-- THE CHUNK-BOUNDARY THEOREM. Feeding two chunks one after the other gives
the result of feeding their concatenation, for every state and every cut. -/
theorem TriGChunkFoldState.feed_split (step : α → Option Subject → List Triple → α)
    (st : TriGChunkFoldState α) (a b : String) :
    (st.feed step a).bind (fun s => s.feed step b) = st.feed step (a ++ b) := by
  unfold TriGChunkFoldState.feed
  rw [TriGScan.drain_feed_split]
  generalize hd : (st.scanner.feed a).drain = d
  obtain ⟨e1, sc1⟩ := d
  simp only []
  rw [applyEvents_withScanner]
  cases hr : applyEvents step st e1 with
  | error x =>
      rw [applyEvents_append, applyEvents_withScanner, hr]
      rfl
  | ok s0 =>
      rw [applyEvents_append, applyEvents_withScanner, hr]
      rfl

/-! ## Graph-block state: braces open and close in strict alternation -/

/-- The block flag after a sequence of units, from a start flag; `none` when
a unit opens a block inside a block, or closes one outside a block. -/
def simBlock : Bool → List TriGEvent → Option Bool
  | b, [] => some b
  | b, .stmt _ :: es => simBlock b es
  | false, .blockOpen _ :: es => simBlock true es
  | true, .blockClose _ :: es => simBlock false es
  | _, _ :: _ => none

theorem simBlock_append (xs ys : List TriGEvent) :
    ∀ b, simBlock b (xs ++ ys) = (simBlock b xs).bind (fun b' => simBlock b' ys) := by
  induction xs with
  | nil => intro b; rfl
  | cons e es ih =>
      intro b
      cases e with
      | stmt t => exact ih b
      | blockOpen h => cases b <;> simp [simBlock, ih]
      | blockClose r => cases b <;> simp [simBlock, ih]

theorem simBlock_stmts (l : List String) :
    ∀ b, simBlock b (l.map TriGEvent.stmt) = some b := by
  induction l with
  | nil => intro b; rfl
  | cons t ts ih => intro b; exact ih b

theorem simBlock_stmts_rev (l : List String) (b : Bool) :
    simBlock b (l.map TriGEvent.stmt).reverse = some b := by
  have : (l.map TriGEvent.stmt).reverse = l.reverse.map TriGEvent.stmt := by simp
  rw [this]; exact simBlock_stmts _ _

/-- One character from a scanner with nothing pending: the units it makes
are well nested from the scanner's own flag, and end at its new flag. -/
theorem TriGScan.feedChar_sim (s : TriGScan) (hp : s.pend = []) (c : Char) :
    simBlock s.inBlock (s.feedChar c).pend.reverse = some (s.feedChar c).inBlock := by
  have h1 : s.inner.completedRev = [] := by
    simp [TriGScan.pend] at hp; exact hp.1
  have h2 : s.eventsRev = [] := by
    simp [TriGScan.pend] at hp; exact hp.2
  unfold TriGScan.feedChar
  by_cases he : s.escaped = true
  · simp only [he, if_true, TriGScan.pend, h2, List.append_nil]
    exact simBlock_stmts_rev _ _
  · by_cases hb : (s.inner.mode == ScanMode.normal) = true ∧ c = '{' ∧ s.inBlock = false
    · simp [he, hb, TriGScan.pend, TriGScan.flushInner, h1, h2, simBlock]
    · by_cases hb2 : (s.inner.mode == ScanMode.normal) = true ∧ c = '}' ∧ s.inBlock = true
      · simp [he, hb2, TriGScan.pend, TriGScan.flushInner, h1, h2, simBlock]
      · have hn : ¬ ((s.inner.mode == ScanMode.normal) = true ∧
            ((c = '{' ∧ s.inBlock = false) ∨ (c = '}' ∧ s.inBlock = true))) := by
          intro h
          obtain ⟨a, b⟩ := h
          rcases b with b | b
          · exact hb ⟨a, b.1, b.2⟩
          · exact hb2 ⟨a, b.1, b.2⟩
        simp [he, hn, TriGScan.pend, h2]
        exact simBlock_stmts_rev _ _

/-- The same from any scanner: the units made by one more character are well
nested from the scanner's flag. -/
theorem TriGScan.feedChar_new_sim (s : TriGScan) (c : Char) :
    simBlock s.inBlock (s.clear.feedChar c).pend.reverse = some (s.feedChar c).inBlock := by
  have := TriGScan.feedChar_sim s.clear (TriGScan.pend_clear s) c
  have hb : (s.feedChar c).inBlock = (s.clear.feedChar c).inBlock := by
    have := congrArg TriGScan.inBlock (TriGScan.feedChar_split s c).2
    simpa [TriGScan.inBlock_clear] using this
  rw [hb]; exact this

/-- Along any chunk: from a scanner whose pending units are well nested from
a start flag, the pending units after the chunk are well nested from the same
start flag and end at the scanner's new flag. -/
theorem TriGScan.feedChars_sim (cs : List Char) :
    ∀ (s : TriGScan) (b0 : Bool), simBlock b0 s.pend.reverse = some s.inBlock →
      simBlock b0 (s.feedChars cs).pend.reverse = some (s.feedChars cs).inBlock := by
  induction cs with
  | nil => intro s b0 h; exact h
  | cons c cs ih =>
      intro s b0 h
      apply ih
      rw [(TriGScan.feedChar_split s c).1, List.reverse_append, simBlock_append, h]
      exact TriGScan.feedChar_new_sim s c

/-- The scanner of a state with nothing pending: after any chunk, the units it
hands over are well nested from the state's flag. -/
theorem TriGScan.feed_sim (s : TriGScan) (hp : s.pend = []) (chunk : String) :
    simBlock s.inBlock (s.feed chunk).pend.reverse = some (s.feed chunk).inBlock := by
  apply TriGScan.feedChars_sim
  rw [hp]; rfl

/-! ## The fold keeps the block flag equal to the brace depth -/

/-- A stmt unit does not change the block state. -/
theorem applyEvent_stmt_block (step : α → Option Subject → List Triple → α)
    (st s : TriGChunkFoldState α) (text : String)
    (h : applyEvent step st (.stmt text) = .ok s) : s.block = st.block := by
  rcases st with ⟨t, a, p, b, sc0⟩
  cases b <;> simp only [applyEvent] at h <;> split at h <;>
    first | (injection h with h; subst h; rfl) | (cases h)

/-- The block flag follows the units. -/
theorem applyEvents_block (step : α → Option Subject → List Triple → α) :
    ∀ (evs : List TriGEvent) (st s : TriGChunkFoldState α) (b : Bool),
      applyEvents step st evs = .ok s → simBlock st.block.isSome evs = some b →
      s.block.isSome = b := by
  intro evs
  induction evs with
  | nil =>
      intro st s b h hs
      injection h with h; subst h
      simpa [simBlock] using hs
  | cons e es ih =>
      intro st s b h hs
      simp only [applyEvents] at h
      cases hr : applyEvent step st e with
      | error x => rw [hr] at h; cases h
      | ok s0 =>
          rw [hr] at h
          cases e with
          | stmt t =>
              have hb := applyEvent_stmt_block step st s0 t hr
              exact ih s0 s b h (by rw [hb]; simpa [simBlock] using hs)
          | blockOpen hd =>
              have hb : s0.block.isSome = true := by
                rcases st with ⟨t, a, p, b', sc0⟩
                simp only [applyEvent] at hr
                split at hr
                · cases hr
                · injection hr with hr; subst hr; rfl
              cases hst : st.block.isSome
              · exact ih s0 s b h (by rw [hb]; simpa [simBlock, hst] using hs)
              · simp [simBlock, hst] at hs
          | blockClose r =>
              rcases st with ⟨t, a, p, b', sc0⟩
              cases b' with
              | none => simp only [applyEvent] at hr; cases hr
              | some g =>
                  have hb : s0.block.isSome = false := by
                    simp only [applyEvent] at hr
                    split at hr
                    · cases hr
                    · injection hr with hr; subst hr; rfl
                  exact ih s0 s b h (by rw [hb]; simpa [simBlock] using hs)

/-- The invariant of a fold state at a chunk boundary: the block flag is the
scanner's brace depth, and nothing is pending. -/
def TriGChunkFoldState.Inv (st : TriGChunkFoldState α) : Prop :=
  st.block.isSome = st.scanner.inBlock ∧ st.scanner.pend = []

theorem TriGChunkFoldState.init_inv (bnodePrefix : String) (acc : α) (base : Option String)
    (mode : Mode) : (TriGChunkFoldState.init bnodePrefix acc base mode).Inv := by
  simp [TriGChunkFoldState.Inv, TriGChunkFoldState.init, TriGScan.pend]

/-- BRACES ARE BALANCED AT EVERY CHUNK BOUNDARY: a successful feed keeps the
block flag equal to the scanner's brace depth, and leaves nothing pending. -/
theorem TriGChunkFoldState.feed_inv (step : α → Option Subject → List Triple → α)
    (st s : TriGChunkFoldState α) (chunk : String) (hi : st.Inv)
    (h : st.feed step chunk = .ok s) : s.Inv := by
  unfold TriGChunkFoldState.feed at h
  generalize hd : (st.scanner.feed chunk).drain = d at h
  obtain ⟨e1, sc1⟩ := d
  simp only [] at h
  rw [TriGScan.drain_eq] at hd
  injection hd with he hsc
  have hsim := TriGScan.feed_sim st.scanner hi.2 chunk
  rw [he] at hsim
  have hblk := applyEvents_block step e1 { st with scanner := sc1 } s _ h
    (by simpa [hi.1] using hsim)
  have hs := applyEvents_scanner step e1 { st with scanner := sc1 } s h
  refine ⟨?_, ?_⟩
  · rw [hblk, hs, ← hsc]; rfl
  · rw [hs, ← hsc]; exact TriGScan.pend_clear _

/-- An input that ends inside a graph block is refused. -/
theorem TriGChunkFoldState.finish_unterminated (step : α → Option Subject → List Triple → α)
    (st : TriGChunkFoldState α) (hi : st.Inv) (hin : st.scanner.inBlock = true) :
    ∃ e, st.finish step = .error e := by
  unfold TriGChunkFoldState.finish
  rw [TriGScan.drain_eq, hi.2]
  simp only [List.reverse_nil, applyEvents]
  have hb : st.block.isSome = true := by rw [hi.1, hin]
  rcases st with ⟨t, a, p, b, sc0⟩
  cases b with
  | none => simp at hb
  | some g => exact ⟨_, rfl⟩

/-! ## The graph label in force -/

/-- A step which records only the graph label of each triple it receives
(newest first). Every `step` call is observed through it. -/
def labelStep (acc : List (Option Subject)) (g : Option Subject) (ts : List Triple) :
    List (Option Subject) :=
  ts.map (fun _ => g) ++ acc

/-- INSIDE A BLOCK, every triple a statement emits carries the block's label:
the labels recorded by `consumeBlock` are the old ones and `g`. -/
theorem consumeBlock_graphs (g : Option Subject) :
    ∀ (fuel : Nat) (st : TurtleState) (acc : List (Option Subject)) (pos : Nat) (cs : List Char)
      (st' : TurtleState) (acc' : List (Option Subject)) (pos' : Nat),
      consumeBlock labelStep g fuel st acc pos cs = .ok (st', acc', pos') →
      ∀ x ∈ acc', x ∈ acc ∨ x = g := by
  intro fuel
  induction fuel with
  | zero => intro st acc pos cs st' acc' pos' h; simp [consumeBlock] at h
  | succ n ih =>
      intro st acc pos cs st' acc' pos' h x hx
      unfold consumeBlock at h
      split at h
      rename_i p1 r1 _
      split at h
      · injection h with h; injection h with _ h; injection h with h _; subst h; exact Or.inl hx
      · injection h with h; injection h with _ h; injection h with h _; subst h; exact Or.inl hx
      · split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · rename_i ts st2 p2 r2 _ _
                have := ih _ _ _ _ _ _ _ h x hx
                rcases this with h1 | h1
                · simp [labelStep] at h1
                  rcases h1 with h1 | h1
                  · exact Or.inr h1.2.symm
                  · exact Or.inl h1
                · exact Or.inr h1

/-- A stmt unit read inside the block of `g` emits only triples of `g`. -/
theorem applyEvent_stmt_graphs (st s : TriGChunkFoldState (List (Option Subject)))
    (g : Option Subject) (text : String) (hb : st.block = some g)
    (h : applyEvent labelStep st (.stmt text) = .ok s) :
    ∀ x ∈ s.acc, x ∈ st.acc ∨ x = g := by
  rcases st with ⟨t, a, p, b, sc0⟩
  simp only at hb
  subst hb
  simp only [applyEvent] at h
  split at h
  · cases h
  · rename_i r hr
    injection h with h; subst h
    exact consumeBlock_graphs g _ _ _ _ _ _ _ _ hr

/-- The unit that closes a block emits only triples of the block's label. -/
theorem applyEvent_close_graphs (st s : TriGChunkFoldState (List (Option Subject)))
    (g : Option Subject) (rest : String) (hb : st.block = some g)
    (h : applyEvent labelStep st (.blockClose rest) = .ok s) :
    ∀ x ∈ s.acc, x ∈ st.acc ∨ x = g := by
  rcases st with ⟨t, a, p, b, sc0⟩
  simp only at hb
  subst hb
  simp only [applyEvent] at h
  split at h
  · cases h
  · rename_i r hr
    injection h with h; subst h
    exact consumeBlock_graphs g _ _ _ _ _ _ _ _ hr

/-- The label of a block does not change while its statements are read. -/
theorem applyEvent_stmt_label (step : α → Option Subject → List Triple → α)
    (st s : TriGChunkFoldState α) (g : Option Subject) (text : String)
    (hb : st.block = some g) (h : applyEvent step st (.stmt text) = .ok s) :
    s.block = some g := by
  rw [applyEvent_stmt_block step st s text h, hb]

end L4Factoidal.Syntax

#print axioms L4Factoidal.Syntax.TriGScan.feedChars_split
#print axioms L4Factoidal.Syntax.TriGScan.drain_feed_split
#print axioms L4Factoidal.Syntax.TriGChunkFoldState.feed_split
#print axioms L4Factoidal.Syntax.TriGScan.feedChars_sim
#print axioms L4Factoidal.Syntax.TriGChunkFoldState.feed_inv
#print axioms L4Factoidal.Syntax.TriGChunkFoldState.finish_unterminated
#print axioms L4Factoidal.Syntax.TriGChunkFoldState.init_inv
#print axioms L4Factoidal.Syntax.applyEvent_stmt_block
#print axioms L4Factoidal.Syntax.applyEvents_block
#print axioms L4Factoidal.Syntax.consumeBlock_graphs
#print axioms L4Factoidal.Syntax.applyEvent_stmt_graphs
#print axioms L4Factoidal.Syntax.applyEvent_close_graphs
#print axioms L4Factoidal.Syntax.applyEvent_stmt_label
