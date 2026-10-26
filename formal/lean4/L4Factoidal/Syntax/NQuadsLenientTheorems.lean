/-
L4Factoidal.Syntax.NQuadsLenientTheorems — what the lenient N-Triples and
N-Quads walk (`NQuadsLenient.lean`) is proved to do
(https://github.com/danbri/factoidal/issues/716).

1. `foldLinesLenient_quad_of_ok`: when the strict generic fold
   `foldQuadLinesAcc` accepts the input with result `r`, the lenient walk
   with the N-Quads reader ends with `r` and leaves the diagnostic consumer,
   the error count and the stop flag as they were. It holds for every
   consumer, so the dataset, indexed-dataset and counting instances are
   corollaries, not separate proofs (owner steer 2026-08-24, "prove it over
   an abstraction").
2. `foldLinesLenient_triple_of_ok`: the same for `parseLinesAcc`, the strict
   N-Triples walk, and the N-Triples reader.
3. `foldLinesLenient_rel`: a relation between two consumers that each step
   preserves is preserved by the lenient walk, and the walk's control fields
   (diagnostics, error count, stop flag, line state) are the same for both.
   The walk never inspects the consumer state, which is why.
4. Entry points: `parseNTriplesLenient_of_ok`, `parseNQuadsLenient_of_ok`,
   `parseNQuadsFastLenient_of_ok` (`parseX s = .ok d → parseXLenient s = (d, [])`)
   and `parseNQuadsFastLenient_eq` (the indexed accumulator gives the
   reference result in lenient mode too).

None of the hypotheses mentions the lenient walk, so none restates a
conclusion (anti-pattern 29).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.NQuadsLenient
import L4Factoidal.Syntax.NQuadsFastTheorems

namespace L4Factoidal.Syntax

open L4Factoidal.RDF
open L4Factoidal.Syntax.NQuadsStreaming

/-! ## One statement branch, unfolded -/

private theorem strictQuad_default_branch (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α)
    (f pos pos1 : Nat) (cs t : List Char) (c : Char) (acc : α)
    (hw : skipWs pos cs = (pos1, c :: t))
    (h1 : c ≠ '#') (h2 : c ≠ '\n') (h3 : c ≠ '\r') :
    foldQuadLinesAcc mode consume (f + 1) pos cs acc
      = (match quadReader mode pos1 (c :: t) with
         | .error e => .error e
         | .ok (tr, gopt, pos2, cs2) =>
             let acc' := consume acc tr gopt
             let (pos3, cs3) := skipWs pos2 cs2
             let (pos4, cs4) := skipComment pos3 cs3
             let (pos5, cs5) := skipEol pos4 cs4
             foldQuadLinesAcc mode consume f pos5 cs5 acc') := by
  simp only [foldQuadLinesAcc, hw]
  split
  all_goals (try (exfalso; simp_all; done))
  rfl

private theorem strictTriple_default_branch (mode : Mode)
    (f pos pos1 : Nat) (cs t : List Char) (c : Char) (acc : List Triple)
    (hw : skipWs pos cs = (pos1, c :: t))
    (h1 : c ≠ '#') (h2 : c ≠ '\n') (h3 : c ≠ '\r') :
    parseLinesAcc mode (f + 1) pos cs acc
      = (match tripleReader mode pos1 (c :: t) with
         | .error e => .error e
         | .ok (tr, _, pos2, cs2) =>
             let (pos3, cs3) := skipWs pos2 cs2
             let (pos4, cs4) := skipComment pos3 cs3
             let (pos5, cs5) := skipEol pos4 cs4
             parseLinesAcc mode f pos5 cs5 (tr :: acc)) := by
  simp only [parseLinesAcc, hw]
  split
  all_goals (try (exfalso; simp_all; done))
  cases mode
  · simp only [tripleReader]
    rcases readTriple11 pos1 (c :: t) with _ | ⟨tr, p2, c2⟩ <;> rfl
  · simp only [tripleReader]
    rcases readTriple12 pos1 (c :: t) with _ | ⟨tr, p2, c2⟩ <;> rfl

private theorem lenient_default_branch (reader : LineReader) {α β : Type}
    (consume : α → Triple → Option Subject → α) (report : β → Diagnostic → β)
    (opts : LenientOptions)
    (f pos pos1 : Nat) (cs t : List Char) (c : Char) (run : LenientRun α β)
    (hw : skipWs pos cs = (pos1, c :: t))
    (h1 : c ≠ '#') (h2 : c ≠ '\n') (h3 : c ≠ '\r') :
    foldLinesLenient reader consume report opts (f + 1) pos cs run
      = (match reader pos1 (c :: t) with
         | .error e =>
             match run.recordError opts report pos1 (c :: t) e with
             | (run', false) => run'
             | (run', true) =>
                 let (pos2, cs2) := skipToEol pos1 (c :: t)
                 let (pos3, cs3) := skipEol pos2 cs2
                 foldLinesLenient reader consume report opts f pos3 cs3
                   { run' with linePos := run'.linePos.advance pos2 (pos3 - pos2) cs2 }
         | .ok (tr, gopt, pos2, cs2) =>
             let acc' := consume run.acc tr gopt
             let (pos3, cs3) := skipWs pos2 cs2
             let (pos4, cs4) := skipComment pos3 cs3
             let (pos5, cs5) := skipEol pos4 cs4
             foldLinesLenient reader consume report opts f pos5 cs5
               { run with acc := acc', linePos := run.linePos.advance pos4 (pos5 - pos4) cs4 }) := by
  simp only [foldLinesLenient, hw]
  split
  all_goals (try (exfalso; simp_all; done))
  rfl

/-! ## 1. Strict success: the lenient N-Quads walk reports nothing -/

theorem foldLinesLenient_quad_of_ok (mode : Mode) {α β : Type}
    (consume : α → Triple → Option Subject → α) (report : β → Diagnostic → β)
    (opts : LenientOptions) :
    ∀ (f pos : Nat) (cs : List Char) (run : LenientRun α β) (r : α),
      foldQuadLinesAcc mode consume f pos cs run.acc = .ok r →
      ∃ lp, foldLinesLenient (quadReader mode) consume report opts f pos cs run
              = { run with acc := r, linePos := lp }
  | 0, _, _, _, _, h => by simp [foldQuadLinesAcc] at h
  | f + 1, pos, cs, run, r, h => by
      cases hw : skipWs pos cs with
      | mk pos1 cs1 =>
        cases hc1 : cs1 with
        | nil =>
            rw [hc1] at hw
            simp only [foldQuadLinesAcc, hw, Except.ok.injEq] at h
            subst h
            refine ⟨run.linePos, ?_⟩
            simp only [foldLinesLenient, hw]
        | cons c t =>
          rw [hc1] at hw
          by_cases hh : c = '#'
          · subst hh
            simp only [foldQuadLinesAcc, hw] at h
            simp only [foldLinesLenient, hw]
            exact foldLinesLenient_quad_of_ok mode consume report opts f _ _ _ _ h
          · by_cases hn : c = '\n'
            · subst hn
              simp only [foldQuadLinesAcc, hw] at h
              simp only [foldLinesLenient, hw]
              exact foldLinesLenient_quad_of_ok mode consume report opts f _ _ _ _ h
            · by_cases hr : c = '\r'
              · subst hr
                simp only [foldQuadLinesAcc, hw] at h
                simp only [foldLinesLenient, hw]
                exact foldLinesLenient_quad_of_ok mode consume report opts f _ _ _ _ h
              · rw [strictQuad_default_branch mode consume f pos pos1 cs t c run.acc hw hh hn hr] at h
                rw [lenient_default_branch (quadReader mode) consume report opts f pos pos1 cs t c
                      run hw hh hn hr]
                cases hs : quadReader mode pos1 (c :: t) with
                | error e => rw [hs] at h; simp at h
                | ok v =>
                    obtain ⟨tr, gg, p2, c2⟩ := v
                    rw [hs] at h
                    exact foldLinesLenient_quad_of_ok mode consume report opts f _ _ _ _ h

/-! ## 2. Strict success: the lenient N-Triples walk reports nothing -/

theorem foldLinesLenient_triple_of_ok (mode : Mode) {β : Type}
    (report : β → Diagnostic → β) (opts : LenientOptions) :
    ∀ (f pos : Nat) (cs : List Char) (run : LenientRun (List Triple) β) (r : List Triple),
      parseLinesAcc mode f pos cs run.acc = .ok r →
      ∃ lp, foldLinesLenient (tripleReader mode) (fun acc t _ => t :: acc) report opts
                f pos cs run
              = { run with acc := r.reverse, linePos := lp }
  | 0, _, _, _, _, h => by simp [parseLinesAcc] at h
  | f + 1, pos, cs, run, r, h => by
      cases hw : skipWs pos cs with
      | mk pos1 cs1 =>
        cases hc1 : cs1 with
        | nil =>
            rw [hc1] at hw
            simp only [parseLinesAcc, hw, Except.ok.injEq] at h
            subst h
            refine ⟨run.linePos, ?_⟩
            simp only [foldLinesLenient, hw, List.reverse_reverse]
        | cons c t =>
          rw [hc1] at hw
          by_cases hh : c = '#'
          · subst hh
            simp only [parseLinesAcc, hw] at h
            simp only [foldLinesLenient, hw]
            exact foldLinesLenient_triple_of_ok mode report opts f _ _ _ _ h
          · by_cases hn : c = '\n'
            · subst hn
              simp only [parseLinesAcc, hw] at h
              simp only [foldLinesLenient, hw]
              exact foldLinesLenient_triple_of_ok mode report opts f _ _ _ _ h
            · by_cases hr : c = '\r'
              · subst hr
                simp only [parseLinesAcc, hw] at h
                simp only [foldLinesLenient, hw]
                exact foldLinesLenient_triple_of_ok mode report opts f _ _ _ _ h
              · rw [strictTriple_default_branch mode f pos pos1 cs t c run.acc hw hh hn hr] at h
                rw [lenient_default_branch (tripleReader mode) _ report opts f pos pos1 cs t c
                      run hw hh hn hr]
                cases hs : tripleReader mode pos1 (c :: t) with
                | error e => rw [hs] at h; simp at h
                | ok v =>
                    obtain ⟨tr, gg, p2, c2⟩ := v
                    rw [hs] at h
                    exact foldLinesLenient_triple_of_ok mode report opts f _ _ _ _ h

/-! ## 3. Two consumers related step by step stay related -/

/-- Two runs agree on everything but the consumer state, which is in `R`. -/
def LenientRun.Rel {α α' β : Type} (R : α → α' → Prop)
    (a : LenientRun α β) (b : LenientRun α' β) : Prop :=
  R a.acc b.acc ∧ a.diags = b.diags ∧ a.errors = b.errors ∧ a.stopped = b.stopped ∧
    a.linePos = b.linePos

private theorem recordError_rel {α α' β : Type} (R : α → α' → Prop) (opts : LenientOptions)
    (report : β → Diagnostic → β) (a : LenientRun α β) (b : LenientRun α' β)
    (pos : Nat) (cs : List Char) (e : ParseError) (h : LenientRun.Rel R a b) :
    (a.recordError opts report pos cs e).2 = (b.recordError opts report pos cs e).2 ∧
    LenientRun.Rel R (a.recordError opts report pos cs e).1 (b.recordError opts report pos cs e).1 := by
  obtain ⟨hacc, hd, he, hs, hl⟩ := h
  simp only [LenientRun.recordError, hd, he, hl]
  split
  · exact ⟨rfl, hacc, rfl, rfl, hs, rfl⟩
  · exact ⟨rfl, hacc, rfl, rfl, rfl, rfl⟩

theorem foldLinesLenient_rel (reader : LineReader) {α α' β : Type} (R : α → α' → Prop)
    (cA : α → Triple → Option Subject → α) (cB : α' → Triple → Option Subject → α')
    (hcons : ∀ a b t g, R a b → R (cA a t g) (cB b t g))
    (report : β → Diagnostic → β) (opts : LenientOptions) :
    ∀ (f pos : Nat) (cs : List Char) (a : LenientRun α β) (b : LenientRun α' β),
      LenientRun.Rel R a b →
      LenientRun.Rel R (foldLinesLenient reader cA report opts f pos cs a)
        (foldLinesLenient reader cB report opts f pos cs b)
  | 0, pos, cs, a, b, h => by
      have hr := recordError_rel R opts report a b pos cs
        ⟨"internal error: parser fuel exhausted (should be unreachable)", pos⟩ h
      obtain ⟨_, hacc, hd, he, _, hl⟩ := hr
      exact ⟨hacc, hd, he, rfl, hl⟩
  | f + 1, pos, cs, a, b, h => by
      have hlp : a.linePos = b.linePos := h.2.2.2.2
      cases hw : skipWs pos cs with
      | mk pos1 cs1 =>
        cases hc1 : cs1 with
        | nil =>
            rw [hc1] at hw
            simp only [foldLinesLenient, hw]
            exact h
        | cons c t =>
          rw [hc1] at hw
          by_cases hh : c = '#'
          · subst hh
            simp only [foldLinesLenient, hw]
            refine foldLinesLenient_rel reader R cA cB hcons report opts f _ _ _ _ ?_
            exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by rw [hlp]⟩
          · by_cases hn : c = '\n'
            · subst hn
              simp only [foldLinesLenient, hw]
              refine foldLinesLenient_rel reader R cA cB hcons report opts f _ _ _ _ ?_
              exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by rw [hlp]⟩
            · by_cases hr : c = '\r'
              · subst hr
                simp only [foldLinesLenient, hw]
                refine foldLinesLenient_rel reader R cA cB hcons report opts f _ _ _ _ ?_
                exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, by rw [hlp]⟩
              · rw [lenient_default_branch reader cA report opts f pos pos1 cs t c a hw hh hn hr,
                    lenient_default_branch reader cB report opts f pos pos1 cs t c b hw hh hn hr]
                cases hs : reader pos1 (c :: t) with
                | error e =>
                    simp only
                    obtain ⟨hbool, hrel⟩ := recordError_rel R opts report a b pos1 (c :: t) e h
                    revert hbool hrel
                    cases (a.recordError opts report pos1 (c :: t) e) with
                    | mk ra ka =>
                      cases (b.recordError opts report pos1 (c :: t) e) with
                      | mk rb kb =>
                        intro hbool hrel
                        simp only at hbool hrel
                        subst hbool
                        cases ka with
                        | false => exact hrel
                        | true =>
                            simp only
                            refine foldLinesLenient_rel reader R cA cB hcons report opts f _ _ _ _ ?_
                            exact ⟨hrel.1, hrel.2.1, hrel.2.2.1, hrel.2.2.2.1,
                              by rw [hrel.2.2.2.2]⟩
                | ok v =>
                    obtain ⟨tr, gg, p2, c2⟩ := v
                    simp only
                    refine foldLinesLenient_rel reader R cA cB hcons report opts f _ _ _ _ ?_
                    exact ⟨hcons _ _ tr gg h.1, h.2.1, h.2.2.1, h.2.2.2.1, by rw [hlp]⟩

/-! ## 4. Entry points -/

/-- **N-Triples.** On input `parseNTriples` accepts, the lenient parse
returns the same graph and no diagnostics, whatever `maxErrors` is. -/
theorem parseNTriplesLenient_of_ok (s : String) (mode : Mode) (opts : LenientOptions)
    (g : Graph) (h : parseNTriples s mode = .ok g) :
    parseNTriplesLenient s mode opts = (g, []) := by
  simp only [parseNTriples] at h
  obtain ⟨lp, hlp⟩ := foldLinesLenient_triple_of_ok mode pushDiag opts (s.toList.length + 1) 0
    s.toList { acc := [], diags := [] } g h
  simp only [parseNTriplesLenient, lenientLines, hlp, List.reverse_reverse, List.reverse_nil]

/-- **N-Quads, reference accumulator.** -/
theorem parseNQuadsLenient_of_ok (s : String) (mode : Mode) (opts : LenientOptions)
    (d : Dataset) (h : parseNQuads s mode = .ok d) :
    parseNQuadsLenient s mode opts = (d, []) := by
  simp only [parseNQuads, parseQuadLinesAcc_eq_fold] at h
  obtain ⟨lp, hlp⟩ := foldLinesLenient_quad_of_ok mode (fun ds t gopt => addQuad ds t gopt)
    pushDiag opts (s.toList.length + 1) 0 s.toList { acc := Dataset.empty, diags := [] } d h
  simp only [parseNQuadsLenient, lenientLines, hlp, List.reverse_nil]

/-- **N-Quads, indexed accumulator** (the WASM and CLI path). -/
theorem parseNQuadsFastLenient_of_ok (s : String) (mode : Mode) (opts : LenientOptions)
    (d : Dataset) (h : parseNQuadsFast s mode = .ok d) :
    parseNQuadsFastLenient s mode opts = (d, []) := by
  simp only [parseNQuadsFast] at h
  cases hf : foldQuadLinesAcc mode addQuadFast (s.toList.length + 1) 0 s.toList {} with
  | error e => rw [hf] at h; simp [Except.map] at h
  | ok a =>
      rw [hf] at h
      simp only [Except.map, Except.ok.injEq] at h
      obtain ⟨lp, hlp⟩ := foldLinesLenient_quad_of_ok mode addQuadFast pushDiag opts
        (s.toList.length + 1) 0 s.toList { acc := {}, diags := [] } a hf
      simp only [parseNQuadsFastLenient, lenientLines, hlp, List.reverse_nil, h]

/-- **The indexed accumulator in lenient mode** computes the reference
accumulator's dataset and the same diagnostics, on every input. -/
theorem parseNQuadsFastLenient_eq (s : String) (mode : Mode) (opts : LenientOptions) :
    parseNQuadsFastLenient s mode opts = parseNQuadsLenient s mode opts := by
  have hrel := foldLinesLenient_rel (quadReader mode)
    (fun (a : FastDataset) (b : Dataset) => a.Inv ∧ a.toDataset = b)
    addQuadFast (fun ds t gopt => addQuad ds t gopt)
    (by
      intro a b t g hab
      exact ⟨FastDataset.add_inv hab.1,
        by rw [addQuadFast_toDataset t g hab.1, hab.2]⟩)
    pushDiag opts (s.toList.length + 1) 0 s.toList
    { acc := {}, diags := [] } { acc := Dataset.empty, diags := [] }
    ⟨⟨FastDataset.inv_empty, FastDataset.toDataset_empty⟩, rfl, rfl, rfl, rfl⟩
  obtain ⟨⟨_, hacc⟩, hd, _, _, _⟩ := hrel
  simp only [parseNQuadsFastLenient, parseNQuadsLenient, lenientLines, hacc, hd]

/-! ## 5. The converse: a walk that reports nothing had nothing to report

With the list consumer `pushDiag`, every error the walk meets adds one
diagnostic, so a walk that ends with the diagnostic list it started with met
no error, and the strict walk accepts the same input. Together with section
1 this makes "a document the strict parser refuses gets at least one
diagnostic" a theorem; the W3C negative syntax tests check it on real files
(`l4w3c --lenient`). -/

private theorem recordError_pushes {α : Type} (opts : LenientOptions)
    (run : LenientRun α (List Diagnostic)) (pos : Nat) (cs : List Char) (e : ParseError) :
    ∃ d, (run.recordError opts pushDiag pos cs e).1.diags = d :: run.diags := by
  unfold LenientRun.recordError
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

private theorem append_cons_ne {γ : Type} (l : List γ) (d : γ) (xs : List γ) :
    l ++ d :: xs ≠ xs := by
  intro h
  have := congrArg List.length h
  simp at this
  omega

/-- The diagnostic list only grows, at the front. -/
theorem foldLinesLenient_diags_grow (reader : LineReader) {α : Type}
    (consume : α → Triple → Option Subject → α) (opts : LenientOptions) :
    ∀ (f pos : Nat) (cs : List Char) (run : LenientRun α (List Diagnostic)),
      ∃ l, (foldLinesLenient reader consume pushDiag opts f pos cs run).diags = l ++ run.diags
  | 0, pos, cs, run => by
      obtain ⟨d, hd⟩ := recordError_pushes opts run pos cs
        ⟨"internal error: parser fuel exhausted (should be unreachable)", pos⟩
      exact ⟨[d], by simp only [foldLinesLenient]; rw [hd]; rfl⟩
  | f + 1, pos, cs, run => by
      cases hw : skipWs pos cs with
      | mk pos1 cs1 =>
        cases hc1 : cs1 with
        | nil =>
            rw [hc1] at hw
            exact ⟨[], by simp only [foldLinesLenient, hw]; rfl⟩
        | cons c t =>
          rw [hc1] at hw
          by_cases hh : c = '#'
          · subst hh
            simp only [foldLinesLenient, hw]
            exact foldLinesLenient_diags_grow reader consume opts f _ _ _
          · by_cases hn : c = '\n'
            · subst hn
              simp only [foldLinesLenient, hw]
              exact foldLinesLenient_diags_grow reader consume opts f _ _ _
            · by_cases hr : c = '\r'
              · subst hr
                simp only [foldLinesLenient, hw]
                exact foldLinesLenient_diags_grow reader consume opts f _ _ _
              · rw [lenient_default_branch reader consume pushDiag opts f pos pos1 cs t c run
                      hw hh hn hr]
                cases hs : reader pos1 (c :: t) with
                | error e =>
                    simp only
                    obtain ⟨d, hd⟩ := recordError_pushes opts run pos1 (c :: t) e
                    revert hd
                    cases (run.recordError opts pushDiag pos1 (c :: t) e) with
                    | mk r' k =>
                      intro hd
                      simp only at hd
                      cases k with
                      | false => exact ⟨[d], by simp only; rw [hd]; rfl⟩
                      | true =>
                          simp only
                          have hg := foldLinesLenient_diags_grow reader consume opts f
                            (skipEol (skipToEol pos1 (c :: t)).1 (skipToEol pos1 (c :: t)).2).1
                            (skipEol (skipToEol pos1 (c :: t)).1 (skipToEol pos1 (c :: t)).2).2
                            { r' with linePos := (r'.linePos.advance (skipToEol pos1 (c :: t)).1
                                ((skipEol (skipToEol pos1 (c :: t)).1
                                    (skipToEol pos1 (c :: t)).2).1
                                  - (skipToEol pos1 (c :: t)).1) (skipToEol pos1 (c :: t)).2) }
                          obtain ⟨l, hl⟩ := hg
                          refine ⟨l ++ [d], ?_⟩
                          rw [hl]
                          simp [hd]
                | ok v =>
                    obtain ⟨tr, gg, p2, c2⟩ := v
                    simp only
                    exact foldLinesLenient_diags_grow reader consume opts f _ _ _

/-- **N-Quads, converse.** A lenient walk that reports nothing: the strict
walk accepts. -/
theorem foldLinesLenient_quad_ok_of_quiet (mode : Mode) {α : Type}
    (consume : α → Triple → Option Subject → α) (opts : LenientOptions) :
    ∀ (f pos : Nat) (cs : List Char) (run : LenientRun α (List Diagnostic)),
      (foldLinesLenient (quadReader mode) consume pushDiag opts f pos cs run).diags = run.diags →
      ∃ r, foldQuadLinesAcc mode consume f pos cs run.acc = .ok r
  | 0, pos, cs, run, h => by
      obtain ⟨d, hd⟩ := recordError_pushes opts run pos cs
        ⟨"internal error: parser fuel exhausted (should be unreachable)", pos⟩
      simp only [foldLinesLenient] at h
      rw [hd] at h
      exact absurd h (append_cons_ne [] d run.diags)
  | f + 1, pos, cs, run, h => by
      cases hw : skipWs pos cs with
      | mk pos1 cs1 =>
        cases hc1 : cs1 with
        | nil =>
            rw [hc1] at hw
            exact ⟨run.acc, by simp only [foldQuadLinesAcc, hw]⟩
        | cons c t =>
          rw [hc1] at hw
          by_cases hh : c = '#'
          · subst hh
            simp only [foldLinesLenient, hw] at h
            simp only [foldQuadLinesAcc, hw]
            have ih := foldLinesLenient_quad_ok_of_quiet mode consume opts f _ _ _ h
            exact ih
          · by_cases hn : c = '\n'
            · subst hn
              simp only [foldLinesLenient, hw] at h
              simp only [foldQuadLinesAcc, hw]
              have ih := foldLinesLenient_quad_ok_of_quiet mode consume opts f _ _ _ h
              exact ih
            · by_cases hr : c = '\r'
              · subst hr
                simp only [foldLinesLenient, hw] at h
                simp only [foldQuadLinesAcc, hw]
                have ih := foldLinesLenient_quad_ok_of_quiet mode consume opts f _ _ _ h
                exact ih
              · rw [lenient_default_branch (quadReader mode) consume pushDiag opts f pos pos1 cs t c
                      run hw hh hn hr] at h
                rw [strictQuad_default_branch mode consume f pos pos1 cs t c run.acc hw hh hn hr]
                cases hs : quadReader mode pos1 (c :: t) with
                | error e =>
                    exfalso
                    rw [hs] at h
                    simp only at h
                    obtain ⟨d, hd⟩ := recordError_pushes opts run pos1 (c :: t) e
                    revert h hd
                    cases (run.recordError opts pushDiag pos1 (c :: t) e) with
                    | mk r' k =>
                      intro h hd
                      simp only at hd
                      cases k with
                      | false =>
                          simp only at h
                          rw [hd] at h
                          exact append_cons_ne [] d run.diags h
                      | true =>
                          simp only at h
                          have hg := foldLinesLenient_diags_grow (quadReader mode) consume opts f
                            (skipEol (skipToEol pos1 (c :: t)).1 (skipToEol pos1 (c :: t)).2).1
                            (skipEol (skipToEol pos1 (c :: t)).1 (skipToEol pos1 (c :: t)).2).2
                            { r' with linePos := (r'.linePos.advance (skipToEol pos1 (c :: t)).1
                                ((skipEol (skipToEol pos1 (c :: t)).1
                                    (skipToEol pos1 (c :: t)).2).1
                                  - (skipToEol pos1 (c :: t)).1) (skipToEol pos1 (c :: t)).2) }
                          obtain ⟨l, hl⟩ := hg
                          rw [hl] at h
                          simp only [hd] at h
                          exact append_cons_ne l d run.diags h
                | ok v =>
                    obtain ⟨tr, gg, p2, c2⟩ := v
                    rw [hs] at h
                    have ih := foldLinesLenient_quad_ok_of_quiet mode consume opts f _ _ _ h
                    exact ih

/-- **N-Triples, converse.** A lenient walk that reports nothing: the strict
walk accepts. -/
theorem foldLinesLenient_triple_ok_of_quiet (mode : Mode) (opts : LenientOptions) :
    ∀ (f pos : Nat) (cs : List Char) (run : LenientRun (List Triple) (List Diagnostic)),
      (foldLinesLenient (tripleReader mode) (fun acc t _ => t :: acc) pushDiag opts f pos cs
          run).diags = run.diags →
      ∃ r, parseLinesAcc mode f pos cs run.acc = .ok r
  | 0, pos, cs, run, h => by
      obtain ⟨d, hd⟩ := recordError_pushes opts run pos cs
        ⟨"internal error: parser fuel exhausted (should be unreachable)", pos⟩
      simp only [foldLinesLenient] at h
      rw [hd] at h
      exact absurd h (append_cons_ne [] d run.diags)
  | f + 1, pos, cs, run, h => by
      cases hw : skipWs pos cs with
      | mk pos1 cs1 =>
        cases hc1 : cs1 with
        | nil =>
            rw [hc1] at hw
            exact ⟨run.acc.reverse, by simp only [parseLinesAcc, hw]⟩
        | cons c t =>
          rw [hc1] at hw
          by_cases hh : c = '#'
          · subst hh
            simp only [foldLinesLenient, hw] at h
            simp only [parseLinesAcc, hw]
            have ih := foldLinesLenient_triple_ok_of_quiet mode opts f _ _ _ h
            exact ih
          · by_cases hn : c = '\n'
            · subst hn
              simp only [foldLinesLenient, hw] at h
              simp only [parseLinesAcc, hw]
              have ih := foldLinesLenient_triple_ok_of_quiet mode opts f _ _ _ h
              exact ih
            · by_cases hr : c = '\r'
              · subst hr
                simp only [foldLinesLenient, hw] at h
                simp only [parseLinesAcc, hw]
                have ih := foldLinesLenient_triple_ok_of_quiet mode opts f _ _ _ h
                exact ih
              · rw [lenient_default_branch (tripleReader mode) _ pushDiag opts f pos pos1 cs t c
                      run hw hh hn hr] at h
                rw [strictTriple_default_branch mode f pos pos1 cs t c run.acc hw hh hn hr]
                cases hs : tripleReader mode pos1 (c :: t) with
                | error e =>
                    exfalso
                    rw [hs] at h
                    simp only at h
                    obtain ⟨d, hd⟩ := recordError_pushes opts run pos1 (c :: t) e
                    revert h hd
                    cases (run.recordError opts pushDiag pos1 (c :: t) e) with
                    | mk r' k =>
                      intro h hd
                      simp only at hd
                      cases k with
                      | false =>
                          simp only at h
                          rw [hd] at h
                          exact append_cons_ne [] d run.diags h
                      | true =>
                          simp only at h
                          have hg := foldLinesLenient_diags_grow (tripleReader mode) (fun (acc : List Triple) t _ => t :: acc) opts f
                            (skipEol (skipToEol pos1 (c :: t)).1 (skipToEol pos1 (c :: t)).2).1
                            (skipEol (skipToEol pos1 (c :: t)).1 (skipToEol pos1 (c :: t)).2).2
                            { r' with linePos := (r'.linePos.advance (skipToEol pos1 (c :: t)).1
                                ((skipEol (skipToEol pos1 (c :: t)).1
                                    (skipToEol pos1 (c :: t)).2).1
                                  - (skipToEol pos1 (c :: t)).1) (skipToEol pos1 (c :: t)).2) }
                          obtain ⟨l, hl⟩ := hg
                          rw [hl] at h
                          simp only [hd] at h
                          exact append_cons_ne l d run.diags h
                | ok v =>
                    obtain ⟨tr, gg, p2, c2⟩ := v
                    rw [hs] at h
                    have ih := foldLinesLenient_triple_ok_of_quiet mode opts f _ _ _ h
                    exact ih

/-- **N-Triples.** A lenient parse with no diagnostic: `parseNTriples`
accepts the same text. -/
theorem parseNTriples_ok_of_lenient_quiet (s : String) (mode : Mode) (opts : LenientOptions)
    (h : (parseNTriplesLenient s mode opts).2 = []) : ∃ g, parseNTriples s mode = .ok g := by
  simp only [parseNTriplesLenient, List.reverse_eq_nil_iff] at h
  simp only [parseNTriples]
  exact foldLinesLenient_triple_ok_of_quiet mode opts
    (s.toList.length + 1) 0 s.toList { acc := [], diags := [] } h

/-- **N-Quads.** A lenient parse with no diagnostic: `parseNQuads` accepts
the same text. With `parseNQuadsLenient_of_ok`, the lenient parse reports
nothing exactly when the strict parser accepts. -/
theorem parseNQuads_ok_of_lenient_quiet (s : String) (mode : Mode) (opts : LenientOptions)
    (h : (parseNQuadsLenient s mode opts).2 = []) : ∃ d, parseNQuads s mode = .ok d := by
  simp only [parseNQuadsLenient, List.reverse_eq_nil_iff] at h
  simp only [parseNQuads, parseQuadLinesAcc_eq_fold]
  exact foldLinesLenient_quad_ok_of_quiet mode (fun ds t gopt => addQuad ds t gopt) opts
    (s.toList.length + 1) 0 s.toList { acc := Dataset.empty, diags := [] } h

/-! ## Axiom audit -/

#print axioms foldLinesLenient_quad_of_ok
#print axioms foldLinesLenient_triple_of_ok
#print axioms foldLinesLenient_rel
#print axioms parseNTriplesLenient_of_ok
#print axioms parseNQuadsLenient_of_ok
#print axioms parseNQuadsFastLenient_of_ok
#print axioms parseNQuadsFastLenient_eq
#print axioms foldLinesLenient_diags_grow
#print axioms foldLinesLenient_quad_ok_of_quiet
#print axioms parseNQuads_ok_of_lenient_quiet
#print axioms foldLinesLenient_triple_ok_of_quiet
#print axioms parseNTriples_ok_of_lenient_quiet

end L4Factoidal.Syntax
