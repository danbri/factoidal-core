/-
L4Factoidal.Syntax.TurtleLenientTheorems — on input the strict Turtle and
TriG parsers accept, the lenient walks (`TurtleLenient.lean`) give the strict
result and report nothing (https://github.com/danbri/factoidal/issues/716).

1. `parseStatementsLenient_of_ok`: when `parseStatementsFold` accepts with
   result `(r, st')`, the lenient walk ends with `r` and `st'` and leaves the
   diagnostic consumer, the error count and the stop flag as they were — for
   every triple consumer and every diagnostic consumer.
2. `parseTriGStatementsLenient_of_ok`: the same for `parseTriGStatements`.
3. Entry points: `parseTurtleLenient_of_ok`,
   `parseTurtleLenientWithPrefixes_of_ok`, `parseTriGLenient_of_ok`,
   `parseTriGLenientWithPrefixes_of_ok`.
4. The converse, `parseTurtle_ok_of_lenient_quiet` and
   `parseTriG_ok_of_lenient_quiet`: a lenient parse that reports no
   diagnostic means the strict parser accepts. For TriG this goes through
   `readGraphBodyRecover_grew` / `readTriGBlockRecover_grew`: a recovered
   graph block that changed the error count or the stop flag added a
   diagnostic.

No hypothesis mentions a lenient walk (anti-pattern 29).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.TurtleLenient
import L4Factoidal.Syntax.TurtleTheorems

namespace L4Factoidal.Syntax

open L4Factoidal.RDF

/-! ## 1. Turtle -/

theorem parseStatementsLenient_of_ok {α β : Type} (step : α → List Triple → α)
    (report : β → Diagnostic → β) (opts : LenientOptions) :
    ∀ (fuel pos : Nat) (cs : List Char) (run : TurtleLenientRun α β) (r : α) (st' : TurtleState),
      parseStatementsFold step fuel run.turtle pos cs run.acc = .ok (r, st') →
      ∃ lp, parseStatementsLenient step report opts fuel pos cs run
              = { run with acc := r, turtle := st', linePos := lp } := by
  intro fuel
  induction fuel with
  | zero =>
      intro pos cs run r st' h
      simp only [parseStatementsFold, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨run.linePos, by cases run; rfl⟩
  | succ fuel ih =>
      intro pos cs run r st' h
      simp only [parseStatementsFold] at h
      simp only [parseStatementsLenient]
      cases hr : (tws pos cs).2 with
      | nil =>
          simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨_, rfl⟩
      | cons c rest =>
          simp only [hr] at h ⊢
          cases hs : readStatement fuel run.turtle (tws pos cs).1 (c :: rest) with
          | error e => simp [hs] at h
          | ok v =>
              obtain ⟨ts, st2, p2, r2⟩ := v
              simp only [hs] at h ⊢
              by_cases hp : p2 ≤ (tws pos cs).1
              · simp only [hp, if_true, Except.ok.injEq, Prod.mk.injEq] at h ⊢
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨_, rfl⟩
              · simp only [hp, if_false] at h ⊢
                exact ih p2 r2 _ r st' h

/-- **Turtle.** On input `parseTurtle` accepts, the lenient parse returns the
same graph and no diagnostics, whatever `maxErrors` is. -/
theorem parseTurtleLenient_of_ok (text : String) (base : Option String) (mode : Mode)
    (opts : LenientOptions) (g : Graph) (h : parseTurtle text base mode = .ok g) :
    parseTurtleLenient text base mode opts = (g, []) := by
  rw [parseTurtle_eq_fold] at h
  simp only [parseTurtleFold] at h
  cases hf : parseStatementsFold prependReverse (text.toList.length + 2)
      (TurtleState.initChars text.toList base mode) 0 text.toList [] with
  | error e => rw [hf] at h; simp [Except.map] at h
  | ok v =>
      obtain ⟨a, st'⟩ := v
      rw [hf] at h
      simp only [Except.map, Except.ok.injEq] at h
      obtain ⟨lp, hlp⟩ := parseStatementsLenient_of_ok prependReverse pushDiag opts
        (text.toList.length + 2) 0 text.toList
        (TurtleLenientRun.init [] [] (TurtleState.initChars text.toList base mode)) a st' hf
      simp only [parseTurtleLenient, parseTurtleLenientWithPrefixes]
      rw [hlp]
      simp [TurtleLenientRun.init, h]

/-- **Turtle, with the prefix map** (the WASM envelope's `prefixes`). -/
theorem parseTurtleLenientWithPrefixes_of_ok (text : String) (base : Option String)
    (mode : Mode) (opts : LenientOptions) (g : Graph) (ps : List (String × String))
    (h : parseTurtleWithPrefixes text base mode = .ok (g, ps)) :
    parseTurtleLenientWithPrefixes text base mode opts = (g, [], ps) := by
  simp only [parseTurtleWithPrefixes, parseStatements_eq_fold] at h
  cases hf : parseStatementsFold prependReverse (text.toList.length + 2)
      (TurtleState.initChars text.toList base mode) 0 text.toList [] with
  | error e => rw [hf] at h; simp [Except.map] at h
  | ok v =>
      obtain ⟨a, st'⟩ := v
      rw [hf] at h
      simp only [Except.map, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hg, hps⟩ := h
      obtain ⟨lp, hlp⟩ := parseStatementsLenient_of_ok prependReverse pushDiag opts
        (text.toList.length + 2) 0 text.toList
        (TurtleLenientRun.init [] [] (TurtleState.initChars text.toList base mode)) a st' hf
      simp only [parseTurtleLenientWithPrefixes]
      rw [hlp]
      simp [TurtleLenientRun.init, hg, hps]

/-! ## 2. TriG -/

theorem parseTriGStatementsLenient_of_ok {β : Type} (report : β → Diagnostic → β)
    (opts : LenientOptions) :
    ∀ (fuel pos : Nat) (cs : List Char) (run : TurtleLenientRun FastDataset β) (ds : FastDataset)
      (st' : TurtleState),
      parseTriGStatements fuel run.turtle pos cs run.acc = .ok (ds, st') →
      ∃ lp, parseTriGStatementsLenient report opts fuel pos cs run
              = { run with acc := ds, turtle := st', linePos := lp } := by
  intro fuel
  induction fuel with
  | zero =>
      intro pos cs run ds st' h
      simp only [parseTriGStatements, Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨run.linePos, by cases run; rfl⟩
  | succ fuel ih =>
      intro pos cs run ds st' h
      simp only [parseTriGStatements] at h
      simp only [parseTriGStatementsLenient]
      cases hr : (tws pos cs).2 with
      | nil =>
          simp only [hr, Except.ok.injEq, Prod.mk.injEq] at h ⊢
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨_, rfl⟩
      | cons c rest =>
          simp only [hr] at h ⊢
          cases hs : readTriGStatement fuel run.turtle (tws pos cs).1 (c :: rest) with
          | error e => simp [hs] at h
          | ok v =>
              obtain ⟨⟨gname, ts⟩, st2, p2, r2⟩ := v
              simp only [hs] at h ⊢
              by_cases hp : p2 ≤ (tws pos cs).1
              · simp only [hp, if_true, Except.ok.injEq, Prod.mk.injEq] at h ⊢
                obtain ⟨rfl, rfl⟩ := h
                exact ⟨_, rfl⟩
              · simp only [hp, if_false] at h ⊢
                exact ih p2 r2 _ ds st' h

/-- **TriG.** On input `parseTriG` accepts, the lenient parse returns the
same dataset and no diagnostics, whatever `maxErrors` is. -/
theorem parseTriGLenient_of_ok (text : String) (base : Option String) (mode : Mode)
    (opts : LenientOptions) (ds : Dataset) (h : parseTriG text base mode = .ok ds) :
    parseTriGLenient text base mode opts = (ds, []) := by
  simp only [parseTriG] at h
  cases hf : parseTriGStatements (text.toList.length + 2) (TurtleState.init text base mode) 0
      text.toList {} with
  | error e => rw [hf] at h; simp at h
  | ok v =>
      obtain ⟨d, st'⟩ := v
      rw [hf] at h
      simp only [Except.ok.injEq] at h
      obtain ⟨lp, hlp⟩ := parseTriGStatementsLenient_of_ok pushDiag opts
        (text.toList.length + 2) 0 text.toList
        (TurtleLenientRun.init ({} : FastDataset) [] (TurtleState.init text base mode)) d st' hf
      simp only [parseTriGLenient, parseTriGLenientWithPrefixes]
      rw [hlp]
      simp [TurtleLenientRun.init, h]

/-- **TriG, with the prefix map.** -/
theorem parseTriGLenientWithPrefixes_of_ok (text : String) (base : Option String)
    (mode : Mode) (opts : LenientOptions) (ds : Dataset) (ps : List (String × String))
    (h : parseTriGWithPrefixes text base mode = .ok (ds, ps)) :
    parseTriGLenientWithPrefixes text base mode opts = (ds, [], ps) := by
  simp only [parseTriGWithPrefixes] at h
  cases hf : parseTriGStatements (text.toList.length + 2) (TurtleState.init text base mode) 0
      text.toList {} with
  | error e => rw [hf] at h; simp at h
  | ok v =>
      obtain ⟨d, st'⟩ := v
      rw [hf] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hd, hps⟩ := h
      obtain ⟨lp, hlp⟩ := parseTriGStatementsLenient_of_ok pushDiag opts
        (text.toList.length + 2) 0 text.toList
        (TurtleLenientRun.init ({} : FastDataset) [] (TurtleState.init text base mode)) d st' hf
      simp only [parseTriGLenientWithPrefixes]
      rw [hlp]
      simp [TurtleLenientRun.init, hd, hps]

/-! ## 3. The converse for Turtle: a walk that reports nothing had nothing to report

With the list consumer `pushDiag`, every error adds one diagnostic, so a walk
that ends with the list it started with met no error and the strict fold
accepts. With `parseTurtleLenient_of_ok`, the lenient parse reports nothing
exactly when `parseTurtle` accepts. -/

private theorem trecordError_pushes {α : Type} (opts : LenientOptions)
    (run : TurtleLenientRun α (List Diagnostic)) (pos : Nat) (cs : List Char) (e : ParseError)
    (r' : TurtleLenientRun α (List Diagnostic)) (k : Bool)
    (h : run.recordError opts pushDiag pos cs e = (r', k)) : ∃ d, r'.diags = d :: run.diags := by
  unfold TurtleLenientRun.recordError at h
  split at h
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨_, rfl⟩
  · simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact ⟨_, rfl⟩

/-- The diagnostic list only grows, at the front: any suffix of the list the
walk starts with is a suffix of the list it ends with. -/
theorem parseStatementsLenient_diags_grow {α : Type} (step : α → List Triple → α)
    (opts : LenientOptions) :
    ∀ (fuel pos : Nat) (cs : List Char) (run : TurtleLenientRun α (List Diagnostic))
      (ys : List Diagnostic), (∃ l1, run.diags = l1 ++ ys) →
      ∃ l, (parseStatementsLenient step pushDiag opts fuel pos cs run).diags = l ++ ys := by
  intro fuel
  induction fuel with
  | zero => intro pos cs run ys h; exact h
  | succ fuel ih =>
      intro pos cs run ys h
      simp only [parseStatementsLenient]
      cases hr : (tws pos cs).2 with
      | nil => exact h
      | cons c rest =>
          cases hs : readStatement fuel run.turtle (tws pos cs).1 (c :: rest) with
          | error e =>
              simp only [hs]
              split
              · rename_i r' heq
                obtain ⟨d, hd⟩ := trecordError_pushes opts _ _ _ _ _ _ heq
                obtain ⟨l1, hl1⟩ := h
                exact ⟨d :: l1, by rw [hd]; simp [hl1]⟩
              · rename_i r' heq
                obtain ⟨d, hd⟩ := trecordError_pushes opts _ _ _ _ _ _ heq
                obtain ⟨l1, hl1⟩ := h
                exact ih _ _ _ ys ⟨d :: l1, by simp only; rw [hd]; simp [hl1]⟩
          | ok v =>
              obtain ⟨ts, st2, p2, r2⟩ := v
              simp only [hs]
              by_cases hp : p2 ≤ (tws pos cs).1
              · simp only [hp, if_true]
                exact h
              · simp only [hp, if_false]
                exact ih _ _ _ ys h

private theorem parseStatementsLenient_diags_ne {α : Type} (step : α → List Triple → α)
    (opts : LenientOptions) (fuel pos : Nat) (cs : List Char)
    (run : TurtleLenientRun α (List Diagnostic)) (xs : List Diagnostic) (d : Diagnostic)
    (h : run.diags = d :: xs) :
    (parseStatementsLenient step pushDiag opts fuel pos cs run).diags ≠ xs := by
  obtain ⟨l, hl⟩ := parseStatementsLenient_diags_grow step opts fuel pos cs run (d :: xs)
    ⟨[], by simp [h]⟩
  rw [hl]
  intro hc
  have := congrArg List.length hc
  simp at this
  omega

theorem parseStatementsFold_ok_of_quiet {α : Type} (step : α → List Triple → α)
    (opts : LenientOptions) :
    ∀ (fuel pos : Nat) (cs : List Char) (run : TurtleLenientRun α (List Diagnostic)),
      (parseStatementsLenient step pushDiag opts fuel pos cs run).diags = run.diags →
      ∃ r st', parseStatementsFold step fuel run.turtle pos cs run.acc = .ok (r, st') := by
  intro fuel
  induction fuel with
  | zero => intro pos cs run _; exact ⟨run.acc, run.turtle, rfl⟩
  | succ fuel ih =>
      intro pos cs run h
      simp only [parseStatementsLenient] at h
      simp only [parseStatementsFold]
      cases hr : (tws pos cs).2 with
      | nil => simp only [hr]; exact ⟨_, _, rfl⟩
      | cons c rest =>
          simp only [hr] at h ⊢
          cases hs : readStatement fuel run.turtle (tws pos cs).1 (c :: rest) with
          | error e =>
              exfalso
              simp only [hs] at h
              split at h
              · rename_i r' heq
                obtain ⟨d, hd⟩ := trecordError_pushes opts _ _ _ _ _ _ heq
                rw [hd] at h
                have := congrArg List.length h
                simp at this
              · rename_i r' heq
                obtain ⟨d, hd⟩ := trecordError_pushes opts _ _ _ _ _ _ heq
                exact absurd h (parseStatementsLenient_diags_ne step opts _ _ _ _ run.diags d
                  (by simp only; rw [hd]))
          | ok v =>
              obtain ⟨ts, st2, p2, r2⟩ := v
              simp only [hs] at h ⊢
              by_cases hp : p2 ≤ (tws pos cs).1
              · simp only [hp, if_true]
                exact ⟨_, _, rfl⟩
              · simp only [hp, if_false] at h ⊢
                have hi := ih p2 r2 _ h
                exact hi

/-- **Turtle.** A lenient parse with no diagnostic: `parseTurtle` accepts the
same text. -/
theorem parseTurtle_ok_of_lenient_quiet (text : String) (base : Option String) (mode : Mode)
    (opts : LenientOptions) (h : (parseTurtleLenient text base mode opts).2 = []) :
    ∃ g, parseTurtle text base mode = .ok g := by
  simp only [parseTurtleLenient, parseTurtleLenientWithPrefixes, List.reverse_eq_nil_iff] at h
  obtain ⟨r, st', hf⟩ := parseStatementsFold_ok_of_quiet prependReverse opts
    (text.toList.length + 2) 0 text.toList
    (TurtleLenientRun.init [] [] (TurtleState.initChars text.toList base mode)) h
  have hf' : parseStatementsFold prependReverse (text.toList.length + 2)
      (TurtleState.initChars text.toList base mode) 0 text.toList [] = .ok (r, st') := hf
  exact ⟨r.reverse, by rw [parseTurtle_eq_fold]; simp [parseTurtleFold, hf', Except.map]⟩

/-! ## 4. The converse for TriG

`Grew out run`: the diagnostic list of `out` is the one of `run` with some
diagnostics in front, and if there are none, the error count and the stop
flag did not change either. Every step of the TriG walks keeps it. -/

/-- `out` extends `run`'s diagnostics; no new diagnostic means no new error
and no stop. -/
def TurtleLenientRun.Grew {α : Type} (out run : TurtleLenientRun α (List Diagnostic)) : Prop :=
  ∃ l, out.diags = l ++ run.diags ∧ (l = [] → out.errors = run.errors ∧ out.stopped = run.stopped)

private theorem grew_refl {α : Type} (run : TurtleLenientRun α (List Diagnostic)) :
    run.Grew run := ⟨[], by simp, fun _ => ⟨rfl, rfl⟩⟩

private theorem grew_trans {α : Type} {a b c : TurtleLenientRun α (List Diagnostic)}
    (hab : a.Grew b) (hbc : b.Grew c) : a.Grew c := by
  obtain ⟨l1, h1, k1⟩ := hab
  obtain ⟨l2, h2, k2⟩ := hbc
  refine ⟨l1 ++ l2, by rw [h1, h2, List.append_assoc], fun h => ?_⟩
  have e1 : l1 = [] := (List.append_eq_nil_iff.mp h).1
  have e2 : l2 = [] := (List.append_eq_nil_iff.mp h).2
  obtain ⟨x1, y1⟩ := k1 e1
  obtain ⟨x2, y2⟩ := k2 e2
  exact ⟨x1.trans x2, y1.trans y2⟩

private theorem grew_record {α : Type} (opts : LenientOptions)
    (run : TurtleLenientRun α (List Diagnostic)) (pos : Nat) (cs : List Char) (e : ParseError)
    (r' : TurtleLenientRun α (List Diagnostic)) (k : Bool)
    (h : run.recordError opts pushDiag pos cs e = (r', k)) : r'.Grew run := by
  obtain ⟨d, hd⟩ := trecordError_pushes opts run pos cs e r' k h
  exact ⟨[d], by simp [hd], fun h => by simp at h⟩

/-- A run with only its line state changed. -/
private theorem grew_linePos {α : Type} (run : TurtleLenientRun α (List Diagnostic))
    (lp : LinePos) : ({ run with linePos := lp } : TurtleLenientRun α (List Diagnostic)).Grew run :=
  ⟨[], by simp, fun _ => ⟨rfl, rfl⟩⟩

theorem readGraphBodyRecover_grew {α : Type} (opts : LenientOptions) :
    ∀ (fuel : Nat) (st : TurtleState) (pos : Nat) (cs : List Char) (acc : List Triple)
      (run : TurtleLenientRun α (List Diagnostic)),
      (readGraphBodyRecover pushDiag opts fuel st pos cs acc run).2.Grew run := by
  intro fuel
  induction fuel with
  | zero => intro st pos cs acc run; exact grew_refl run
  | succ fuel ih =>
      intro st pos cs acc run
      simp only [readGraphBodyRecover]
      split
      · -- end of input inside the block
        split
        · rename_i r' heq
          exact grew_trans (grew_record opts _ _ _ _ _ _ heq) (grew_linePos run _)
        · rename_i r' heq
          exact grew_trans (grew_record opts _ _ _ _ _ _ heq) (grew_linePos run _)
      · exact grew_linePos run _
      · split
        · split
          · rename_i r' heq
            exact grew_trans (grew_record opts _ _ _ _ _ _ heq) (grew_linePos run _)
          · rename_i r' heq
            exact grew_trans (grew_trans (ih _ _ _ _ _) (grew_linePos r' _))
              (grew_trans (grew_record opts _ _ _ _ _ _ heq) (grew_linePos run _))
        · split
          · exact grew_linePos run _
          · exact grew_trans (ih _ _ _ _ _) (grew_linePos run _)

theorem readGraphBodyRecover_grew' {α : Type} (opts : LenientOptions) (fuel : Nat)
    (st : TurtleState) (pos : Nat) (cs : List Char) (acc : List Triple)
    (run : TurtleLenientRun α (List Diagnostic))
    (x : Except ParseError (List Triple × TurtleState × Nat × List Char))
    (out : TurtleLenientRun α (List Diagnostic))
    (h : readGraphBodyRecover pushDiag opts fuel st pos cs acc run = (x, out)) : out.Grew run := by
  have hg := readGraphBodyRecover_grew opts fuel st pos cs acc run
  rw [h] at hg
  exact hg

theorem readTriGBlockRecover_grew {α : Type} (opts : LenientOptions) (fuel : Nat)
    (st : TurtleState) (pos : Nat) (cs : List Char) (run : TurtleLenientRun α (List Diagnostic))
    (res : Except ParseError ((Option Subject × List Triple) × TurtleState × Nat × List Char))
    (run2 : TurtleLenientRun α (List Diagnostic))
    (h : readTriGBlockRecover pushDiag opts fuel st pos cs run = some (res, run2)) :
    run2.Grew run := by
  simp only [readTriGBlockRecover] at h
  repeat' split at h
  all_goals first
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h
       obtain ⟨-, rfl⟩ := h
       exact grew_trans (readGraphBodyRecover_grew' opts _ _ _ _ _ _ _ _ (by assumption))
         (grew_linePos run _))
    | (simp at h)

/-- The diagnostic list of the TriG walk only grows, at the front. -/
theorem parseTriGStatementsLenient_diags_grow (opts : LenientOptions) :
    ∀ (fuel pos : Nat) (cs : List Char) (run : TurtleLenientRun FastDataset (List Diagnostic))
      (ys : List Diagnostic), (∃ l1, run.diags = l1 ++ ys) →
      ∃ l, (parseTriGStatementsLenient pushDiag opts fuel pos cs run).diags = l ++ ys := by
  intro fuel
  induction fuel with
  | zero => intro pos cs run ys h; exact h
  | succ fuel ih =>
      intro pos cs run ys h
      obtain ⟨l1, hl1⟩ := h
      simp only [parseTriGStatementsLenient]
      cases hr : (tws pos cs).2 with
      | nil => exact ⟨l1, hl1⟩
      | cons c rest =>
          cases hs : readTriGStatement fuel run.turtle (tws pos cs).1 (c :: rest) with
          | ok v =>
              obtain ⟨⟨gname, ts⟩, st2, p2, r2⟩ := v
              simp only [hs]
              by_cases hp : p2 ≤ (tws pos cs).1
              · simp only [hp, if_true]; exact ⟨l1, hl1⟩
              · simp only [hp, if_false]; exact ih _ _ _ ys ⟨l1, hl1⟩
          | error e =>
              simp only [hs]
              split
              · -- recovered
                rename_i gname ts st' p2 r2 run2 hrec
                have hg : run2.Grew run := by
                  revert hrec
                  split
                  · rename_i res run2' heqB
                    intro hrec
                    split at hrec
                    · simp only [Option.some.injEq, Prod.mk.injEq] at hrec
                      obtain ⟨-, -, -, -, -, rfl⟩ := hrec
                      exact grew_trans (readTriGBlockRecover_grew opts _ _ _ _ _ _ _ heqB)
                        (grew_linePos run _)
                    · simp at hrec
                  · rename_i e2 run2' heqB
                    intro hrec
                    split at hrec
                    · simp only [Option.some.injEq, Prod.mk.injEq] at hrec
                      obtain ⟨-, -, -, -, -, rfl⟩ := hrec
                      exact grew_trans (readTriGBlockRecover_grew opts _ _ _ _ _ _ _ heqB)
                        (grew_linePos run _)
                    · simp at hrec
                  · intro hrec; simp at hrec
                obtain ⟨l2, hl2, -⟩ := hg
                split
                · exact ⟨l2 ++ l1, by simp only; rw [hl2, hl1, List.append_assoc]⟩
                · exact ih _ _ _ ys ⟨l2 ++ l1, by simp only; rw [hl2, hl1, List.append_assoc]⟩
              · split
                · rename_i r' heq
                  obtain ⟨d, hd⟩ := trecordError_pushes opts _ _ _ _ _ _ heq
                  exact ⟨d :: l1, by rw [hd]; simp [hl1]⟩
                · rename_i r' heq
                  obtain ⟨d, hd⟩ := trecordError_pushes opts _ _ _ _ _ _ heq
                  exact ih _ _ _ ys ⟨d :: l1, by simp only; rw [hd]; simp [hl1]⟩

private theorem parseTriGStatementsLenient_diags_ne (opts : LenientOptions) (fuel pos : Nat)
    (cs : List Char) (run : TurtleLenientRun FastDataset (List Diagnostic)) (xs l2 : List Diagnostic)
    (hl2 : run.diags = l2 ++ xs) (hne : l2 ≠ []) :
    (parseTriGStatementsLenient pushDiag opts fuel pos cs run).diags ≠ xs := by
  obtain ⟨l, hl⟩ := parseTriGStatementsLenient_diags_grow opts fuel pos cs run run.diags
    ⟨[], by simp⟩
  intro hc
  rw [hc, hl2] at hl
  have hlen := congrArg List.length hl
  simp only [List.length_append] at hlen
  exact hne (List.eq_nil_of_length_eq_zero (by omega))

theorem parseTriGStatements_ok_of_quiet (opts : LenientOptions) :
    ∀ (fuel pos : Nat) (cs : List Char) (run : TurtleLenientRun FastDataset (List Diagnostic)),
      run.stopped = false →
      (parseTriGStatementsLenient pushDiag opts fuel pos cs run).diags = run.diags →
      ∃ ds st', parseTriGStatements fuel run.turtle pos cs run.acc = .ok (ds, st') := by
  intro fuel
  induction fuel with
  | zero => intro pos cs run _ _; exact ⟨run.acc, run.turtle, rfl⟩
  | succ fuel ih =>
      intro pos cs run hstop h
      simp only [parseTriGStatementsLenient] at h
      simp only [parseTriGStatements]
      cases hr : (tws pos cs).2 with
      | nil => simp only [hr]; exact ⟨_, _, rfl⟩
      | cons c rest =>
          simp only [hr] at h ⊢
          cases hs : readTriGStatement fuel run.turtle (tws pos cs).1 (c :: rest) with
          | ok v =>
              obtain ⟨⟨gname, ts⟩, st2, p2, r2⟩ := v
              simp only [hs] at h ⊢
              by_cases hp : p2 ≤ (tws pos cs).1
              · simp only [hp, if_true]; exact ⟨_, _, rfl⟩
              · simp only [hp, if_false] at h ⊢
                obtain ⟨ds, st', hf⟩ := ih p2 r2 _ (by exact hstop) h
                exact ⟨ds, st', hf⟩
          | error e =>
              exfalso
              simp only [hs] at h
              split at h
              · -- recovered: the block reported something, so the list grew.
                rename_i gname ts st' p2 r2 run2 hrec
                have hg : run2.Grew run ∧ (run2.errors > run.errors || run2.stopped) = true := by
                  revert hrec
                  split
                  · rename_i res run2' heqB
                    intro hrec
                    split at hrec
                    · rename_i hcond
                      simp only [Option.some.injEq, Prod.mk.injEq] at hrec
                      obtain ⟨-, -, -, -, -, rfl⟩ := hrec
                      exact ⟨grew_trans (readTriGBlockRecover_grew opts _ _ _ _ _ _ _ heqB)
                        (grew_linePos run _), hcond⟩
                    · simp at hrec
                  · rename_i e2 run2' heqB
                    intro hrec
                    split at hrec
                    · rename_i hcond
                      simp only [Option.some.injEq, Prod.mk.injEq] at hrec
                      obtain ⟨-, -, -, -, -, rfl⟩ := hrec
                      exact ⟨grew_trans (readTriGBlockRecover_grew opts _ _ _ _ _ _ _ heqB)
                        (grew_linePos run _), by simp [hcond]⟩
                    · simp at hrec
                  · intro hrec; simp at hrec
                obtain ⟨⟨l2, hl2, hk⟩, hcond⟩ := hg
                have hne : l2 ≠ [] := by
                  intro hl
                  obtain ⟨he, hst⟩ := hk hl
                  rw [he, hst, hstop] at hcond
                  simp at hcond
                split at h
                · simp only at h
                  rw [hl2] at h
                  have hlen := congrArg List.length h
                  simp only [List.length_append] at hlen
                  exact hne (List.eq_nil_of_length_eq_zero (by omega))
                · exact absurd h (parseTriGStatementsLenient_diags_ne opts _ _ _ _ run.diags l2
                    (by simp only; exact hl2) hne)
              · split at h
                · rename_i r' heq
                  obtain ⟨d, hd⟩ := trecordError_pushes opts _ _ _ _ _ _ heq
                  rw [hd] at h
                  have hlen := congrArg List.length h
                  simp at hlen
                · rename_i r' heq
                  obtain ⟨d, hd⟩ := trecordError_pushes opts _ _ _ _ _ _ heq
                  exact absurd h (parseTriGStatementsLenient_diags_ne opts _ _ _ _ run.diags [d]
                    (by simp only; rw [hd]; rfl) (by simp))

/-- **TriG.** A lenient parse with no diagnostic: `parseTriG` accepts the
same text. -/
theorem parseTriG_ok_of_lenient_quiet (text : String) (base : Option String) (mode : Mode)
    (opts : LenientOptions) (h : (parseTriGLenient text base mode opts).2 = []) :
    ∃ ds, parseTriG text base mode = .ok ds := by
  simp only [parseTriGLenient, parseTriGLenientWithPrefixes, List.reverse_eq_nil_iff] at h
  obtain ⟨ds, st', hf⟩ := parseTriGStatements_ok_of_quiet opts
    (text.toList.length + 2) 0 text.toList
    (TurtleLenientRun.init ({} : FastDataset) [] (TurtleState.init text base mode)) rfl h
  have hf' : parseTriGStatements (text.toList.length + 2) (TurtleState.init text base mode) 0
      text.toList {} = .ok (ds, st') := hf
  exact ⟨ds.toDataset, by simp [parseTriG, hf']⟩

/-! ## Axiom audit -/

#print axioms parseStatementsLenient_of_ok
#print axioms parseTurtleLenient_of_ok
#print axioms parseTurtleLenientWithPrefixes_of_ok
#print axioms parseTriGStatementsLenient_of_ok
#print axioms parseTriGLenient_of_ok
#print axioms parseTriGLenientWithPrefixes_of_ok
#print axioms parseStatementsLenient_diags_grow
#print axioms parseStatementsFold_ok_of_quiet
#print axioms parseTurtle_ok_of_lenient_quiet
#print axioms readGraphBodyRecover_grew
#print axioms parseTriGStatementsLenient_diags_grow
#print axioms parseTriGStatements_ok_of_quiet
#print axioms parseTriG_ok_of_lenient_quiet

end L4Factoidal.Syntax
