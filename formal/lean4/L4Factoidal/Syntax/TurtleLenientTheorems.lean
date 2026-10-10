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
4. The converse for Turtle, `parseTurtle_ok_of_lenient_quiet`: a lenient
   parse that reports no diagnostic means `parseTurtle` accepts. (For TriG
   the converse is not proved; the W3C negative syntax tests check it.)

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
    ∀ (fuel pos : Nat) (cs : List Char) (run : TurtleLenientRun Dataset β) (ds : Dataset)
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
          cases hs : readTriGStatement run.turtle (tws pos cs).1 (c :: rest) with
          | error e => simp [hs] at h
          | ok v =>
              obtain ⟨⟨gname, ts⟩, st2, p2, r2⟩ := v
              simp only [hs] at h ⊢
              by_cases hp : r2.length ≥ (c :: rest).length
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
      text.toList Dataset.empty with
  | error e => rw [hf] at h; simp at h
  | ok v =>
      obtain ⟨d, st'⟩ := v
      rw [hf] at h
      simp only [Except.ok.injEq] at h
      obtain ⟨lp, hlp⟩ := parseTriGStatementsLenient_of_ok pushDiag opts
        (text.toList.length + 2) 0 text.toList
        (TurtleLenientRun.init Dataset.empty [] (TurtleState.init text base mode)) d st' hf
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
      text.toList Dataset.empty with
  | error e => rw [hf] at h; simp at h
  | ok v =>
      obtain ⟨d, st'⟩ := v
      rw [hf] at h
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨hd, hps⟩ := h
      obtain ⟨lp, hlp⟩ := parseTriGStatementsLenient_of_ok pushDiag opts
        (text.toList.length + 2) 0 text.toList
        (TurtleLenientRun.init Dataset.empty [] (TurtleState.init text base mode)) d st' hf
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

end L4Factoidal.Syntax
