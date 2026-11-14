/-
L4Factoidal.MathML.OpenMathStrict — what `ofOM` reads from an OpenMath object is Strict Content.

`MathML/OpenMath.lean` proves the round trip from the `Expr` side (`ofOM (toOM s) = some s` for strict
`s`). This module proves the property from the OpenMath side: an object is read only into strict
form, by induction over `OMObj`.
-/
import L4Factoidal.MathML.OpenMath

namespace L4Factoidal.MathML

/-- The direct children of an object. -/
def omChildren : OMObj → List OMObj
  | .oma h args       => h :: args
  | .ombind b vs body => b :: body :: vs
  | .omattr ps o      => o :: ps
  | _                 => []

/-- Induction over `OMObj` by direct children. -/
theorem OMObj.childInduction {P : OMObj → Prop}
    (step : ∀ o, (∀ c ∈ omChildren o, P c) → P o) : ∀ o, P o := by
  intro o
  refine OMObj.rec (motive_1 := P) (motive_2 := fun l => ∀ c ∈ l, P c)
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ o
  · intro n; exact step _ (by simp [omChildren])
  · intro hex lex; exact step _ (by simp [omChildren])
  · intro s; exact step _ (by simp [omChildren])
  · intro name; exact step _ (by simp [omChildren])
  · intro cd name; exact step _ (by simp [omChildren])
  · intro h args ihh ihargs
    exact step _ (by
      intro c hc
      simp only [omChildren, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact ihh
      · exact ihargs c hc)
  · intro b vs body ihb ihvs ihbody
    exact step _ (by
      intro c hc
      simp only [omChildren, List.mem_cons] at hc
      rcases hc with rfl | rfl | hc
      · exact ihb
      · exact ihbody
      · exact ihvs c hc)
  · intro ps o' ihps iho
    exact step _ (by
      intro c hc
      simp only [omChildren, List.mem_cons] at hc
      rcases hc with rfl | hc
      · exact iho
      · exact ihps c hc)
  · intro c hc; simp at hc
  · intro a as iha ihas c hc
    simp only [List.mem_cons] at hc
    rcases hc with rfl | hc
    · exact iha
    · exact ihas c hc

theorem ofOMLoop_strict : ∀ (l : List OMObj),
    (∀ c ∈ l, ∀ e, ofOM c = some e → isStrict e = true) →
    ∀ (acc es : List Expr), (∀ e ∈ acc, isStrict e = true) → ofOMLoop l acc = some es →
      ∀ e ∈ es, isStrict e = true
  | [], _, acc, es, hacc, h => by
      simp only [ofOMLoop, Option.some.injEq] at h
      subst h
      intro e he
      exact hacc e (List.mem_reverse.mp he)
  | o :: os, hl, acc, es, hacc, h => by
      simp only [ofOMLoop] at h
      cases ho : ofOM o with
      | none => simp [ho] at h
      | some e0 =>
          simp only [ho] at h
          have h0 : isStrict e0 = true := hl o (by simp) e0 ho
          exact ofOMLoop_strict os (fun c hc => hl c (by simp [hc])) (e0 :: acc) es
            (by
              intro e he
              simp only [List.mem_cons] at he
              rcases he with rfl | he
              · exact h0
              · exact hacc e he) h

/-- Theorem (invariant). Says: whatever `ofOM` reads from an OpenMath object is in strict form.
    Does not say: that `ofOM` reads every object, or that the expression has a value. -/
theorem ofOM_isStrict : ∀ (o : OMObj) (e : Expr), ofOM o = some e → isStrict e = true := by
  apply OMObj.childInduction
  intro o ih e h
  cases o with
  | omi n => simp only [ofOM, Option.some.injEq] at h; subst h; simp [isStrict]
  | omv s => simp only [ofOM, Option.some.injEq] at h; subst h; simp [isStrict]
  | omf hex lex => simp [ofOM] at h
  | omstr s => simp [ofOM] at h
  | ombind b vs body => simp [ofOM] at h
  | omattr ps o' => simp [ofOM] at h
  | oms cd name =>
      simp only [ofOM] at h
      cases hk : keyOf cd name with
      | some k =>
          simp only [hk, Option.some.injEq] at h
          subst h
          simp [isStrict, isStrictList, strictNodeOk]
      | none =>
          simp only [hk] at h
          by_cases c1 : (cd == "logic1" && name == "true") = true
          · rw [if_pos c1] at h
            simp only [Option.some.injEq] at h
            subst h
            simp [isStrict]
          · rw [if_neg c1] at h
            by_cases c2 : (cd == "logic1" && name == "false") = true
            · rw [if_pos c2] at h
              simp only [Option.some.injEq] at h
              subst h
              simp [isStrict]
            · rw [if_neg c2] at h
              cases h
  | oma hd args =>
      simp only [ofOM] at h
      cases hh : headKey hd with
      | none => simp [hh] at h
      | some k =>
          cases hl : ofOMLoop args [] with
          | none => simp [hh, hl] at h
          | some as =>
              simp only [hh, hl] at h
              by_cases hn : strictNodeOk (.app k as) = true
              · rw [if_pos hn] at h
                simp only [Option.some.injEq] at h
                subst h
                have hargs : ∀ e ∈ as, isStrict e = true :=
                  ofOMLoop_strict args
                    (fun c hc e he => ih c (by simp [omChildren, hc]) e he) [] as
                    (by intro e he; simp at he) hl
                simp only [isStrict, hn, Bool.true_and]
                exact (isStrictList_iff as).mpr hargs
              · rw [if_neg hn] at h
                cases h

#print axioms ofOM_isStrict

end L4Factoidal.MathML
