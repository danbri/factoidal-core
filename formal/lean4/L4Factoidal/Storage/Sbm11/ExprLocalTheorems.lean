/-
L4Factoidal.Storage.Sbm11.ExprLocalTheorems — what `Expr.evalIn` reads of a
solution mapping (https://github.com/danbri/factoidal/issues/776; the
locality lemma of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md,
section 2, L5v).

The id path evaluates a FILTER conjunct on a solution mapping that it builds
from the ids of the variables the conjunct reads (`IdQuery.applyFilters`:
`.general` and `.residual`, memoised by those ids); the reference evaluates
it on the whole decoded row, merged into the empty mapping
(`IdGroup.filterFn`). The two agree when `Expr.evalIn` reads nothing else of
the mapping. This file proves that.

* `Expr.refVars`: the names `Expr.evalIn` looks up: the variables of `?v` and
  `BOUND(?v)`, and the two reserved freshness keys (`fxKeyRow`, `fxKeyOcc`)
  under a call of UUID, STRUUID or BNODE (`freshFn`; they read
  `Binding.freshnessCtx`).
* `evalIn_congr`: two mappings with the same lookup for every name of
  `refVars e` give `e` the same value; and two environments give it the same
  value when `e` is `Expr.backendLocal` (no NOW, IRI(), REGEX, REPLACE,
  hash or function call). The id path's `.general`, `.str` and `.strRange`
  conjuncts are evaluated in the empty environment (`IdQuery.refFilter`),
  and `compileFilter` only builds them for a `backendLocal` conjunct.
* `EnvAgree`, `evalIn_agree`: two environments that agree on `ext`, `now`
  and `base` give every expression the same value; `Expr.evalIn` does not
  read `EvalEnv.dataset` (only `substituteExistentials` does, for EXISTS).
* `evalIn_bindEq`: the same lookup for every name gives the same value, so
  the order of the pairs of a mapping does not change it.
* `lookup_merge_empty`: `Binding.empty.merge row` (the mapping
  `QueryPattern.lowerWith` evaluates a condition on) has the lookup of `row`.
* `residualVars_spec`, `exprVars_spec`: every name of `refVars e` that is not
  a freshness key is in the variables the id path reads
  (`IdQuery.residualVars`, `IdQuery.exprVars`, explicit-stack loops).
* `conjuncts_spec`: the EBV of `c` is true exactly when the EBV of every
  conjunct of `IdQuery.conjuncts c` is true (`ebvOrFalse_evalIn_and`).

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.IdQuery
import L4Factoidal.Storage.Sbm11.IdQueryTests

namespace L4Factoidal.SPARQL

open L4Factoidal.RDF

/-- UUID, STRUUID and BNODE: the calls that read the freshness context of the
    mapping (`Binding.freshnessCtx`). -/
def Expr.freshFn (i : WfIri) : Bool :=
  i.val == fnNamespace ++ "uuid" || i.val == fnNamespace ++ "struuid" || i.val == fnNamespace ++ "bnode"

mutual
/-- The names `Expr.evalIn` looks up in the mapping. -/
def Expr.refVars : Expr → List String
  | .var v | .bound v => [v]
  | .iri _ | .lit _ | .boolLit _ | .numericLit _ | .decimalLit _ | .doubleLit _ | .now => []
  | .existsPat _ | .notExistsPat _ | .aggregate _ _ _ => []
  | .unaryMinus a | .unaryPlus a | .not a | .isIri a | .isBlank a | .isLiteral a | .isNumeric a
  | .str a | .lang a | .datatype a | .iriFn a | .hasLang a | .hasLangDir a | .langDir a
  | .strLen a | .uCase a | .lCase a | .encodeForUri a | .abs a | .round a | .ceil a | .floor a
  | .md5 a | .sha1 a | .sha256 a | .sha384 a | .sha512 a
  | .year a | .month a | .day a | .hours a | .minutes a | .seconds a | .timezone a | .tz a
  | .ttSubject a | .ttPredicate a | .ttObject a | .isTriple a => Expr.refVars a
  | .arith _ a b | .compare _ a b | .and a b | .or a b | .sameTerm a b | .strDt a b | .strLang a b
  | .strStarts a b | .strEnds a b | .contains a b | .strBefore a b | .strAfter a b
  | .substr a b none | .regex a b none => Expr.refVars a ++ Expr.refVars b
  | .strLangDir a b c | .cond a b c | .tripleTerm a b c | .substr a b (some c) | .regex a b (some c)
  | .replace a b c none => Expr.refVars a ++ Expr.refVars b ++ Expr.refVars c
  | .replace a b c (some d) => Expr.refVars a ++ Expr.refVars b ++ Expr.refVars c ++ Expr.refVars d
  | .coalesce es | .concat es => Expr.refVarsList es
  | .functionCall i es => (if Expr.freshFn i then [fxKeyRow, fxKeyOcc] else []) ++ Expr.refVarsList es
  | .inList a es | .notInList a es => Expr.refVars a ++ Expr.refVarsList es

def Expr.refVarsList : List Expr → List String
  | [] => []
  | e :: es => Expr.refVars e ++ Expr.refVarsList es
end

end L4Factoidal.SPARQL

namespace L4Factoidal.Storage.Sbm11.ExprLocalTheorems

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.IdQueryTests (ebvOrFalse_evalIn_and)

/-- Two environments that agree on what `Expr.evalIn` reads of an
    environment: the extension functions (`ext`), NOW (`now`) and BASE
    (`base`). The dataset (`EvalEnv.dataset`, which `substituteExistentials`
    reads for EXISTS) and the SERVICE endpoints are not among them. -/
def EnvAgree (env1 env2 : EvalEnv) : Prop := env1.ext = env2.ext ∧ env1.now = env2.now ∧ env1.base = env2.base

theorem EnvAgree.refl (env : EvalEnv) : EnvAgree env env := ⟨rfl, rfl, rfl⟩

/-- An environment and the same environment with another dataset agree. -/
theorem EnvAgree.withDataset (env : EvalEnv) (d : Option Dataset) : EnvAgree env { env with dataset := d } :=
  ⟨rfl, rfl, rfl⟩

theorem nonlocal {env1 env2 : EvalEnv} {e : Expr} (he : e.backendLocal = true ∨ EnvAgree env1 env2)
    (hb : e.backendLocal = false) : EnvAgree env1 env2 := by
  rcases he with h | h
  · rw [hb] at h; cases h
  · exact h

theorem local2 {E : Prop} {x a b : Bool} (he : x = true ∨ E) (hx : x = (a && b)) :
    (a = true ∨ E) ∧ (b = true ∨ E) := by
  subst hx
  rcases he with h | h
  · simp only [Bool.and_eq_true] at h
    exact ⟨Or.inl h.1, Or.inl h.2⟩
  · exact ⟨Or.inr h, Or.inr h⟩

theorem local3 {E : Prop} {x a b c : Bool} (he : x = true ∨ E) (hx : x = (a && b && c)) :
    (a = true ∨ E) ∧ (b = true ∨ E) ∧ (c = true ∨ E) := by
  subst hx
  rcases he with h | h
  · simp only [Bool.and_eq_true] at h
    exact ⟨Or.inl h.1.1, Or.inl h.1.2, Or.inl h.2⟩
  · exact ⟨Or.inr h, Or.inr h, Or.inr h⟩

mutual
/-- **Locality of `Expr.evalIn`.** Two mappings with the same lookup for
    every name `e` reads (`refVars`) give `e` the same value; two
    environments do when `e` is `backendLocal`. -/
theorem evalIn_congr (env1 env2 : EvalEnv) (mu1 mu2 : Binding) :
    (e : Expr) → (∀ v ∈ Expr.refVars e, mu1.lookup v = mu2.lookup v) →
      (e.backendLocal = true ∨ EnvAgree env1 env2) → Expr.evalIn env1 mu1 e = Expr.evalIn env2 mu2 e
  | .iri _, _, _ => by simp only [Expr.evalIn]
  | .lit _, _, _ => by simp only [Expr.evalIn]
  | .boolLit _, _, _ => by simp only [Expr.evalIn]
  | .numericLit _, _, _ => by simp only [Expr.evalIn]
  | .decimalLit _, _, _ => by simp only [Expr.evalIn]
  | .doubleLit _, _, _ => by simp only [Expr.evalIn]
  | .now, _, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn, e.2.1]
  | .existsPat _, _, _ => by simp only [Expr.evalIn]
  | .notExistsPat _, _, _ => by simp only [Expr.evalIn]
  | .aggregate _ _ _, _, _ => by simp only [Expr.evalIn]
  | .var v, h, _ => by
    simp only [Expr.evalIn]
    rw [h v (by simp [Expr.refVars])]
  | .bound v, h, _ => by
    simp only [Expr.evalIn]
    rw [h v (by simp [Expr.refVars])]
  | .unaryMinus a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .unaryPlus a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .not a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .isIri a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .isBlank a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .isLiteral a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .isNumeric a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .str a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .lang a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .datatype a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .hasLang a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .hasLangDir a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .langDir a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .strLen a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .uCase a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .lCase a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .encodeForUri a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .abs a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .round a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .ceil a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .floor a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .year a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .month a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .day a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .hours a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .minutes a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .seconds a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .timezone a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .tz a, h, he => by
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .iriFn a, h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.2.2])
  | .md5 a, h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.1, e.2.1, e.2.2])
  | .sha1 a, h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.1, e.2.1, e.2.2])
  | .sha256 a, h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.1, e.2.1, e.2.2])
  | .sha384 a, h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.1, e.2.1, e.2.2])
  | .sha512 a, h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.1, e.2.1, e.2.2])
  | .ttSubject a, h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.1, e.2.1, e.2.2])
  | .ttPredicate a, h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.1, e.2.1, e.2.2])
  | .ttObject a, h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.1, e.2.1, e.2.2])
  | .isTriple a, h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.1, e.2.1, e.2.2])
  | .arith op a b, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocal b) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .compare op a b, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocal b) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .and a b, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocal b) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .or a b, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocal b) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .sameTerm a b, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocal b) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .strDt a b, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocal b) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .strLang a b, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocal b) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .strStarts a b, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocal b) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .strEnds a b, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocal b) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .contains a b, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocal b) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .strBefore a b, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocal b) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .strAfter a b, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocal b) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .strLangDir a b c, h, he => by
    have ⟨ha, hb, hc⟩ := local3 (a := Expr.backendLocal a) (b := Expr.backendLocal b) (c := Expr.backendLocal c) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb, evalIn_congr env1 env2 mu1 mu2 c (fun v hv => h v (by simp [Expr.refVars, hv])) hc]
  | .cond a b c, h, he => by
    have ⟨ha, hb, hc⟩ := local3 (a := Expr.backendLocal a) (b := Expr.backendLocal b) (c := Expr.backendLocal c) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb, evalIn_congr env1 env2 mu1 mu2 c (fun v hv => h v (by simp [Expr.refVars, hv])) hc]
  | .tripleTerm a b c, h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e), evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e), evalIn_congr env1 env2 mu1 mu2 c (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.1, e.2.1, e.2.2])
  | .coalesce es, h, he => by
    simp only [Expr.evalIn]
    rw [evalArgs_congr env1 env2 mu1 mu2 es (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .concat es, h, he => by
    simp only [Expr.evalIn]
    rw [evalArgs_congr env1 env2 mu1 mu2 es (fun v hv => h v (by simp [Expr.refVars, hv])) (by simpa only [Expr.backendLocal] using he)]
  | .inList a es, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocalList es) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalArgs_congr env1 env2 mu1 mu2 es (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .notInList a es, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocalList es) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalArgs_congr env1 env2 mu1 mu2 es (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .substr a b none, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal a) (b := Expr.backendLocal b) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn, Expr.evalOpt]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb]
  | .substr a b (some c), h, he => by
    have ⟨ha, hb, hc⟩ := local3 (a := Expr.backendLocal a) (b := Expr.backendLocal b) (c := Expr.backendLocal c) he (by simp only [Expr.backendLocal])
    simp only [Expr.evalIn, Expr.evalOpt]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) ha, evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) hb, evalIn_congr env1 env2 mu1 mu2 c (fun v hv => h v (by simp [Expr.refVars, hv])) hc]
  | .regex a b none, h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e), evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.1, e.2.1, e.2.2])
  | .regex a b (some c), h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e), evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e), evalIn_congr env1 env2 mu1 mu2 c (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.1, e.2.1, e.2.2])
  | .replace a b c none, h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e), evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e), evalIn_congr env1 env2 mu1 mu2 c (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.1, e.2.1, e.2.2])
  | .replace a b c (some d), h, he => by
    have e := nonlocal he (by rfl)
    simp only [Expr.evalIn]
    rw [evalIn_congr env1 env2 mu1 mu2 a (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e), evalIn_congr env1 env2 mu1 mu2 b (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e), evalIn_congr env1 env2 mu1 mu2 c (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e), evalIn_congr env1 env2 mu1 mu2 d (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)]
    all_goals (simp only [e.1, e.2.1, e.2.2])
  | .functionCall i es, h, he => by
    have e := nonlocal he (by rfl)
    have hv := evalArgs_congr env1 env2 mu1 mu2 es (fun v hv => h v (by simp [Expr.refVars, hv])) (Or.inr e)
    by_cases hf : Expr.freshFn i = true
    · have h1 := h fxKeyRow (by simp [Expr.refVars, hf])
      have h2 := h fxKeyOcc (by simp [Expr.refVars, hf])
      have e1 : mu1.freshnessCtx fxKeyRow = mu2.freshnessCtx fxKeyRow := by
        simp only [Binding.freshnessCtx, h1]
      have e2 : mu1.freshnessCtx fxKeyOcc = mu2.freshnessCtx fxKeyOcc := by
        simp only [Binding.freshnessCtx, h2]
      simp only [Expr.evalIn, hv, e1, e2, e.1]
    · simp only [Expr.freshFn, Bool.or_eq_true, not_or, Bool.not_eq_true] at hf
      obtain ⟨⟨f1, f2⟩, f3⟩ := hf
      simp only [Expr.evalIn, hv, f1, f2, f3, Bool.false_eq_true, if_false, e.1]


/-- The list form of `evalIn_congr`. -/
theorem evalArgs_congr (env1 env2 : EvalEnv) (mu1 mu2 : Binding) :
    (es : List Expr) → (∀ v ∈ Expr.refVarsList es, mu1.lookup v = mu2.lookup v) →
      (Expr.backendLocalList es = true ∨ EnvAgree env1 env2) → Expr.evalArgs env1 mu1 es = Expr.evalArgs env2 mu2 es
  | [], _, _ => by simp only [Expr.evalArgs]
  | e :: es, h, he => by
    have ⟨ha, hb⟩ := local2 (a := Expr.backendLocal e) (b := Expr.backendLocalList es) he (by simp only [Expr.backendLocalList])
    simp only [Expr.evalArgs]
    rw [evalIn_congr env1 env2 mu1 mu2 e (fun v hv => h v (by simp [Expr.refVarsList, hv])) ha,
      evalArgs_congr env1 env2 mu1 mu2 es (fun v hv => h v (by simp [Expr.refVarsList, hv])) hb]
end

/-- The same lookup for every name gives the same value: the order of the
    pairs of a mapping, and pairs a later pair of the same name hides, do
    not change it. -/
theorem evalIn_bindEq (env : EvalEnv) (mu1 mu2 : Binding) (h : ∀ v, mu1.lookup v = mu2.lookup v) (e : Expr) :
    Expr.evalIn env mu1 e = Expr.evalIn env mu2 e :=
  evalIn_congr env env mu1 mu2 e (fun v _ => h v) (Or.inr (EnvAgree.refl env))

/-- **`Expr.evalIn` does not read the dataset.** Two environments that agree
    on `ext`, `now` and `base` give every expression the same value on every
    mapping: `Expr.evalIn` reads EXISTS as an error, and only
    `substituteExistentials` reads `EvalEnv.dataset`. -/
theorem evalIn_agree {env1 env2 : EvalEnv} (h : EnvAgree env1 env2) (mu : Binding) (e : Expr) :
    Expr.evalIn env1 mu e = Expr.evalIn env2 mu e :=
  evalIn_congr env1 env2 mu mu e (fun _ _ => rfl) (Or.inr h)

/-- `merge` keeps the first binding of a name: the lookup of `mu.merge row`
    is `mu`'s, else `row`'s. -/
theorem lookup_merge (v : String) : ∀ (row mu : Binding),
    (Binding.merge mu row).lookup v = match mu.lookup v with
      | some t => some t
      | none => row.lookup v
  | [], mu => by
    simp only [Binding.merge]
    cases mu.lookup v <;> rfl
  | (w, t) :: rest, mu => by
    simp only [Binding.merge]
    cases hw : mu.lookup w with
    | some _ =>
      simp only []
      rw [lookup_merge v rest mu]
      cases hv : mu.lookup v with
      | some _ => rfl
      | none =>
        simp only [Binding.lookup]
        by_cases e : w = v
        · subst e; rw [hw] at hv; cases hv
        · simp [e]
    | none =>
      simp only []
      rw [lookup_merge v rest ((w, t) :: mu)]
      simp only [Binding.lookup]
      by_cases e : w = v
      · subst e; simp [hw]
      · simp [e]

theorem lookup_merge_empty (row : Binding) (v : String) : (Binding.empty.merge row).lookup v = row.lookup v := by
  rw [lookup_merge]; rfl


/-! ## The variables the id path reads: `residualVars`, `exprVars` -/

/-- An invariant of a `for` loop over a list in `Id` with `break` or an early
    `return`: `P` after every step that continues, `Q` after one that stops. -/
theorem forIn_pq {α β : Type} (P Q : β → Prop) {f : α → β → Id (ForInStep β)} :
    ∀ (xs : List α) {b : β} {F : Id β}, forIn xs b f = F → P b →
      (∀ a s, P s → (∀ s', (f a s).run = .yield s' → P s') ∧ (∀ s', (f a s).run = .done s' → Q s')) →
      P F.run ∨ Q F.run
  | [], b, F, hF, h0, _ => by subst hF; exact Or.inl h0
  | a :: as, b, F, hF, h0, hs => by
    subst hF
    rw [List.forIn_cons]
    obtain ⟨hy, hd⟩ := hs a b h0
    cases e : (f a b).run with
    | done b' =>
      show P (match f a b with | .done b => pure b | .yield b => forIn as b f).run ∨ _
      rw [show f a b = .done b' from e]
      exact Or.inr (hd b' e)
    | yield b' =>
      show P (match f a b with | .done b => pure b | .yield b => forIn as b f).run ∨ _
      rw [show f a b = .yield b' from e]
      exact forIn_pq P Q as rfl (hy b' e) hs

theorem yield_ok {β : Type} {P Q : β → Prop} {t : β} (h : P t) :
    (∀ s', (ForInStep.yield t) = .yield s' → P s') ∧ (∀ s', (ForInStep.yield t) = .done s' → Q s') :=
  ⟨fun s' e => (by cases e; exact h), fun s' e => (by cases e)⟩

theorem done_ok {β : Type} {P Q : β → Prop} {t : β} (h : Q t) :
    (∀ s', (ForInStep.done t) = .yield s' → P s') ∧ (∀ s', (ForInStep.done t) = .done s' → Q s') :=
  ⟨fun s' e => (by cases e), fun s' e => (by cases e; exact h)⟩

/-- One of the two reserved freshness keys. -/
def IsFx (v : String) : Prop := v = fxKeyRow ∨ v = fxKeyOcc

theorem mem_refVarsList (v : String) : ∀ (es : List Expr), v ∈ Expr.refVarsList es ↔ ∃ y ∈ es, v ∈ y.refVars
  | [] => by simp [Expr.refVarsList]
  | e :: es => by
    simp only [Expr.refVarsList, List.mem_append, mem_refVarsList v es, List.mem_cons, exists_eq_or_imp]

theorem back_pop {a : Array Expr} {x : Expr} (h : a.back? = some x) : a.toList = a.pop.toList ++ [x] := by
  rw [Array.toList_pop]
  have : a.toList.getLast? = some x := by
    rw [← h]; exact Array.getLast?_toList a
  obtain ⟨ys, hy⟩ := List.getLast?_eq_some_iff.mp this
  rw [hy, List.dropLast_concat]

/-- Every name `e` reads is in `out`, or read by an expression on the stack,
    or a freshness key. -/
def VarsP (e : Expr) (st : Array Expr) (out : Array String) : Prop :=
  ∀ v ∈ e.refVars, v ∈ out.toList ∨ (∃ y ∈ st.toList, v ∈ y.refVars) ∨ IsFx v

/-- The state of the loops of `residualVars` and `exprVars` after a step that
    continues: no result, and `VarsP`. -/
def PInv (e : Expr) (s : Option (Option (Array String)) × Array Expr × Array String) : Prop :=
  s.1 = none ∧ VarsP e s.2.1 s.2.2

/-- After a step that stops: the result `none`, or no result and `VarsP`. -/
def QInv (e : Expr) (s : Option (Option (Array String)) × Array Expr × Array String) : Prop :=
  s.1 = some none ∨ (s.1 = none ∧ VarsP e s.2.1 s.2.2)

theorem step_gen {e : Expr} {st newst : Array Expr} {out out' : Array String} {x : Expr}
    (hb : st.back? = some x) (hinv : VarsP e st out)
    (hpop : ∀ y ∈ st.pop.toList, y ∈ newst.toList) (hout : ∀ w ∈ out.toList, w ∈ out'.toList)
    (hx : ∀ v ∈ x.refVars, v ∈ out'.toList ∨ (∃ y ∈ newst.toList, v ∈ y.refVars) ∨ IsFx v) :
    PInv e (none, newst, out') := by
  refine ⟨rfl, ?_⟩
  intro v hv
  rcases hinv v hv with h | ⟨y, hy, hvy⟩ | h
  · exact Or.inl (hout v h)
  · rw [back_pop hb, List.mem_append, List.mem_singleton] at hy
    rcases hy with hy | rfl
    · exact Or.inr (Or.inl ⟨y, hpop y hy, hvy⟩)
    · exact hx v hvy
  · exact Or.inr (Or.inr h)

theorem step_kids {e : Expr} {st newst : Array Expr} {out : Array String} {x : Expr}
    (hb : st.back? = some x) (hinv : VarsP e st out) (kids : List Expr)
    (hnew : ∀ y, y ∈ st.pop.toList ∨ y ∈ kids → y ∈ newst.toList)
    (hx : ∀ v ∈ x.refVars, v ∈ Expr.refVarsList kids ∨ IsFx v) :
    PInv e (none, newst, out) := by
  refine step_gen hb hinv (fun y hy => hnew y (Or.inl hy)) (fun w hw => hw) ?_
  intro v hv
  rcases hx v hv with h | h
  · obtain ⟨y, hy, h⟩ := (mem_refVarsList v kids).mp h
    exact Or.inr (Or.inl ⟨y, hnew y (Or.inr hy), h⟩)
  · exact Or.inr (Or.inr h)

theorem step_kids_eq {e : Expr} {st newst : Array Expr} {out : Array String} {x : Expr}
    (hb : st.back? = some x) (hinv : VarsP e st out) (kids : List Expr)
    (hnew : ∀ y, y ∈ st.pop.toList ∨ y ∈ kids → y ∈ newst.toList)
    (hx : x.refVars = Expr.refVarsList kids) :
    PInv e (none, newst, out) :=
  step_kids hb hinv kids hnew (fun v hv => Or.inl (hx ▸ hv))

theorem step_leaf {e : Expr} {st : Array Expr} {out : Array String} {x : Expr}
    (hb : st.back? = some x) (hinv : VarsP e st out) (hx : x.refVars = []) :
    PInv e (none, st.pop, out) :=
  step_gen hb hinv (fun y hy => hy) (fun w hw => hw) (by rw [hx]; simp)

theorem step_var {e : Expr} {st : Array Expr} {out out' : Array String} {x : Expr} {v : String}
    (hb : st.back? = some x) (hinv : VarsP e st out) (hx : x.refVars = [v])
    (hv : v ∈ out'.toList) (hout : ∀ w ∈ out.toList, w ∈ out'.toList) :
    PInv e (none, st.pop, out') :=
  step_gen hb hinv (fun y hy => hy) hout (by
    rw [hx]; intro w hw; rw [List.mem_singleton] at hw; subst hw; exact Or.inl hv)

/-- **The variables of a residual conjunct.** When `residualVars e` answers
    `some vs`, every name `e` reads is in `vs` or a freshness key. -/
theorem residualVars_spec (e : Expr) (vs : Array String) (h : residualVars e = some vs) :
    ∀ v ∈ e.refVars, v ∈ vs.toList ∨ IsFx v := by
  unfold residualVars at h
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range'] at h
  generalize hF : forIn (m := Id) (List.range' 0 _) _ _ = F at h
  have hI := forIn_pq (PInv e) (QInv e) _ hF ⟨rfl, by intro v hv; exact Or.inr (Or.inl ⟨e, by simp, hv⟩)⟩ (by
    intro a s hs
    obtain ⟨ret, st, out⟩ := s
    obtain ⟨_, hinv⟩ := hs
    simp only [] at hinv
    cases hb : st.back? with
    | none =>
      simp only []
      exact done_ok (Or.inr ⟨rfl, hinv⟩)
    | some x =>
      simp only []
      revert hb
      match x with
      | .iri _ => intro hb; exact yield_ok (step_leaf hb hinv (by simp [Expr.refVars]))
      | .lit _ => intro hb; exact yield_ok (step_leaf hb hinv (by simp [Expr.refVars]))
      | .boolLit _ => intro hb; exact yield_ok (step_leaf hb hinv (by simp [Expr.refVars]))
      | .numericLit _ => intro hb; exact yield_ok (step_leaf hb hinv (by simp [Expr.refVars]))
      | .decimalLit _ => intro hb; exact yield_ok (step_leaf hb hinv (by simp [Expr.refVars]))
      | .doubleLit _ => intro hb; exact yield_ok (step_leaf hb hinv (by simp [Expr.refVars]))
      | .now => intro hb; exact yield_ok (step_leaf hb hinv (by simp [Expr.refVars]))
      | .var v => 
        intro hb; dsimp only; split
        · exact yield_ok (step_var (out' := out.push v) (v := v) hb hinv (by simp [Expr.refVars]) (by simp) (fun w hw => by simp [hw]))
        · next hc => exact yield_ok (step_var (out' := out) (v := v) hb hinv (by simp [Expr.refVars]) (by simpa using hc) (fun w hw => hw))
      | .bound v => 
        intro hb; dsimp only; split
        · exact yield_ok (step_var (out' := out.push v) (v := v) hb hinv (by simp [Expr.refVars]) (by simp) (fun w hw => by simp [hw]))
        · next hc => exact yield_ok (step_var (out' := out) (v := v) hb hinv (by simp [Expr.refVars]) (by simpa using hc) (fun w hw => hw))
      | .unaryMinus a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .unaryPlus a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .not a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .isIri a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .isBlank a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .isLiteral a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .isNumeric a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .str a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .lang a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .datatype a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .hasLang a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .hasLangDir a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .langDir a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strLen a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .uCase a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .lCase a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .encodeForUri a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .abs a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .round a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .ceil a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .floor a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .year a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .month a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .day a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .hours a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .minutes a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .seconds a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .timezone a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .tz a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .iriFn a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .md5 a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .sha1 a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .sha256 a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .sha384 a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .sha512 a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .ttSubject a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .ttPredicate a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .ttObject a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .isTriple a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .arith _ a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .compare _ a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .and a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .or a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .sameTerm a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strDt a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strLang a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strStarts a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strEnds a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .contains a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strBefore a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strAfter a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strLangDir a b c => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b, c] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .cond a b c => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b, c] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .tripleTerm a b c => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b, c] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .substr a b none => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .substr a b (some c) => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b, c] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .regex a b none => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .regex a b (some c) => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b, c] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .replace a b c none => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b, c] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .replace a b c (some d) => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b, c, d] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .coalesce es => intro hb; exact yield_ok (step_kids_eq hb hinv es (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .concat es => intro hb; exact yield_ok (step_kids_eq hb hinv es (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .functionCall i es => intro hb; exact yield_ok (step_kids hb hinv es (by simp) (by
          intro v hv; simp only [Expr.refVars, List.mem_append] at hv
          rcases hv with h | h
          · split at h <;> simp [IsFx] at h ⊢ <;> simp [h]
          · exact Or.inl h))
      | .inList a es => intro hb; exact yield_ok (step_kids_eq hb hinv (a :: es) (by intro y hy; simp at hy ⊢; rcases hy with h | h | h <;> simp [h]) (by simp [Expr.refVars, Expr.refVarsList]))
      | .notInList a es => intro hb; exact yield_ok (step_kids_eq hb hinv (a :: es) (by intro y hy; simp at hy ⊢; rcases hy with h | h | h <;> simp [h]) (by simp [Expr.refVars, Expr.refVarsList]))
      | .existsPat _ => intro _; exact done_ok (Or.inl rfl)
      | .notExistsPat _ => intro _; exact done_ok (Or.inl rfl)
      | .aggregate _ _ _ => intro _; exact done_ok (Or.inl rfl))
  intro v hvar
  replace h : Id.run _ = some vs := h
  rw [Id.run_bind] at h
  generalize F.run = S at hI h
  obtain ⟨r, st, out⟩ := S
  have hv : VarsP e st out ∧ r = none := by
    rcases hI with ⟨h1, h2⟩ | (h1 | ⟨h1, h2⟩)
    · exact ⟨h2, h1⟩
    · simp only [] at h1; subst h1; cases h
    · exact ⟨h2, h1⟩
  obtain ⟨hv, hr⟩ := hv
  subst hr
  simp only [] at h
  split at h
  · cases h
  · next hne =>
    cases h
    rcases hv v hvar with h1 | ⟨y, hy, _⟩ | h1
    · exact Or.inl h1
    · have he : st.isEmpty = true := by simpa using hne
      rw [Array.isEmpty_iff] at he
      subst he; cases hy
    · exact Or.inr h1

/-- **The variables of a compiled conjunct.** When `exprVars e` answers
    `some vs`, every name `e` reads is in `vs` or a freshness key (an
    expression `exprVars` admits calls no function, so reads none). -/
theorem exprVars_spec (e : Expr) (vs : Array String) (h : exprVars e = some vs) :
    ∀ v ∈ e.refVars, v ∈ vs.toList ∨ IsFx v := by
  unfold exprVars at h
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range'] at h
  generalize hF : forIn (m := Id) (List.range' 0 _) _ _ = F at h
  have hI := forIn_pq (PInv e) (QInv e) _ hF ⟨rfl, by intro v hv; exact Or.inr (Or.inl ⟨e, by simp, hv⟩)⟩ (by
    intro a s hs
    obtain ⟨ret, st, out⟩ := s
    obtain ⟨_, hinv⟩ := hs
    simp only [] at hinv
    cases hb : st.back? with
    | none =>
      simp only []
      exact done_ok (Or.inr ⟨rfl, hinv⟩)
    | some x =>
      simp only []
      revert hb
      match x with
      | .iri _ => intro hb; exact yield_ok (step_leaf hb hinv (by simp [Expr.refVars]))
      | .lit _ => intro hb; exact yield_ok (step_leaf hb hinv (by simp [Expr.refVars]))
      | .boolLit _ => intro hb; exact yield_ok (step_leaf hb hinv (by simp [Expr.refVars]))
      | .numericLit _ => intro hb; exact yield_ok (step_leaf hb hinv (by simp [Expr.refVars]))
      | .decimalLit _ => intro hb; exact yield_ok (step_leaf hb hinv (by simp [Expr.refVars]))
      | .doubleLit _ => intro hb; exact yield_ok (step_leaf hb hinv (by simp [Expr.refVars]))
      | .now => intro _; exact done_ok (Or.inl rfl)
      | .var v => 
        intro hb; dsimp only; split
        · exact yield_ok (step_var (out' := out.push v) (v := v) hb hinv (by simp [Expr.refVars]) (by simp) (fun w hw => by simp [hw]))
        · next hc => exact yield_ok (step_var (out' := out) (v := v) hb hinv (by simp [Expr.refVars]) (by simpa using hc) (fun w hw => hw))
      | .bound v => 
        intro hb; dsimp only; split
        · exact yield_ok (step_var (out' := out.push v) (v := v) hb hinv (by simp [Expr.refVars]) (by simp) (fun w hw => by simp [hw]))
        · next hc => exact yield_ok (step_var (out' := out) (v := v) hb hinv (by simp [Expr.refVars]) (by simpa using hc) (fun w hw => hw))
      | .unaryMinus a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .unaryPlus a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .not a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .isIri a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .isBlank a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .isLiteral a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .isNumeric a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .str a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .lang a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .datatype a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .hasLang a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .hasLangDir a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .langDir a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strLen a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .uCase a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .lCase a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .encodeForUri a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .abs a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .round a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .ceil a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .floor a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .year a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .month a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .day a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .hours a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .minutes a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .seconds a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .timezone a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .tz a => intro hb; exact yield_ok (step_kids_eq hb hinv [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .iriFn a => intro _; exact done_ok (Or.inl rfl)
      | .md5 a => intro _; exact done_ok (Or.inl rfl)
      | .sha1 a => intro _; exact done_ok (Or.inl rfl)
      | .sha256 a => intro _; exact done_ok (Or.inl rfl)
      | .sha384 a => intro _; exact done_ok (Or.inl rfl)
      | .sha512 a => intro _; exact done_ok (Or.inl rfl)
      | .ttSubject a => intro _; exact done_ok (Or.inl rfl)
      | .ttPredicate a => intro _; exact done_ok (Or.inl rfl)
      | .ttObject a => intro _; exact done_ok (Or.inl rfl)
      | .isTriple a => intro _; exact done_ok (Or.inl rfl)
      | .arith _ a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .compare _ a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .and a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .or a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .sameTerm a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strDt a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strLang a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strStarts a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strEnds a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .contains a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strBefore a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strAfter a b => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .strLangDir a b c => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b, c] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .cond a b c => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b, c] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .tripleTerm a b c => intro _; exact done_ok (Or.inl rfl)
      | .substr a b none => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .substr a b (some c) => intro hb; exact yield_ok (step_kids_eq hb hinv [a, b, c] (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .regex a b none => intro _; exact done_ok (Or.inl rfl)
      | .regex a b (some c) => intro _; exact done_ok (Or.inl rfl)
      | .replace a b c none => intro _; exact done_ok (Or.inl rfl)
      | .replace a b c (some d) => intro _; exact done_ok (Or.inl rfl)
      | .coalesce es => intro hb; exact yield_ok (step_kids_eq hb hinv es (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .concat es => intro hb; exact yield_ok (step_kids_eq hb hinv es (by simp) (by simp [Expr.refVars, Expr.refVarsList]))
      | .functionCall i es => intro _; exact done_ok (Or.inl rfl)
      | .inList a es => intro hb; exact yield_ok (step_kids_eq hb hinv (a :: es) (by intro y hy; simp at hy ⊢; rcases hy with h | h | h <;> simp [h]) (by simp [Expr.refVars, Expr.refVarsList]))
      | .notInList a es => intro hb; exact yield_ok (step_kids_eq hb hinv (a :: es) (by intro y hy; simp at hy ⊢; rcases hy with h | h | h <;> simp [h]) (by simp [Expr.refVars, Expr.refVarsList]))
      | .existsPat _ => intro _; exact done_ok (Or.inl rfl)
      | .notExistsPat _ => intro _; exact done_ok (Or.inl rfl)
      | .aggregate _ _ _ => intro _; exact done_ok (Or.inl rfl))
  intro v hvar
  replace h : Id.run _ = some vs := h
  rw [Id.run_bind] at h
  generalize F.run = S at hI h
  obtain ⟨r, st, out⟩ := S
  have hv : VarsP e st out ∧ r = none := by
    rcases hI with ⟨h1, h2⟩ | (h1 | ⟨h1, h2⟩)
    · exact ⟨h2, h1⟩
    · simp only [] at h1; subst h1; cases h
    · exact ⟨h2, h1⟩
  obtain ⟨hv, hr⟩ := hv
  subst hr
  simp only [] at h
  split at h
  · cases h
  · next hne =>
    cases h
    rcases hv v hvar with h1 | ⟨y, hy, _⟩ | h1
    · exact Or.inl h1
    · have he : st.isEmpty = true := by simpa using hne
      rw [Array.isEmpty_iff] at he
      subst he; cases hy
    · exact Or.inr h1


/-! ## The conjuncts of a FILTER -/

/-- What the loop of `conjuncts` keeps: the conjunction of the EBVs of the
    conjuncts found and of the expressions left on the stack is the EBV of
    `c`, and every one is EXISTS-free when `c` is. -/
def CInv (env : EvalEnv) (mu : Binding) (c : Expr) (s : Array Expr × Array Expr) : Prop :=
  ebvOrFalse (Expr.evalIn env mu c) =
      ((s.2.toList.all fun x => ebvOrFalse (Expr.evalIn env mu x)) &&
        (s.1.toList.all fun x => ebvOrFalse (Expr.evalIn env mu x))) ∧
    (c.existsFree = true → (∀ x ∈ s.1.toList, x.existsFree = true) ∧ ∀ x ∈ s.2.toList, x.existsFree = true)

theorem back_pop' {α : Type} {a : Array α} {x : α} (h : a.back? = some x) : a.toList = a.pop.toList ++ [x] := by
  rw [Array.toList_pop]
  have : a.toList.getLast? = some x := by
    rw [← h]; exact Array.getLast?_toList a
  obtain ⟨ys, hy⟩ := List.getLast?_eq_some_iff.mp this
  rw [hy, List.dropLast_concat]

/-- **The conjuncts of a FILTER.** The EBV of `c` is the conjunction of the
    EBVs of `IdQuery.conjuncts c`, and each conjunct of an EXISTS-free `c` is
    EXISTS-free. -/
theorem conjuncts_spec (env : EvalEnv) (mu : Binding) (c : Expr) :
    ebvOrFalse (Expr.evalIn env mu c) = ((conjuncts c).toList.all fun x => ebvOrFalse (Expr.evalIn env mu x)) ∧
      (c.existsFree = true → ∀ x ∈ (conjuncts c).toList, x.existsFree = true) := by
  unfold conjuncts
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range']
  generalize hF : forIn (m := Id) (List.range' 0 _) _ _ = F
  have hI := forIn_pq (CInv env mu c) (CInv env mu c) _ hF
    ⟨by simp, fun h => ⟨by simp [h], by simp⟩⟩ (by
    intro a s hs
    obtain ⟨st, out⟩ := s
    obtain ⟨he, hx⟩ := hs
    simp only [] at he hx
    cases hb : st.back? with
    | none =>
      simp only []
      exact done_ok ⟨he, hx⟩
    | some x =>
      have hst := back_pop' hb
      simp only []
      revert hb
      cases x
      all_goals intro hb
      case and l r =>
        refine yield_ok ⟨?_, ?_⟩
        · rw [he, hst]
          simp only [Array.toList_push, List.all_append, List.all_cons, List.all_nil, Bool.and_true,
            ebvOrFalse_evalIn_and]
          cases (out.toList.all fun x => ebvOrFalse (Expr.evalIn env mu x)) <;>
            cases (st.pop.toList.all fun x => ebvOrFalse (Expr.evalIn env mu x)) <;>
            cases ebvOrFalse (Expr.evalIn env mu l) <;> cases ebvOrFalse (Expr.evalIn env mu r) <;> rfl
        · intro hc
          obtain ⟨h1, h2⟩ := hx hc
          rw [hst] at h1
          have hlr := h1 (.and l r) (by simp)
          simp only [Expr.existsFree, Bool.and_eq_true] at hlr
          refine ⟨fun y hy => ?_, h2⟩
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hy
          rcases hy with (hy | rfl) | rfl
          · exact h1 y (List.mem_append.mpr (Or.inl hy))
          · exact hlr.2
          · exact hlr.1
      all_goals
        refine yield_ok ⟨?_, ?_⟩
        · rw [he, hst]
          simp only [Array.toList_push, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
          generalize (out.toList.all fun x => ebvOrFalse (Expr.evalIn env mu x)) = p
          generalize (st.pop.toList.all fun x => ebvOrFalse (Expr.evalIn env mu x)) = q
          generalize ebvOrFalse (Expr.evalIn env mu _) = w
          cases p <;> cases q <;> cases w <;> rfl
        · intro hc
          obtain ⟨h1, h2⟩ := hx hc
          rw [hst] at h1
          refine ⟨fun y hy => h1 y (List.mem_append.mpr (Or.inl hy)), fun y hy => ?_⟩
          simp only [Array.toList_push, List.mem_append, List.mem_singleton] at hy
          rcases hy with hy | rfl
          · exact h2 y hy
          · exact h1 _ (List.mem_append.mpr (Or.inr (List.mem_singleton.mpr rfl))))
  have hfin : CInv env mu c F.run := by rcases hI with h | h <;> exact h
  show _ = ((F.run.2 ++ F.run.1.reverse).toList.all fun x => ebvOrFalse (Expr.evalIn env mu x)) ∧
    (c.existsFree = true → ∀ x ∈ (F.run.2 ++ F.run.1.reverse).toList, x.existsFree = true)
  generalize F.run = S at hfin
  obtain ⟨st, out⟩ := S
  obtain ⟨he, hx⟩ := hfin
  refine ⟨?_, ?_⟩
  · rw [he]
    simp only [Array.toList_append, Array.toList_reverse, List.all_append, List.all_reverse]
  · intro hc y hy
    obtain ⟨h1, h2⟩ := hx hc
    simp only [Array.toList_append, Array.toList_reverse, List.mem_append, List.mem_reverse] at hy
    rcases hy with hy | hy
    · exact h2 y hy
    · exact h1 y hy

end L4Factoidal.Storage.Sbm11.ExprLocalTheorems

#print axioms L4Factoidal.Storage.Sbm11.ExprLocalTheorems.evalIn_congr
#print axioms L4Factoidal.Storage.Sbm11.ExprLocalTheorems.lookup_merge_empty
#print axioms L4Factoidal.Storage.Sbm11.ExprLocalTheorems.evalIn_bindEq
#print axioms L4Factoidal.Storage.Sbm11.ExprLocalTheorems.residualVars_spec
#print axioms L4Factoidal.Storage.Sbm11.ExprLocalTheorems.exprVars_spec
#print axioms L4Factoidal.Storage.Sbm11.ExprLocalTheorems.conjuncts_spec
