/-
L4Factoidal.Storage.Sbm11.FilterIdTheorems — the FILTER conjuncts of the id
path against `Expr.evalIn` on the decoded rows
(https://github.com/danbri/factoidal/issues/776; lemma L5d of
docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

`IdQuery.compileFilter` compiles a FILTER conjunct to a test on ids, and
`IdQuery.filterKeep` (the loop of `applyFilters`) runs one test per conjunct
over the rows of a table. This file proves each test equal to the reference
FILTER of its conjunct, `ebvOrFalse (Expr.evalIn env μ e)`, on the decoded
row `μ`:

* `vc_const`, `eq_row`: `?v = c` and `c = ?v` with a constant
  `eqByTermConst?` accepts (an IRI, or a literal with no direction of type
  `xsd:string` or `rdf:langString`) is `Term.eqb` of `c` and the term of
  `?v`, for every term (numeric and boolean literals included:
  `valueCompare` gives an error or false for them).
* `sameTerm_row`, `sameTermVar_row`: `sameTerm` with a constant or a
  variable is `Term.sameTerm` of the two terms.
* `eq_ids`, `same_ids`, `var_ids`: on ids, with the dictionary lookup `cid`
  exact on the ids in `ok` (`CidOk`), answering the language-tag-folded term
  itself (`hcidN`: `normalizeTerm`, RDF 1.1 Concepts 3.3), and `Term.eqb` of
  decoded ids in `ok` id equality (`hdec`), the id tests are those
  relations.
* `compile_spec`: over a store whose dictionary lookup is `cid`,
  `compileFilter` returns one of those id tests or the `general` test
  (`KOk`), for a conjunct that is not a string test on dictionary keys
  (`StrForm`).
* `keep_residual`, `keep_general`, `keep_compiled`: the test of each kind in
  row `i` (`keepOf`) is the reference FILTER on the decoded row; the
  `general` and `residual` tests evaluate on a mapping of the variables
  `exprVars` and `residualVars` list, so they rest on the locality lemma
  (`ExprLocalTheorems.evalIn_congr`).
* `filterKeep_spec`: `filterKeep` keeps row `i` exactly when every test
  passes, with the memos of the decoded tests sound for their keys.
* `kind_sem` (L5d): a conjunct as `IdGroup.filterM` classifies it
  (`KindOf`: the residual test, or the compiled one when every variable is
  bound in every row).

## The defect this found

`sameTerm(?v, c)` with a literal constant whose language tag is not in
lower case kept no row on the id path, and the reference kept the rows whose
term has that tag in any case (`Literal.sameTerm` compares tags without
case). Minimal query, over `<http://e/s> <http://e/p> "a"@en .`:
`SELECT ?s WHERE { ?s <http://e/p> ?o FILTER(sameTerm(?o, "a"@EN)) }`; the
reference answers `<http://e/s>`, the id path answered nothing.
`compileFilter` now looks the constant up folded (`normalizeTerm`), as it
does for `=`; `tests/sbm11/gate/ids-sameterm-langcase*.rq` are the
regression tests.

## Not proved here

The string tests on dictionary keys (`FKind.str`, `FKind.strRange`:
STRSTARTS, STRENDS and CONTAINS of a variable and a simple literal) are
excluded (`StrForm`); they are tested by `IdQueryTests` and the W3C census.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.ExprLocalTheorems
import L4Factoidal.Storage.Sbm11.LeftJoinTableTheorems
import L4Factoidal.Fn.ComparisonTheorems

namespace L4Factoidal.Storage.Sbm11.FilterIdTheorems

open L4Factoidal.RDF
open L4Factoidal.SPARQL
open L4Factoidal.Storage.Sbm11.IdQuery
open L4Factoidal.Storage.Sbm11.ExprLocalTheorems

/-! ## Term identity on the terms -/

theorem char_toLower_idem (c : Char) : c.toLower.toLower = c.toLower := by
  unfold Char.toLower
  split
  · next h =>
    rw [dif_neg]
    intro h2
    simp only [UInt32.le_iff_toNat_le, UInt32.toNat_add] at h h2
    simp at h h2
    omega
  · rfl

theorem string_toLower_idem (s : String) : s.toLower.toLower = s.toLower := by
  apply String.ext
  simp [String.toLower, String.toList_map, char_toLower_idem]

/-- A constant of `=` that `eqByTermConst?` accepts: an IRI, or a literal
    with no direction whose datatype is `xsd:string` or `rdf:langString`. -/
def EqConst : Term → Prop
  | .iri _ => True
  | .literal l => l.val.direction = none ∧ (l.val.datatype = xsdString ∨ l.val.datatype = rdfLangString)
  | _ => False

theorem eqConst_of (c : Expr) (t : Term) (h : eqByTermConst? c = some t) : EqConst t := by
  cases c <;> simp only [eqByTermConst?, Option.some.injEq, reduceCtorEq] at h
  · subst h; trivial
  · next l =>
    split at h
    · next hc =>
      cases h
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, Bool.or_eq_true, Option.isSome_iff_ne_none,
        beq_iff_eq] at hc
      refine ⟨hc.1, ?_⟩
      rcases hc.2 with h1 | h1
      · right
        have hw := l.property
        unfold literalWf at hw
        cases ht : l.val.langTag with
        | none => exact absurd ht h1
        | some _ => rw [ht, hc.1] at hw; exact Subtype.ext (by simpa using hw)
      · left; exact h1
    · cases h

theorem lexicalValue_none (dt : WfIri) (s : String) (h : dt = xsdString ∨ dt = rdfLangString) :
    L4Factoidal.Fn.Numeric.lexicalValue? dt s = none := by
  rcases h with rfl | rfl
  · unfold L4Factoidal.Fn.Numeric.lexicalValue?
    have : L4Factoidal.XSD.builtinOfIri? xsdString.val = some .string := by decide +kernel
    rw [this]
    have : L4Factoidal.Fn.Numeric.isType .string = false := by decide +kernel
    simp [this]
  · unfold L4Factoidal.Fn.Numeric.lexicalValue?
    have : L4Factoidal.XSD.builtinOfIri? rdfLangString.val = none := by decide +kernel
    rw [this]; rfl

theorem strCompare_eq_zero (a b : String) : (strCompare a b == 0) = (a == b) := by
  rw [strCompare_eq_fast]
  unfold strCompareFast
  by_cases h1 : a < b
  · have : a ≠ b := fun e => by subst e; exact (String.lt_irrefl a) h1
    simp [h1, this]
  · by_cases h2 : a = b
    · simp [h1, h2]
    · simp [h1, h2]

theorem numDt_false (dt : WfIri) (h : dt = xsdString ∨ dt = rdfLangString) :
    L4Factoidal.Fn.Comparison.numericDatatype dt = false := by
  rcases h with rfl | rfl
  · decide +kernel
  · decide +kernel

theorem promote_const (l : WfLiteral) (h : l.val.datatype = xsdString ∨ l.val.datatype = rdfLangString) :
    literalPromote l = .term (.literal l) := by
  unfold literalPromote
  rcases h with h | h <;> rw [h]
  · have h1 : (xsdString == RDF.xsdInteger) = false := by decide +kernel
    have h2 : (xsdString == RDF.xsdDecimal) = false := by decide +kernel
    have h3 : (xsdString == RDF.xsdDouble) = false := by decide +kernel
    have h4 : (xsdString == SPARQL.xsdFloat) = false := by decide +kernel
    have h5 : (xsdString == RDF.xsdBoolean) = false := by decide +kernel
    simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, if_false, Bool.or_false]
  · have h1 : (rdfLangString == RDF.xsdInteger) = false := by decide +kernel
    have h2 : (rdfLangString == RDF.xsdDecimal) = false := by decide +kernel
    have h3 : (rdfLangString == RDF.xsdDouble) = false := by decide +kernel
    have h4 : (rdfLangString == SPARQL.xsdFloat) = false := by decide +kernel
    have h5 : (rdfLangString == RDF.xsdBoolean) = false := by decide +kernel
    simp only [h1, h2, h3, h4, h5, Bool.false_eq_true, if_false, Bool.or_false]

theorem numDt_true : L4Factoidal.Fn.Comparison.numericDatatype RDF.xsdInteger = true ∧
    L4Factoidal.Fn.Comparison.numericDatatype RDF.xsdDecimal = true ∧
    L4Factoidal.Fn.Comparison.numericDatatype RDF.xsdDouble = true ∧
    L4Factoidal.Fn.Comparison.numericDatatype SPARQL.xsdFloat = true := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide +kernel

theorem notXml (dt : WfIri) (h : dt = xsdString ∨ dt = rdfLangString) : (dt == rdfXMLLiteral) = false := by
  rcases h with rfl | rfl <;> decide +kernel

theorem promote_cases (ls : WfLiteral) (hn : L4Factoidal.Fn.Comparison.numericDatatype ls.val.datatype = false) :
    literalPromote ls = .term (.literal ls) ∨ ∃ b, literalPromote ls = .bool b ∧ ls.val.datatype = RDF.xsdBoolean := by
  have hdi : (ls.val.datatype == RDF.xsdInteger) = false := by
    cases e : (ls.val.datatype == RDF.xsdInteger)
    · rfl
    · rw [beq_iff_eq] at e; rw [e, numDt_true.1] at hn; cases hn
  have hdd : (ls.val.datatype == RDF.xsdDecimal) = false := by
    cases e : (ls.val.datatype == RDF.xsdDecimal)
    · rfl
    · rw [beq_iff_eq] at e; rw [e, numDt_true.2.1] at hn; cases hn
  have hdb : (ls.val.datatype == RDF.xsdDouble) = false := by
    cases e : (ls.val.datatype == RDF.xsdDouble)
    · rfl
    · rw [beq_iff_eq] at e; rw [e, numDt_true.2.2.1] at hn; cases hn
  have hdf : (ls.val.datatype == SPARQL.xsdFloat) = false := by
    cases e : (ls.val.datatype == SPARQL.xsdFloat)
    · rfl
    · rw [beq_iff_eq] at e; rw [e, numDt_true.2.2.2] at hn; cases hn
  unfold literalPromote
  simp only [hdi, hdd, hdb, hdf, Bool.false_eq_true, if_false, Bool.or_false]
  split
  · next hbo =>
    rw [beq_iff_eq] at hbo
    split
    · exact Or.inr ⟨true, rfl, hbo⟩
    · exact Or.inr ⟨true, rfl, hbo⟩
    · exact Or.inr ⟨false, rfl, hbo⟩
    · exact Or.inr ⟨false, rfl, hbo⟩
    · exact Or.inl rfl
  · exact Or.inl rfl

theorem lit_vc (ls lt : WfLiteral) (hdt : lt.val.datatype = xsdString ∨ lt.val.datatype = rdfLangString) :
    (valueCompare (.term (.literal ls)) (.term (.literal lt)) .eq).getD false = Literal.eqb lt.val ls.val ∧
    (valueCompare (.term (.literal lt)) (.term (.literal ls)) .eq).getD false = Literal.eqb lt.val ls.val := by
  have hnt : L4Factoidal.Fn.Comparison.numericDatatype lt.val.datatype = false := numDt_false _ hdt
  have hpt : literalPromote lt = .term (.literal lt) := promote_const lt hdt
  have hx : (lt.val.datatype == rdfXMLLiteral) = false := notXml _ hdt
  have hlv : L4Factoidal.Fn.Numeric.literalValue? lt.val = none := lexicalValue_none _ _ hdt
  by_cases hn : L4Factoidal.Fn.Comparison.numericDatatype ls.val.datatype = true
  · have hne : (lt.val.datatype == ls.val.datatype) = false := by
      cases e : (lt.val.datatype == ls.val.datatype)
      · rfl
      · rw [beq_iff_eq] at e; rw [e] at hnt; rw [hnt] at hn; cases hn
    have hst1 : ls.val.sameTerm lt.val = false := by
      simp only [Literal.sameTerm, Bool.and_eq_false_iff]
      left; left; right
      cases e : (ls.val.datatype == lt.val.datatype)
      · rfl
      · rw [beq_iff_eq] at e; rw [e, beq_self_eq_true] at hne; cases hne
    have hst2 : lt.val.sameTerm ls.val = false := by
      simp only [Literal.sameTerm, Bool.and_eq_false_iff]
      left; left; right; exact hne
    have heq : Literal.eqb lt.val ls.val = false := by
      simp only [Literal.eqb, hne, Bool.and_false, Bool.false_and]
    rw [heq]
    constructor
    · simp only [valueCompare, EvalResult.isNumericOperand, hn, Bool.true_or, if_true, numericEquality,
        numericValueCompare, EvalResult.numericValue?, hlv, hst1]
      cases L4Factoidal.Fn.Numeric.literalValue? ls.val <;> rfl
    · simp only [valueCompare, EvalResult.isNumericOperand, hn, Bool.or_true, if_true, numericEquality,
        numericValueCompare, EvalResult.numericValue?, hlv, hst2]
      rfl
  · have hn' : L4Factoidal.Fn.Comparison.numericDatatype ls.val.datatype = false := by simpa using hn
    have hpc := promote_cases ls hn'
    have hbool : RDF.xsdBoolean ≠ lt.val.datatype := by
      rcases hdt with h | h <;> rw [h] <;> decide +kernel
    have hlr : (Literal.eqb lt.val ls.val) = ((lt.val.lexicalForm == ls.val.lexicalForm) &&
        (lt.val.datatype == ls.val.datatype) && langTagOptionEq lt.val.langTag ls.val.langTag &&
        (lt.val.direction == ls.val.direction)) := by
      simp only [Literal.eqb, hx, Bool.false_and, Bool.false_eq_true, if_false]
    constructor
    · simp only [valueCompare, EvalResult.isNumericOperand, hn', hnt, Bool.or_false, Bool.false_eq_true, if_false,
        EvalResult.promoteLiteral, hpt]
      rcases hpc with hp | ⟨b, hp, hb⟩
      · rw [hp]
        simp only []
        rw [hlr]
        by_cases hd : ls.val.datatype = lt.val.datatype
        · simp only [hd, beq_self_eq_true, if_true, Bool.true_and, Bool.and_true]
          rw [langTagOptionEq_symm]
          cases langTagOptionEq lt.val.langTag ls.val.langTag <;>
            cases hdir : (lt.val.direction == ls.val.direction) <;> simp [applyCompOp, strCompare_eq_zero, hdir]
          · rw [if_neg (fun e => by simp [e] at hdir)]; rfl
          · rw [if_pos (by simp only [beq_iff_eq] at hdir; exact hdir.symm)]
            by_cases h : ls.val.lexicalForm = lt.val.lexicalForm
            · simp [h]
            · have h' : ¬ lt.val.lexicalForm = ls.val.lexicalForm := fun e => h e.symm
              rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr h']; rfl
        · have hd' : (ls.val.datatype == lt.val.datatype) = false := beq_eq_false_iff_ne.mpr hd
          have hd'' : (lt.val.datatype == ls.val.datatype) = false := beq_eq_false_iff_ne.mpr (Ne.symm hd)
          simp only [hd', hd'', Bool.false_eq_true, if_false, Bool.and_false, Bool.false_and]
          rfl
      · rw [hp]
        have hd'' : (lt.val.datatype == ls.val.datatype) = false := by
          rw [hb]; exact beq_eq_false_iff_ne.mpr (Ne.symm hbool)
        rw [hlr, hd'']
        simp only [Bool.and_false, Bool.false_and]
        rfl
    · simp only [valueCompare, EvalResult.isNumericOperand, hn', hnt, Bool.or_false, Bool.false_eq_true, if_false,
        EvalResult.promoteLiteral, hpt]
      rcases hpc with hp | ⟨b, hp, hb⟩
      · rw [hp]
        simp only []
        rw [hlr]
        by_cases hd : ls.val.datatype = lt.val.datatype
        · simp only [hd, beq_self_eq_true, if_true, Bool.true_and, Bool.and_true]
          cases langTagOptionEq lt.val.langTag ls.val.langTag <;>
            cases hdir : (lt.val.direction == ls.val.direction) <;> simp [applyCompOp, strCompare_eq_zero, hdir]
        · have hd' : (ls.val.datatype == lt.val.datatype) = false := beq_eq_false_iff_ne.mpr hd
          have hd'' : (lt.val.datatype == ls.val.datatype) = false := beq_eq_false_iff_ne.mpr (Ne.symm hd)
          simp only [hd', hd'', Bool.false_eq_true, if_false, Bool.and_false, Bool.false_and]
          rfl
      · rw [hp]
        have hd'' : (lt.val.datatype == ls.val.datatype) = false := by
          rw [hb]; exact beq_eq_false_iff_ne.mpr (Ne.symm hbool)
        rw [hlr, hd'']
        simp only [Bool.and_false, Bool.false_and]
        rfl

theorem iri_beq (i j : WfIri) : (i.val == j.val) = (i == j) := by
  by_cases h : i = j
  · subst h; simp
  · have h' : i.val ≠ j.val := fun e => h (Subtype.ext e)
    rw [beq_eq_false_iff_ne.mpr h', beq_eq_false_iff_ne.mpr h]

theorem lit_iri_vc (ls : WfLiteral) (i : WfIri) :
    (valueCompare (.term (.literal ls)) (.term (.iri i)) .eq).getD false = false ∧
    (valueCompare (.term (.iri i)) (.term (.literal ls)) .eq).getD false = false := by
  by_cases hn : L4Factoidal.Fn.Comparison.numericDatatype ls.val.datatype = true
  · constructor
    · simp only [valueCompare, EvalResult.isNumericOperand, hn, Bool.true_or, if_true, numericEquality,
        numericValueCompare, EvalResult.numericValue?]
      cases L4Factoidal.Fn.Numeric.literalValue? ls.val <;> rfl
    · simp only [valueCompare, EvalResult.isNumericOperand, hn, Bool.or_true, if_true, numericEquality,
        numericValueCompare, EvalResult.numericValue?]
      rfl
  · have hn' : L4Factoidal.Fn.Comparison.numericDatatype ls.val.datatype = false := by simpa using hn
    rcases promote_cases ls hn' with hp | ⟨b, hp, _⟩
    · constructor
      · simp only [valueCompare, EvalResult.isNumericOperand, hn', Bool.or_false, Bool.false_eq_true, if_false,
          EvalResult.promoteLiteral, hp]
        rfl
      · simp only [valueCompare, EvalResult.isNumericOperand, hn', Bool.or_false, Bool.false_or,
          Bool.false_eq_true, if_false, EvalResult.promoteLiteral, hp]
        rfl
    · constructor
      · simp only [valueCompare, EvalResult.isNumericOperand, hn', Bool.or_false, Bool.false_eq_true, if_false,
          EvalResult.promoteLiteral, hp]
        rfl
      · simp only [valueCompare, EvalResult.isNumericOperand, hn', Bool.or_false, Bool.false_or,
          Bool.false_eq_true, if_false, EvalResult.promoteLiteral, hp]
        rfl

/-- **`=` with a constant of term identity.** For a constant `eqByTermConst?`
    accepts, `=` with any term is `Term.eqb` of the two, both ways round. -/
theorem vc_const (s t : Term) (ht : EqConst t) :
    (valueCompare (.term s) (.term t) .eq).getD false = t.eqb s ∧
    (valueCompare (.term t) (.term s) .eq).getD false = t.eqb s := by
  cases t with
  | iri i =>
    cases s with
    | iri j =>
      simp only [valueCompare, EvalResult.isNumericOperand, Bool.or_false, Bool.false_eq_true, if_false,
        EvalResult.promoteLiteral, applyCompOp, strCompare_eq_zero, Option.getD_some, Term.eqb, iri_beq]
      constructor
      · rw [show (j == i) = (i == j) from by
          by_cases h : i = j
          · subst h; rfl
          · rw [beq_eq_false_iff_ne.mpr h, beq_eq_false_iff_ne.mpr (Ne.symm h)]]
      · trivial
    | literal ls =>
      obtain ⟨h1, h2⟩ := lit_iri_vc ls i
      exact ⟨h1, h2⟩
    | bnode _ => exact ⟨rfl, rfl⟩
    | tripleTerm _ _ _ => exact ⟨rfl, rfl⟩
  | literal lt =>
    obtain ⟨_, hdt⟩ := ht
    cases s with
    | literal ls => exact lit_vc ls lt hdt
    | iri j =>
      have hnt := numDt_false _ hdt
      have hpt := promote_const lt hdt
      constructor
      · simp only [valueCompare, EvalResult.isNumericOperand, hnt, Bool.or_false, Bool.false_or,
          Bool.false_eq_true, if_false, EvalResult.promoteLiteral, hpt]
        rfl
      · simp only [valueCompare, EvalResult.isNumericOperand, hnt, Bool.or_false, Bool.false_or,
          Bool.false_eq_true, if_false, EvalResult.promoteLiteral, hpt]
        rfl
    | bnode _ =>
      have hnt := numDt_false _ hdt
      have hpt := promote_const lt hdt
      constructor
      · simp only [valueCompare, EvalResult.isNumericOperand, hnt, Bool.or_false, Bool.false_or,
          Bool.false_eq_true, if_false, EvalResult.promoteLiteral, hpt]
        rfl
      · simp only [valueCompare, EvalResult.isNumericOperand, hnt, Bool.or_false, Bool.false_or,
          Bool.false_eq_true, if_false, EvalResult.promoteLiteral, hpt]
        rfl
    | tripleTerm _ _ _ =>
      have hnt := numDt_false _ hdt
      have hpt := promote_const lt hdt
      constructor
      · simp only [valueCompare, EvalResult.isNumericOperand, hnt, Bool.or_false, Bool.false_or,
          Bool.false_eq_true, if_false, EvalResult.promoteLiteral, hpt]
        rfl
      · simp only [valueCompare, EvalResult.isNumericOperand, hnt, Bool.or_false, Bool.false_or,
          Bool.false_eq_true, if_false, EvalResult.promoteLiteral, hpt]
        rfl
  | bnode _ => exact ht.elim
  | tripleTerm _ _ _ => exact ht.elim

theorem term_sameTerm_refl : ∀ (t : Term), t.sameTerm t = true
  | .iri _ => by simp [Term.sameTerm]
  | .bnode _ => by simp [Term.sameTerm]
  | .literal _ => by simp [Term.sameTerm]
  | .tripleTerm _ _ o => by simp [Term.sameTerm, term_sameTerm_refl o]

theorem langTagOptionEq_toLower (a : String) (b : Option String) :
    langTagOptionEq (some a.toLower) b = langTagOptionEq (some a) b := by
  cases b <;> simp [langTagOptionEq, langTagEq, string_toLower_idem]

theorem normalizeLit_cases (l : WfLiteral) : normalizeLit l = .literal l ∨
    ∃ (v : WfLiteral) (tag : String), normalizeLit l = .literal v ∧ l.val.langTag = some tag ∧
      v.val = { l.val with langTag := some tag.toLower } := by
  unfold normalizeLit
  split
  · exact Or.inl rfl
  · next tag h =>
    simp only []
    by_cases hw : literalWf { l.val with langTag := some tag.toLower } = true
    · rw [dif_pos hw]; exact Or.inr ⟨⟨_, hw⟩, tag, rfl, h, rfl⟩
    · rw [dif_neg hw]; exact Or.inl rfl

/-- `normalizeTerm` changes no answer of `Term.eqb`: it folds language tags,
    and `Term.eqb` compares them without case. -/
theorem eqb_normalize : ∀ (t s : Term), (normalizeTerm t).eqb s = t.eqb s
  | .iri _, _ => rfl
  | .bnode _, _ => rfl
  | .literal l, s => by
    show (normalizeLit l).eqb s = _
    rcases normalizeLit_cases l with h | ⟨v, tag, h, ht, hv⟩
    · rw [h]
    · rw [h]
      cases s with
      | literal ls =>
        simp only [Term.eqb, Literal.eqb, hv, ht, langTagOptionEq_toLower]
      | _ => rfl
  | .tripleTerm s p o, s' => by
    cases s' with
    | tripleTerm s2 p2 o2 =>
      simp only [normalizeTerm, Term.eqb, eqb_normalize o o2]
    | _ => rfl

theorem normalize_sameTerm (t : Term) (ht : ∀ s p o, t ≠ .tripleTerm s p o) : (normalizeTerm t).sameTerm t = true := by
  cases t with
  | iri _ => simp [normalizeTerm, Term.sameTerm]
  | bnode _ => simp [normalizeTerm, Term.sameTerm]
  | literal l =>
    show (normalizeLit l).sameTerm (.literal l) = true
    rcases normalizeLit_cases l with h | ⟨v, tag, h, htag, hv⟩
    · rw [h]; simp [Term.sameTerm]
    · rw [h]
      simp only [Term.sameTerm, Literal.sameTerm, hv, htag, langTagOptionEq_toLower]
      simp
  | tripleTerm s p o => exact absurd rfl (ht s p o)

theorem normalize_idem (t : Term) : normalizeTerm (normalizeTerm t) = normalizeTerm t := by
  induction t with
  | iri _ => rfl
  | bnode _ => rfl
  | literal l =>
    show normalizeTerm (normalizeLit l) = normalizeLit l
    rcases normalizeLit_cases l with h | ⟨v, tag, h, htag, hv⟩
    · rw [h]; exact h
    · rw [h]
      show normalizeLit v = .literal v
      unfold normalizeLit
      rw [show v.val.langTag = some tag.toLower by rw [hv]]
      simp only []
      have hvv : ({ v.val with langTag := some tag.toLower.toLower } : Literal) = v.val := by
        rw [hv, string_toLower_idem]
      by_cases hw : literalWf { v.val with langTag := some tag.toLower.toLower } = true
      · rw [dif_pos hw]
        congr 1
        exact Subtype.ext hvv
      · rw [dif_neg hw]
  | tripleTerm s p o ih =>
    simp only [normalizeTerm, ih]

/-! ## The conjuncts the id path compiles, on a solution mapping -/

theorem eval_eqConst (env : EvalEnv) (mu : Binding) (ce : Expr) (t : Term) (h : eqByTermConst? ce = some t) :
    Expr.evalIn env mu ce = .term t := by
  cases ce <;> simp only [eqByTermConst?, reduceCtorEq] at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

theorem eval_sameConst (env : EvalEnv) (mu : Binding) (ce : Expr) (t : Term) (h : sameTermConst? ce = some t) :
    Expr.evalIn env mu ce = .term t := by
  cases ce <;> simp only [sameTermConst?, reduceCtorEq, Option.some.injEq] at h
  · subst h; rfl
  · subst h; rfl

theorem sameConst_shape (ce : Expr) (t : Term) (h : sameTermConst? ce = some t) :
    ∀ s p o, t ≠ .tripleTerm s p o := by
  cases ce <;> simp only [sameTermConst?, reduceCtorEq, Option.some.injEq] at h
  · subst h; intro _ _ _ e; cases e
  · subst h; intro _ _ _ e; cases e

theorem ebv_compare (r : Option Bool) :
    ebvOrFalse (match r with | some b => EvalResult.bool b | none => .error) = r.getD false := by
  cases r <;> rfl

/-- `?v = c` and `c = ?v` with a constant of term identity, on a mapping
    that binds `?v` to `s`: `Term.eqb` of `c` and `s`. -/
theorem eq_row (env : EvalEnv) (mu : Binding) (v : String) (ce : Expr) (t s : Term)
    (hc : eqByTermConst? ce = some t) (hv : mu.lookup v = some s) :
    ebvOrFalse (Expr.evalIn env mu (.compare .eq (.var v) ce)) = t.eqb s ∧
    ebvOrFalse (Expr.evalIn env mu (.compare .eq ce (.var v))) = t.eqb s := by
  have h := vc_const s t (eqConst_of ce t hc)
  simp only [Expr.evalIn, hv, eval_eqConst env mu ce t hc]
  obtain ⟨h1, h2⟩ := h
  constructor
  · rw [← h1]; cases valueCompare (EvalResult.term s) (EvalResult.term t) CompOp.eq <;> rfl
  · rw [← h2]; cases valueCompare (EvalResult.term t) (EvalResult.term s) CompOp.eq <;> rfl

theorem sameTerm_symm_const (s t : Term) (ht : ∀ a p o, t ≠ .tripleTerm a p o) : s.sameTerm t = t.sameTerm s := by
  cases t with
  | iri i => cases s <;> simp [Term.sameTerm, BEq.comm]
  | bnode b => cases s <;> simp [Term.sameTerm, BEq.comm]
  | literal l =>
    cases s with
    | literal ls =>
      simp only [Term.sameTerm, Literal.sameTerm, langTagOptionEq_symm]
      rw [BEq.comm (a := ls.val.lexicalForm), BEq.comm (a := ls.val.datatype),
        BEq.comm (a := ls.val.direction)]
    | _ => rfl
  | tripleTerm a p o => exact absurd rfl (ht a p o)

/-- `sameTerm(?v, c)` and `sameTerm(c, ?v)` on a mapping that binds `?v` to
    `s`: `Term.sameTerm` of the two. -/
theorem sameTerm_row (env : EvalEnv) (mu : Binding) (v : String) (ce : Expr) (t s : Term)
    (hc : sameTermConst? ce = some t) (hv : mu.lookup v = some s) :
    ebvOrFalse (Expr.evalIn env mu (.sameTerm (.var v) ce)) = s.sameTerm t ∧
    ebvOrFalse (Expr.evalIn env mu (.sameTerm ce (.var v))) = s.sameTerm t := by
  simp only [Expr.evalIn, hv, eval_sameConst env mu ce t hc, EvalResult.toTerm?]
  exact ⟨rfl, by rw [sameTerm_symm_const s t (sameConst_shape ce t hc)]; rfl⟩

theorem sameTermVar_row (env : EvalEnv) (mu : Binding) (v w : String) (s s' : Term)
    (hv : mu.lookup v = some s) (hw : mu.lookup w = some s') :
    ebvOrFalse (Expr.evalIn env mu (.sameTerm (.var v) (.var w))) = s.sameTerm s' := by
  simp only [Expr.evalIn, hv, hw, EvalResult.toTerm?]
  rfl

/-! ## On ids -/

section ids
open L4Factoidal.Storage.Sbm11.IdLeaf (CidOk)

/-- **`=` on ids.** With a dictionary lookup `cid` exact on the ids in `ok`
    (`CidOk`), the id test of `?v = c` (the id of `normalizeTerm c`, no row
    when it has none) is `Term.eqb` of `c` and the decoded id. -/
theorem eq_ids (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop) (t : Term)
    (hcid : CidOk dec ok (normalizeTerm t) (cid (normalizeTerm t))) (y : UInt64) (hy : ok y) :
    (match cid (normalizeTerm t) with | some x => y == x | none => false) = t.eqb (dec y) := by
  have h := hcid
  rw [← eqb_normalize t (dec y)]
  cases e : cid (normalizeTerm t) with
  | some x =>
    rw [e] at h
    simp only [CidOk] at h
    rw [h y hy, BEq.comm]
  | none =>
    rw [e] at h
    simp only [CidOk] at h
    rw [h y hy]

/-- **`sameTerm` with a constant on ids.** With `CidOk` on `ok` and a lookup
    that answers the id of the term itself, folded (`hcidN`), the id test of
    `sameTerm(?v, c)` is `Term.sameTerm` of the decoded id and `c`. -/
theorem same_ids (cid : Term → Option UInt64) (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (t : Term) (hcid : CidOk dec ok (normalizeTerm t) (cid (normalizeTerm t)))
    (ht : ∀ a p o, t ≠ .tripleTerm a p o) (y : UInt64) (hy : ok y) :
    (match cid (normalizeTerm t) with | some x => y == x | none => false) = (dec y).sameTerm t := by
  have h := hcid
  have hne : (normalizeTerm t).eqb (dec y) = false → (dec y).sameTerm t = false := by
    intro he
    cases hs : (dec y).sameTerm t
    · rfl
    · have h1 := Term.eqb_of_sameTerm hs
      rw [Term.eqb_symm, ← eqb_normalize] at h1
      rw [he] at h1; cases h1
  cases e : cid (normalizeTerm t) with
  | some x =>
    rw [e] at h
    simp only [CidOk] at h
    show (y == x) = _
    by_cases hxy : y = x
    · subst hxy
      have hd := hcidN _ _ e
      rw [normalize_idem] at hd
      rw [hd, beq_self_eq_true]
      exact (normalize_sameTerm t ht).symm
    · rw [beq_eq_false_iff_ne.mpr hxy]
      have := h y hy
      rw [beq_eq_false_iff_ne.mpr (Ne.symm hxy)] at this
      exact (hne this).symm
  | none =>
    rw [e] at h
    simp only [CidOk] at h
    exact (hne (h y hy)).symm

/-- **`sameTerm(?v, ?w)` on ids.** When `Term.eqb` of two decoded ids in `ok`
    is id equality (`hdec`), id equality is `Term.sameTerm` of the decoded
    terms. -/
theorem var_ids (dec : UInt64 → Term) (ok : UInt64 → Prop)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y)) (x y : UInt64) (hx : ok x) (hy : ok y) :
    (x == y) = (dec x).sameTerm (dec y) := by
  by_cases h : x = y
  · subst h; rw [beq_self_eq_true, term_sameTerm_refl]
  · rw [beq_eq_false_iff_ne.mpr h]
    cases hs : (dec x).sameTerm (dec y)
    · rfl
    · have := Term.eqb_of_sameTerm hs
      rw [hdec x y hx hy, beq_eq_false_iff_ne.mpr h] at this
      cases this

end ids

/-! ## `compileFilter` -/

/-- A conjunct `compileFilter` compiles to a string test on dictionary keys
    (`FKind.str`, `FKind.strRange`): STRSTARTS, STRENDS or CONTAINS of a
    variable and a simple literal. Not proved here. -/
def StrForm : Expr → Prop
  | .strStarts (.var _) c | .strEnds (.var _) c | .contains (.var _) c => simpleNeedle? c ≠ none
  | _ => False

/-- What `compileFilter` compiles a conjunct to. -/
def KOk (cid : Term → Option UInt64) (cj : Expr) (k : FKind) : Prop :=
  (∃ v ce t, (cj = .compare .eq (.var v) ce ∨ cj = .compare .eq ce (.var v)) ∧ eqByTermConst? ce = some t ∧
      k = .idEq v (cid (normalizeTerm t))) ∨
  (∃ v w, cj = .sameTerm (.var v) (.var w) ∧ k = .idEqVar v w) ∨
  (∃ v ce t, (cj = .sameTerm (.var v) ce ∨ cj = .sameTerm ce (.var v)) ∧ sameTermConst? ce = some t ∧
      k = .idEq v (cid (normalizeTerm t))) ∨
  (∃ vs, exprVars cj = some vs ∧ k = .general cj vs)

/-- **`compileFilter` on a store whose dictionary lookup is `cid`.** -/
theorem compile_spec (st : Store Id) (cid : Term → Option UInt64) (hid : ∀ t, st.idOf t = pure (cid t))
    (cj : Expr) (hns : ¬ StrForm cj) (vs : Array String) (hev : exprVars cj = some vs) :
    ∃ k, compileFilter st cj = pure k ∧ KOk cid cj k := by
  have hg : KOk cid cj (.general cj vs) := Or.inr (Or.inr (Or.inr ⟨vs, hev, rfl⟩))
  unfold compileFilter
  simp only [hev]
  split
  · next v c =>
    cases ht : eqByTermConst? c with
    | some t => exact ⟨_, by simp only [hid]; rfl, Or.inl ⟨v, c, t, Or.inl rfl, ht, rfl⟩⟩
    | none => exact ⟨_, rfl, hg⟩
  · next c v _ =>
    cases ht : eqByTermConst? c with
    | some t => exact ⟨_, by simp only [hid]; rfl, Or.inl ⟨v, c, t, Or.inr rfl, ht, rfl⟩⟩
    | none => exact ⟨_, rfl, hg⟩
  · next v w => exact ⟨_, rfl, Or.inr (Or.inl ⟨v, w, rfl, rfl⟩)⟩
  · next v c _ =>
    cases ht : sameTermConst? c with
    | some t => exact ⟨_, by simp only [hid]; rfl, Or.inr (Or.inr (Or.inl ⟨v, c, t, Or.inl rfl, ht, rfl⟩))⟩
    | none => exact ⟨_, rfl, hg⟩
  · next c v _ =>
    cases ht : sameTermConst? c with
    | some t => exact ⟨_, by simp only [hid]; rfl, Or.inr (Or.inr (Or.inl ⟨v, c, t, Or.inr rfl, ht, rfl⟩))⟩
    | none => exact ⟨_, rfl, hg⟩
  · next v c =>
    have : simpleNeedle? c = none := by simpa [StrForm] using hns
    simp only [this]
    exact ⟨_, rfl, hg⟩
  · next v c =>
    have : simpleNeedle? c = none := by simpa [StrForm] using hns
    simp only [this]
    exact ⟨_, rfl, hg⟩
  · next v c =>
    have : simpleNeedle? c = none := by simpa [StrForm] using hns
    simp only [this]
    exact ⟨_, rfl, hg⟩
  · exact ⟨_, rfl, hg⟩

/-! ## Every variable `exprVars` lists is read -/

/-- The variables output and the names read by the expressions on the stack
    are names `e` reads. -/
def SoundP (e : Expr) (s : Option (Option (Array String)) × Array Expr × Array String) : Prop :=
  (∀ w ∈ s.2.2.toList, w ∈ e.refVars) ∧ ∀ y ∈ s.2.1.toList, ∀ w ∈ y.refVars, w ∈ e.refVars

theorem sstep_gen {e : Expr} {st newst : Array Expr} {out out' : Array String} {x : Expr}
    (r : Option (Option (Array String)))
    (hb : st.back? = some x) (hinv : SoundP e (r, st, out))
    (hpop : ∀ y ∈ newst.toList, y ∈ st.pop.toList ∨ ∀ w ∈ y.refVars, w ∈ x.refVars)
    (hout : ∀ w ∈ out'.toList, w ∈ out.toList ∨ w ∈ x.refVars) :
    SoundP e (r, newst, out') := by
  obtain ⟨h1, h2⟩ := hinv
  simp only [] at h1 h2
  have hx : ∀ w ∈ x.refVars, w ∈ e.refVars := h2 x (by rw [back_pop hb]; simp)
  refine ⟨fun w hw => ?_, fun y hy w hw => ?_⟩
  · rcases hout w hw with h | h
    · exact h1 w h
    · exact hx w h
  · rcases hpop y hy with h | h
    · exact h2 y (by rw [back_pop hb]; exact List.mem_append.mpr (Or.inl h)) w hw
    · exact hx w (h w hw)

theorem sstep_kids {e : Expr} {st newst : Array Expr} {out : Array String} {x : Expr}
    (hb : st.back? = some x) (hinv : SoundP e (none, st, out)) (kids : List Expr)
    (hnew : ∀ y, y ∈ newst.toList → y ∈ st.pop.toList ∨ y ∈ kids)
    (hx : x.refVars = Expr.refVarsList kids) :
    SoundP e (none, newst, out) := by
  refine sstep_gen none hb hinv (fun y hy => ?_) (fun w hw => Or.inl hw)
  rcases hnew y hy with h | h
  · exact Or.inl h
  · right; intro w hw; rw [hx]; exact (mem_refVarsList w kids).mpr ⟨y, h, hw⟩

theorem sstep_leaf {e : Expr} {st : Array Expr} {out : Array String} {x : Expr} {r : Option (Option (Array String))}
    (hb : st.back? = some x) (hinv : SoundP e (none, st, out)) :
    SoundP e (r, st.pop, out) :=
  sstep_gen r hb hinv (fun y hy => Or.inl hy) (fun w hw => Or.inl hw) |> fun h => ⟨h.1, h.2⟩

theorem sstep_var {e : Expr} {st : Array Expr} {out out' : Array String} {x : Expr} {v : String}
    (hb : st.back? = some x) (hinv : SoundP e (none, st, out)) (hx : x.refVars = [v])
    (hout : ∀ w ∈ out'.toList, w ∈ out.toList ∨ w = v) :
    SoundP e (none, st.pop, out') :=
  sstep_gen none hb hinv (fun y hy => Or.inl hy) (fun w hw => by
    rcases hout w hw with h | h
    · exact Or.inl h
    · right; rw [hx, h]; simp)

/-- **Every variable `exprVars` lists is read.** -/
theorem exprVars_sound (e : Expr) (vs : Array String) (h : exprVars e = some vs) :
    ∀ w ∈ vs.toList, w ∈ e.refVars := by
  unfold exprVars at h
  simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range'] at h
  generalize hF : forIn (m := Id) (List.range' 0 _) _ _ = F at h
  have hI := forIn_pq (fun s => s.1 = none ∧ SoundP e s) (fun s => (s.1 = none ∨ s.1 = some none) ∧ SoundP e s) _ hF
    ⟨rfl, fun w hw => by simp at hw, fun y hy w hw => by simp at hy; subst hy; exact hw⟩ (by
    intro a s hs
    obtain ⟨ret, st, out⟩ := s
    obtain ⟨hr, hinv⟩ := hs
    simp only [] at hr
    subst hr
    cases hb : st.back? with
    | none =>
      simp only []
      exact done_ok ⟨Or.inl rfl, hinv⟩
    | some x =>
      simp only []
      revert hb
      match x with
      | .iri _ => intro hb; exact yield_ok ⟨rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .lit _ => intro hb; exact yield_ok ⟨rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .boolLit _ => intro hb; exact yield_ok ⟨rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .numericLit _ => intro hb; exact yield_ok ⟨rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .decimalLit _ => intro hb; exact yield_ok ⟨rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .doubleLit _ => intro hb; exact yield_ok ⟨rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .now => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .var v => 
        intro hb; dsimp only; split
        · exact yield_ok ⟨rfl, sstep_var (out' := out.push v) (v := v) hb ⟨hinv.1, hinv.2⟩ (by simp [Expr.refVars]) (fun w hw => by simpa using hw)⟩
        · exact yield_ok ⟨rfl, sstep_var (out' := out) (v := v) hb ⟨hinv.1, hinv.2⟩ (by simp [Expr.refVars]) (fun w hw => Or.inl hw)⟩
      | .bound v => 
        intro hb; dsimp only; split
        · exact yield_ok ⟨rfl, sstep_var (out' := out.push v) (v := v) hb ⟨hinv.1, hinv.2⟩ (by simp [Expr.refVars]) (fun w hw => by simpa using hw)⟩
        · exact yield_ok ⟨rfl, sstep_var (out' := out) (v := v) hb ⟨hinv.1, hinv.2⟩ (by simp [Expr.refVars]) (fun w hw => Or.inl hw)⟩
      | .unaryMinus a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .unaryPlus a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .not a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .isIri a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .isBlank a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .isLiteral a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .isNumeric a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .str a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .lang a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .datatype a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .hasLang a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .hasLangDir a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .langDir a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .strLen a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .uCase a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .lCase a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .encodeForUri a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .abs a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .round a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .ceil a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .floor a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .year a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .month a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .day a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .hours a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .minutes a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .seconds a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .timezone a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .tz a => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .iriFn a => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .md5 a => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .sha1 a => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .sha256 a => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .sha384 a => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .sha512 a => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .ttSubject a => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .ttPredicate a => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .ttObject a => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .isTriple a => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .arith _ a b => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .compare _ a b => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .and a b => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .or a b => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .sameTerm a b => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .strDt a b => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .strLang a b => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .strStarts a b => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .strEnds a b => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .contains a b => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .strBefore a b => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .strAfter a b => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .strLangDir a b c => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b, c] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .cond a b c => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b, c] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .tripleTerm a b c => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .substr a b none => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .substr a b (some c) => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ [a, b, c] (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .regex a b none => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .regex a b (some c) => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .replace a b c none => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .replace a b c (some d) => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .coalesce es => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ es (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .concat es => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ es (by simp) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .functionCall i es => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .inList a es => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ (a :: es) (by intro y hy; simp at hy ⊢; rcases hy with h | h | h <;> simp [h]) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .notInList a es => intro hb; exact yield_ok ⟨rfl, sstep_kids hb ⟨hinv.1, hinv.2⟩ (a :: es) (by intro y hy; simp at hy ⊢; rcases hy with h | h | h <;> simp [h]) (by simp [Expr.refVars, Expr.refVarsList])⟩
      | .existsPat _ => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .notExistsPat _ => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩
      | .aggregate _ _ _ => intro hb; exact done_ok ⟨Or.inr rfl, sstep_leaf hb ⟨hinv.1, hinv.2⟩⟩)
  replace h : Id.run _ = some vs := h
  rw [Id.run_bind] at h
  have hS : (F.run.1 = none ∨ F.run.1 = some none) ∧ SoundP e F.run := by
    rcases hI with ⟨h0, h1⟩ | h1
    · exact ⟨Or.inl h0, h1⟩
    · exact h1
  generalize F.run = S at hS h
  obtain ⟨r, st, out⟩ := S
  obtain ⟨hr, h1, _⟩ := hS
  simp only [] at h1 h hr
  intro w hw
  rcases hr with hr | hr <;> subst hr
  · simp only [] at h
    split at h
    · cases h
    · cases h; exact h1 w hw
  · cases h

/-! ## `colBound` -/

open L4Factoidal.Qlvr (Table) in
/-- `colBound t v`: `v` is a column of `t` and no row leaves it unbound. -/
theorem colBound_spec (t : Table) (v : String) (h : IdGroup.colBound t v = true) :
    ∃ c, t.idx v = some c ∧ ∀ i, i < t.rows → t.at c i ≠ OptJoin.unbound := by
  unfold IdGroup.colBound at h
  cases hc : t.idx v with
  | none => rw [hc] at h; cases h
  | some c =>
    rw [hc] at h
    simp only [Id.run, Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero,
      Nat.add_sub_cancel, Nat.div_one] at h
    refine ⟨c, rfl, ?_⟩
    generalize hF : forIn (m := Id) (List.range' 0 t.rows) _ _ = F at h
    have hI := L4Factoidal.Storage.Sbm11.TableTheorems.forIn_inv'
      (fun k (s : Option Bool × Unit) => s.1 = none ∧ ∀ i, i < k → t.at c i ≠ OptJoin.unbound)
      (fun (s : Option Bool × Unit) => s.1 = some false) hF ⟨rfl, fun i hi => absurd hi (by omega)⟩ (by
        intro a b _ _ ⟨hb, hall⟩
        constructor
        · intro b' e
          split at e
          · cases e
          · next hne =>
            cases e
            refine ⟨rfl, fun i hi => ?_⟩
            rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
            · exact hall i hi
            · simpa using hne
        · intro b' e
          split at e
          · cases e; rfl
          · cases e)
    replace h : Id.run _ = true := h
    rw [Id.run_bind] at h
    rcases hI with ⟨hn, hall⟩ | hs
    · simpa using hall
    · rw [hs] at h; cases h

/-! ## The row test of each compiled conjunct -/

section rows
open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.OptJoin (decRow RowIds unbound idLookup lookup_decRow)
open L4Factoidal.Storage.Sbm11.IdLeaf (CidOk)

/-- The mapping a `general` conjunct is evaluated on: `vs[k]` bound to the
    decoded `ids[k]`. -/
def genMu (dec : UInt64 → Term) (vs : Array String) (ids : List UInt64) : Binding :=
  (List.range vs.size).map fun k => (vs[k]!, dec ids[k]!)

/-- The mapping a `residual` conjunct is evaluated on: `vs[k]` bound to the
    decoded `ids[k]` when it is not `unbound`. -/
def resMu (dec : UInt64 → Term) (vs : Array String) (ids : List UInt64) : Binding :=
  (List.range vs.size).filterMap fun k => if ids[k]! != unbound then some (vs[k]!, dec ids[k]!) else none

/-- The memo key of a `general` conjunct in row `i`. -/
def genKey (t : Table) (vs : Array String) (i : Nat) : List UInt64 :=
  ((vs.filterMap t.idx).map fun c => t.at c i).toList

/-- The memo key of a `residual` conjunct in row `i`. -/
def resKey (t : Table) (vs : Array String) (i : Nat) : List UInt64 :=
  ((vs.map t.idx).map fun c => match c with
    | some c => t.at c i
    | none => unbound).toList

/-- Whether `applyFilters` keeps row `i` of `t` for one conjunct. -/
def keepOf (dec : UInt64 → Term) (t : Table) (i : Nat) : FKind → Bool
  | .idEq v (some x) => match t.idx v with
    | some col => t.at col i == x
    | none => false
  | .idEq _ none => false
  | .idEqVar v w => match t.idx v, t.idx w with
    | some a, some b => t.at a i == t.at b i
    | _, _ => false
  | .general e vs => if (vs.filterMap t.idx).size != vs.size then false else refFilter e (genMu dec vs (genKey t vs i))
  | .residual env e vs => residualHolds env e (resMu dec vs (resKey t vs i))
  | .str _ _ _ _ => false
  | .strRange _ _ _ _ _ => false

/-- The value a memo of `applyFilters` holds for a key. -/
def memoVal (dec : UInt64 → Term) : FKind → List UInt64 → Bool
  | .general e vs, ids => refFilter e (genMu dec vs ids)
  | .residual env e vs, ids => residualHolds env e (resMu dec vs ids)
  | _, _ => false

theorem lookup_eq_of (v : String) (val : Option Term) :
    ∀ (mu : Binding), (∀ p ∈ mu, p.1 = v → some p.2 = val) → (val.isSome → ∃ p ∈ mu, p.1 = v) → mu.lookup v = val
  | [], _, h2 => by
    cases val with
    | none => rfl
    | some _ => obtain ⟨p, hp, _⟩ := h2 rfl; cases hp
  | (w, x) :: rest, h1, h2 => by
    simp only [Binding.lookup]
    by_cases e : w = v
    · simp only [e, if_true]; exact h1 (w, x) List.mem_cons_self e
    · simp only [e, if_false]
      apply lookup_eq_of v val rest (fun p hp => h1 p (List.mem_cons_of_mem _ hp))
      intro hs
      obtain ⟨p, hp, hpv⟩ := h2 hs
      rcases List.mem_cons.mp hp with rfl | hp
      · exact absurd hpv e
      · exact ⟨p, hp, hpv⟩

theorem decRow_lookup (dec : UInt64 → Term) (t : Table) (ht : t.WF) (i : Nat) (v : String) :
    (decRow dec (t.idRow i)).lookup v = (match t.idx v with
      | some c => if t.at c i == unbound then none else some (dec (t.at c i))
      | none => none) := by
  rw [lookup_decRow, L4Factoidal.Storage.Sbm11.TableTheorems.lookup_idRow t ht.nodup]
  unfold Table.lookupAt
  cases t.idx v with
  | none => rfl
  | some c => by_cases h : t.at c i == unbound <;> simp [h]

theorem getElem!_toList_map {α β : Type} [Inhabited β] (a : Array α) (f : α → β) (k : Nat) (hk : k < a.size) :
    (a.map f).toList[k]! = f a[k] := by
  rw [getElem!_pos _ k (by simpa using hk)]
  simp

theorem lookup_resMu (dec : UInt64 → Term) (t : Table) (ht : t.WF) (i : Nat) (vs : Array String) (v : String)
    (hv : v ∈ vs.toList) :
    (resMu dec vs (resKey t vs i)).lookup v = (decRow dec (t.idRow i)).lookup v := by
  rw [decRow_lookup dec t ht i v]
  apply lookup_eq_of
  · intro p hp hpv
    simp only [resMu, List.mem_filterMap, List.mem_range] at hp
    obtain ⟨k, hk, hp⟩ := hp
    split at hp
    · next hne =>
      cases hp
      simp only [] at hpv
      have hkey : (resKey t vs i)[k]! = (match t.idx vs[k] with | some c => t.at c i | none => unbound) := by
        unfold resKey
        rw [getElem!_toList_map _ _ k (by simpa using hk), Array.getElem_map]
      rw [getElem!_pos vs k hk] at hpv
      rw [hkey] at hne ⊢
      subst hpv
      cases hc : t.idx vs[k] with
      | none => rw [hc] at hne; simp at hne
      | some c =>
        rw [hc] at hne
        simp only [] at hne ⊢
        rw [if_neg (by simpa using hne)]
    · cases hp
  · intro hs
    cases hc : t.idx v with
    | none => rw [hc] at hs; cases hs
    | some c =>
      rw [hc] at hs
      simp only [] at hs
      have hne : t.at c i ≠ unbound := by
        intro e; rw [e] at hs; simp at hs
      obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hv
      simp only [Array.length_toList] at hk
      refine ⟨(vs[k]!, dec (resKey t vs i)[k]!), ?_, by rw [getElem!_pos vs k hk]; simpa using hkv⟩
      simp only [resMu, List.mem_filterMap, List.mem_range]
      refine ⟨k, hk, ?_⟩
      have hkey : (resKey t vs i)[k]! = t.at c i := by
        unfold resKey
        rw [getElem!_toList_map _ _ k (by simpa using hk), Array.getElem_map]
        rw [show vs[k] = v by simpa using hkv, hc]
      rw [hkey, if_pos (by simpa using hne)]

theorem filterMap_eq_map {α β : Type} (f : α → Option β) (d : β) :
    ∀ (l : List α), (∀ a ∈ l, (f a).isSome) → l.filterMap f = l.map (fun a => (f a).getD d)
  | [], _ => rfl
  | a :: l, h => by
    have ha := h a List.mem_cons_self
    simp only [List.filterMap_cons, List.map_cons]
    cases e : f a with
    | none => rw [e] at ha; cases ha
    | some b =>
      simp only [Option.getD_some]
      rw [filterMap_eq_map f d l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

theorem filterMap_idx_size (t : Table) (vs : Array String) (hall : ∀ w ∈ vs.toList, (t.idx w).isSome) :
    (vs.filterMap t.idx).size = vs.size := by
  have hl : (vs.filterMap t.idx).toList = vs.toList.map (fun w => (t.idx w).getD 0) := by
    rw [Array.toList_filterMap]; exact filterMap_eq_map _ 0 _ hall
  rw [← Array.length_toList, hl, List.length_map, Array.length_toList]

theorem genKey_get (t : Table) (vs : Array String) (i : Nat)
    (hall : ∀ w ∈ vs.toList, (t.idx w).isSome) (k : Nat) (hk : k < vs.size) :
    (genKey t vs i)[k]! = t.at ((t.idx vs[k]).getD 0) i ∧ (vs.filterMap t.idx).size = vs.size := by
  have hl : (vs.filterMap t.idx).toList = vs.toList.map (fun w => (t.idx w).getD 0) := by
    rw [Array.toList_filterMap]; exact filterMap_eq_map _ 0 _ hall
  have hsz : (vs.filterMap t.idx).size = vs.size := by
    rw [← Array.length_toList, hl, List.length_map, Array.length_toList]
  refine ⟨?_, hsz⟩
  unfold genKey
  rw [getElem!_toList_map _ _ k (by rw [hsz]; exact hk)]
  congr 1
  rw [← Array.getElem_toList]
  simp only [hl, List.getElem_map, Array.getElem_toList]

theorem lookup_genMu (dec : UInt64 → Term) (t : Table) (ht : t.WF) (i : Nat) (vs : Array String) (v : String)
    (hv : v ∈ vs.toList) (hall : ∀ w ∈ vs.toList, ∃ c, t.idx w = some c ∧ t.at c i ≠ unbound) :
    (genMu dec vs (genKey t vs i)).lookup v = (decRow dec (t.idRow i)).lookup v := by
  have hall' : ∀ w ∈ vs.toList, (t.idx w).isSome := fun w hw => by
    obtain ⟨c, hc, _⟩ := hall w hw; rw [hc]; rfl
  rw [decRow_lookup dec t ht i v]
  obtain ⟨c, hc, hne⟩ := hall v hv
  rw [hc]
  show _ = (if (t.at c i == unbound) = true then none else some (dec (t.at c i)))
  rw [if_neg (by simpa using hne)]
  apply lookup_eq_of
  · intro p hp hpv
    simp only [genMu, List.mem_map, List.mem_range] at hp
    obtain ⟨k, hk, rfl⟩ := hp
    simp only [] at hpv ⊢
    rw [getElem!_pos vs k hk] at hpv
    rw [(genKey_get t vs i hall' k hk).1, hpv, hc]
    rfl
  · intro _
    obtain ⟨k, hk, hkv⟩ := List.getElem_of_mem hv
    simp only [Array.length_toList] at hk
    refine ⟨(vs[k]!, dec (genKey t vs i)[k]!), ?_, by rw [getElem!_pos vs k hk]; simpa using hkv⟩
    simp only [genMu, List.mem_map, List.mem_range]
    exact ⟨k, hk, rfl⟩

/-- What the FILTER of the id path needs of one conjunct: no EXISTS, a
    variable list `residualVars` gives, no read of a freshness key (no UUID,
    STRUUID or BNODE call; no variable named like one), and not a string
    test on dictionary keys (`StrForm`, not proved here). -/
structure CjOk (cj : Expr) : Prop where
  ef : cj.existsFree = true
  rv : (residualVars cj).isSome = true
  nofx : ∀ v ∈ cj.refVars, ¬ IsFx v
  nostr : ¬ StrForm cj

/-- **The residual conjunct.** `applyFilters`' test of a `residual`
    conjunct in row `i` is the reference FILTER of the conjunct on the
    decoded row. -/
theorem keep_residual (dec : UInt64 → Term) (t : Table) (ht : t.WF) (i : Nat) (env : EvalEnv) (cj : Expr)
    (hcj : CjOk cj) (vs : Array String) (hvs : residualVars cj = some vs) :
    keepOf dec t i (.residual env cj vs) = ebvOrFalse (Expr.evalIn env (decRow dec (t.idRow i)) cj) := by
  simp only [keepOf, residualHolds,
    L4Factoidal.Storage.Sbm11.IdPostTheorems.substituteExistentials_existsFree env _ _ cj hcj.ef]
  rw [evalIn_congr env env _ (decRow dec (t.idRow i)) cj (fun v hv => ?_) (Or.inr (ExprLocalTheorems.EnvAgree.refl env))]
  rcases residualVars_spec cj vs hvs v hv with h | h
  · exact lookup_resMu dec t ht i vs v h
  · exact absurd h (hcj.nofx v hv)

theorem refFilter_eq (e : Expr) (mu : Binding) : refFilter e mu = ebvOrFalse (Expr.evalIn {} mu e) := rfl

/-- **The general conjunct.** `applyFilters`' test of a `general` conjunct
    (the reference evaluator in the empty environment on the decoded ids of
    `exprVars`) is the reference FILTER, when every variable of `exprVars`
    has a column bound in row `i`. -/
theorem keep_general (dec : UInt64 → Term) (t : Table) (ht : t.WF) (i : Nat) (env : EvalEnv) (cj : Expr)
    (hcj : CjOk cj) (hbl : cj.backendLocal = true) (vs : Array String) (hev : exprVars cj = some vs)
    (hall : ∀ w ∈ vs.toList, ∃ c, t.idx w = some c ∧ t.at c i ≠ unbound) :
    keepOf dec t i (.general cj vs) = ebvOrFalse (Expr.evalIn env (decRow dec (t.idRow i)) cj) := by
  have hall' : ∀ w ∈ vs.toList, (t.idx w).isSome := fun w hw => by
    obtain ⟨c, hc, _⟩ := hall w hw; rw [hc]; rfl
  have hsz := filterMap_idx_size t vs hall'
  simp only [keepOf, hsz, bne_self_eq_false, Bool.false_eq_true, if_false, refFilter_eq]
  rw [evalIn_congr {} env _ (decRow dec (t.idRow i)) cj (fun v hv => ?_) (Or.inl hbl)]
  rcases exprVars_spec cj vs hev v hv with h | h
  · exact lookup_genMu dec t ht i vs v h hall
  · exact absurd h (hcj.nofx v hv)

theorem bound_var (dec : UInt64 → Term) (ok : UInt64 → Prop) (t : Table) (ht : t.WF) (i : Nat)
    (hr : RowIds ok (t.idRow i)) (cj : Expr) (hcj : CjOk cj) (vs : Array String) (hvs : residualVars cj = some vs)
    (hb : ∀ w ∈ vs.toList, ∃ c, t.idx w = some c ∧ t.at c i ≠ unbound) (v : String) (hv : v ∈ cj.refVars) :
    ∃ c, t.idx v = some c ∧ t.at c i ≠ unbound ∧ ok (t.at c i) ∧
      (decRow dec (t.idRow i)).lookup v = some (dec (t.at c i)) := by
  have hvs' : v ∈ vs.toList := by
    rcases residualVars_spec cj vs hvs v hv with h | h
    · exact h
    · exact absurd h (hcj.nofx v hv)
  obtain ⟨c, hc, hne⟩ := hb v hvs'
  have hl : idLookup v (t.idRow i) = some (t.at c i) := by
    rw [L4Factoidal.Storage.Sbm11.TableTheorems.lookup_idRow t ht.nodup]
    unfold Table.lookupAt
    rw [hc]
    simp only []
    rw [if_neg (by simpa using hne)]
  refine ⟨c, hc, hne, hr _ (L4Factoidal.Storage.Sbm11.OptJoin.idLookup_mem hl), ?_⟩
  rw [lookup_decRow, hl]
  rfl

/-- **A compiled conjunct.** For a conjunct `compileFilter` compiles
    (`KOk`) whose variables are bound in row `i`, `applyFilters`' test is the
    reference FILTER of the conjunct on the decoded row. Hypotheses: the
    dictionary lookup `cid` is exact on the ids in `ok` (`CidOk`) and answers
    the folded term itself (`hcidN`), and `Term.eqb` of decoded ids in `ok`
    is id equality (`hdec`). -/
theorem keep_compiled (dec : UInt64 → Term) (ok : UInt64 → Prop) (cid : Term → Option UInt64) (VE : Prop)
    (hcid : ∀ c, ((cid c).isSome = true ∨ VE) → CidOk dec ok c (cid c))
    (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (t : Table) (ht : t.WF) (i : Nat) (hr : RowIds ok (t.idRow i)) (env : EvalEnv) (cj : Expr) (k : FKind)
    (hk : KOk cid cj k) (hve : ∀ v, k = .idEq v none → VE) (hcj : CjOk cj) (hbl : cj.backendLocal = true)
    (vs : Array String)
    (hvs : residualVars cj = some vs) (hb : ∀ w ∈ vs.toList, ∃ c, t.idx w = some c ∧ t.at c i ≠ unbound) :
    keepOf dec t i k = ebvOrFalse (Expr.evalIn env (decRow dec (t.idRow i)) cj) := by
  have hcidk : ∀ v c, k = .idEq v (cid c) → CidOk dec ok c (cid c) := by
    intro v c hkc
    apply hcid
    cases e : cid c with
    | some _ => exact Or.inl rfl
    | none => exact Or.inr (hve v (by rw [hkc, e]))
  have bv := bound_var dec ok t ht i hr cj hcj vs hvs hb
  have hidEq : ∀ v col c', t.idx v = some col →
      keepOf dec t i (.idEq v c') = (match c' with | some x => t.at col i == x | none => false) := by
    intro v col c' hc
    cases c' with
    | none => rfl
    | some x => simp only [keepOf, hc]
  rcases hk with ⟨v, ce, tt, hform, hce, rfl⟩ | ⟨v, w, rfl, rfl⟩ | ⟨v, ce, tt, hform, hce, rfl⟩ | ⟨vs', hev, rfl⟩
  · have hv : v ∈ cj.refVars := by rcases hform with rfl | rfl <;> simp [Expr.refVars]
    obtain ⟨col, hc, _, hok, hl⟩ := bv v hv
    rw [hidEq v col _ hc]
    rw [eq_ids cid dec ok tt (hcidk v _ rfl) _ hok]
    have := eq_row env (decRow dec (t.idRow i)) v ce tt _ hce hl
    rcases hform with rfl | rfl
    · exact this.1.symm
    · exact this.2.symm
  · have hv : v ∈ (Expr.sameTerm (.var v) (.var w)).refVars := by simp [Expr.refVars]
    have hw : w ∈ (Expr.sameTerm (.var v) (.var w)).refVars := by simp [Expr.refVars]
    obtain ⟨a, ha, _, hoka, hla⟩ := bv v hv
    obtain ⟨b, hb', _, hokb, hlb⟩ := bv w hw
    simp only [keepOf, ha, hb']
    rw [var_ids dec ok hdec _ _ hoka hokb, sameTermVar_row env _ v w _ _ hla hlb]
  · have hv : v ∈ cj.refVars := by rcases hform with rfl | rfl <;> simp [Expr.refVars]
    obtain ⟨col, hc, _, hok, hl⟩ := bv v hv
    rw [hidEq v col _ hc]
    have hsh : ∀ a p o, tt ≠ .tripleTerm a p o := by
      intro a p o e
      cases ce <;> simp only [sameTermConst?, reduceCtorEq, Option.some.injEq] at hce
      · subst hce; cases e
      · subst hce; cases e
    rw [same_ids cid dec ok hcidN tt (hcidk v _ rfl) hsh _ hok]
    have := sameTerm_row env (decRow dec (t.idRow i)) v ce tt _ hce hl
    rcases hform with rfl | rfl
    · exact this.1.symm
    · exact this.2.symm
  · apply keep_general dec t ht i env cj hcj hbl vs' hev
    intro w hw
    obtain ⟨c, hc, hne, _, _⟩ := bv w (exprVars_sound cj vs' hev w hw)
    exact ⟨c, hc, hne⟩

end rows

/-! ## The loops of `filterKeep` -/

section loops
open L4Factoidal.Storage.Sbm11.BgpTableTheorems (forIn_exc)

theorem set!_get (a : Array Bool) (i j : Nat) (v : Bool) :
    (a.set! i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by
  simp only [Array.set!]
  by_cases hj : j < a.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos a j hj, Array.getElem_setIfInBounds]
    · by_cases h : i = j
      · subst h; simp [hj]
      · simp [h]
    · exact hj
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg a j hj]
    split
    · next h => exact absurd (h.1 ▸ h.2) hj
    · rfl

theorem set!_size (a : Array Bool) (i : Nat) (v : Bool) : (a.set! i v).size = a.size := by
  simp [Array.set!]

/-- The row loop of a test on ids (`idEq`, `idEqVar`): row `i` stays when it
    was kept and passes `test i`. -/
theorem maskLoop (n : Nat) (test : Nat → Bool) (body : Nat → Array Bool → ExceptT String Id (ForInStep (Array Bool)))
    (hbody : ∀ i kp, i < n → body i kp = pure (.yield (if kp[i]! && !test i then kp.set! i false else kp)))
    (kp0 : Array Bool) (hsz : kp0.size = n) :
    ∃ kp, forIn (List.range' 0 n) kp0 body = pure kp ∧ kp.size = n ∧ ∀ i, i < n → kp[i]! = (kp0[i]! && test i) := by
  obtain ⟨kp, h, hP | hQ⟩ := forIn_exc
    (fun k (kp : Array Bool) => kp.size = n ∧ ∀ i, i < n → kp[i]! = if i < k then (kp0[i]! && test i) else kp0[i]!)
    (fun _ => False) body n 0 kp0 ⟨hsz, fun i _ => by simp⟩ (by
      intro a kp _ ha ⟨hs, hk⟩
      refine Or.inl ⟨_, hbody a kp (by omega), ?_, ?_⟩
      · split <;> simp [set!_size, hs]
      · intro i hi
        by_cases hc : (kp[a]! && !test a) = true
        · rw [if_pos hc, set!_get]
          by_cases hia : a = i
          · subst hia
            rw [if_pos ⟨rfl, by omega⟩, if_pos (Nat.lt_succ_self _)]
            rw [hk a hi, if_neg (Nat.lt_irrefl _)] at hc
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
            rw [hc.1, hc.2]; rfl
          · rw [if_neg (fun e => hia e.1), hk i hi]
            by_cases h2 : i < a
            · simp [h2, show i < a + 1 by omega]
            · have : ¬ i < a + 1 := by omega
              simp [h2, this]
        · rw [if_neg hc]
          by_cases hia : a = i
          · subst hia
            rw [hk a hi, if_neg (Nat.lt_irrefl _), if_pos (Nat.lt_succ_self _)]
            rw [hk a hi, if_neg (Nat.lt_irrefl _)] at hc
            cases h0 : kp0[a]! <;> cases ht : test a <;> simp_all
          · rw [hk i hi]
            by_cases h2 : i < a
            · simp [h2, show i < a + 1 by omega]
            · have : ¬ i < a + 1 := by omega
              simp [h2, this])
  · exact ⟨kp, h, hP.1, fun i hi => by rw [hP.2 i hi, if_pos (by omega)]⟩
  · exact hQ.elim

/-- The row loop of a test that reads decoded terms through a memo
    (`general`, `residual`): row `i` stays when it was kept and passes
    `test i`; the memo keeps the invariant `S`. -/
theorem maskLoopS {σ : Type} (S : σ → Prop) (n : Nat) (test : Nat → Bool)
    (body : Nat → Array Bool × σ → ExceptT String Id (ForInStep (Array Bool × σ)))
    (hbody : ∀ i kp m, i < n → S m → ∃ m', S m' ∧
      body i (kp, m) = pure (.yield (if kp[i]! && !test i then kp.set! i false else kp, m')))
    (kp0 : Array Bool) (m0 : σ) (hsz : kp0.size = n) (hm0 : S m0) :
    ∃ kp m, forIn (List.range' 0 n) (kp0, m0) body = pure (kp, m) ∧ kp.size = n ∧
      (∀ i, i < n → kp[i]! = (kp0[i]! && test i)) ∧ S m := by
  obtain ⟨⟨kp, m⟩, h, hP | hQ⟩ := forIn_exc
    (fun k (st : Array Bool × σ) => st.1.size = n ∧ (∀ i, i < n → st.1[i]! = if i < k then (kp0[i]! && test i) else kp0[i]!) ∧ S st.2)
    (fun _ => False) body n 0 (kp0, m0) ⟨hsz, fun i _ => by simp, hm0⟩ (by
      intro a ⟨kp, m⟩ _ ha ⟨hs, hk, hm⟩
      simp only [] at hs hk hm
      obtain ⟨m', hm', hb⟩ := hbody a kp m (by omega) hm
      refine Or.inl ⟨_, hb, ?_, ?_, hm'⟩
      · split <;> simp [set!_size, hs]
      · intro i hi
        by_cases hc : (kp[a]! && !test a) = true
        · rw [if_pos hc, set!_get]
          by_cases hia : a = i
          · subst hia
            rw [if_pos ⟨rfl, by omega⟩, if_pos (Nat.lt_succ_self _)]
            rw [hk a hi, if_neg (Nat.lt_irrefl _)] at hc
            simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
            rw [hc.1, hc.2]; rfl
          · rw [if_neg (fun e => hia e.1), hk i hi]
            by_cases h2 : i < a
            · simp [h2, show i < a + 1 by omega]
            · have : ¬ i < a + 1 := by omega
              simp [h2, this]
        · rw [if_neg hc]
          by_cases hia : a = i
          · subst hia
            rw [hk a hi, if_neg (Nat.lt_irrefl _), if_pos (Nat.lt_succ_self _)]
            rw [hk a hi, if_neg (Nat.lt_irrefl _)] at hc
            cases h0 : kp0[a]! <;> cases ht : test a <;> simp_all
          · rw [hk i hi]
            by_cases h2 : i < a
            · simp [h2, show i < a + 1 by omega]
            · have : ¬ i < a + 1 := by omega
              simp [h2, this])
  · exact ⟨kp, m, h, hP.1, fun i hi => by rw [hP.2.1 i hi, if_pos (by omega)], hP.2.2⟩
  · exact hQ.elim

/-- A loop that appends one element per index. -/
theorem listLoop {α : Type} (n : Nat) (g : Nat → Option α) (body : Nat → List α → ExceptT String Id (ForInStep (List α)))
    (hbody : ∀ k acc, k < n → body k acc = pure (.yield (match g k with | some x => acc ++ [x] | none => acc))) :
    forIn (List.range' 0 n) [] body = pure ((List.range n).filterMap g) := by
  obtain ⟨r, h, hP | hQ⟩ := forIn_exc (fun k (acc : List α) => acc = (List.range k).filterMap g) (fun _ => False)
    body n 0 [] rfl (by
      intro a acc _ ha hacc
      refine Or.inl ⟨_, hbody a acc (by omega), ?_⟩
      rw [List.range_succ, List.filterMap_append, hacc]
      cases hg : g a <;> simp [hg])
  · rw [h, hP]; simp
  · exact hQ.elim

theorem set!_get' {β : Type} [Inhabited β] (a : Array β) (i j : Nat) (v : β) :
    (a.set! i v)[j]! = if i = j ∧ i < a.size then v else a[j]! := by
  simp only [Array.set!]
  by_cases hj : j < a.size
  · rw [getElem!_pos _ j (by simpa using hj), getElem!_pos a j hj, Array.getElem_setIfInBounds]
    · by_cases h : i = j
      · subst h; simp [hj]
      · simp [h]
    · exact hj
  · rw [getElem!_neg _ j (by simpa using hj), getElem!_neg a j hj]
    split
    · next h => exact absurd (h.1 ▸ h.2) hj
    · rfl

theorem maskLoop' {n : Nat} (test : Nat → Bool) {body : Nat → Array Bool → ExceptT String Id (ForInStep (Array Bool))}
    {kp0 : Array Bool} {G : ExceptT String Id (Array Bool)} (hG : forIn (List.range' 0 n) kp0 body = G)
    (hbody : ∀ i kp, i < n → body i kp = pure (.yield (if kp[i]! && !test i then kp.set! i false else kp)))
    (hsz : kp0.size = n) :
    ∃ kp, G = pure kp ∧ kp.size = n ∧ ∀ i, i < n → kp[i]! = (kp0[i]! && test i) := by
  subst hG; exact maskLoop n test body hbody kp0 hsz

theorem maskLoopS' {σ : Type} (S : σ → Prop) {n : Nat} (test : Nat → Bool)
    {body : Nat → Array Bool × σ → ExceptT String Id (ForInStep (Array Bool × σ))}
    {kp0 : Array Bool} {m0 : σ} {G : ExceptT String Id (Array Bool × σ)}
    (hG : forIn (List.range' 0 n) (kp0, m0) body = G)
    (hbody : ∀ i kp m, i < n → S m → ∃ m', S m' ∧
      body i (kp, m) = pure (.yield (if kp[i]! && !test i then kp.set! i false else kp, m')))
    (hsz : kp0.size = n) (hm0 : S m0) :
    ∃ kp m, G = pure (kp, m) ∧ kp.size = n ∧ (∀ i, i < n → kp[i]! = (kp0[i]! && test i)) ∧ S m := by
  subst hG; exact maskLoopS S n test body hbody kp0 m0 hsz hm0

theorem listLoop' {α : Type} {n : Nat} (g : Nat → Option α) {body : Nat → List α → ExceptT String Id (ForInStep (List α))}
    {G : ExceptT String Id (List α)} (hG : forIn (List.range' 0 n) [] body = G)
    (hbody : ∀ k acc, k < n → body k acc = pure (.yield (match g k with | some x => acc ++ [x] | none => acc))) :
    G = pure ((List.range n).filterMap g) := by
  subst hG; exact listLoop n g body hbody

end loops

/-! ## `filterKeep` -/

section keep
open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.OptJoin (decRow RowIds unbound idLookup)
open L4Factoidal.Storage.Sbm11.BgpTableTheorems (forIn_exc)

/-- The conjuncts `filterKeep_spec` covers: no string test on dictionary keys;
    the variables of a `general` conjunct have columns bound in every row. -/
def KWf (t : Table) : FKind → Prop
  | .str _ _ _ _ | .strRange _ _ _ _ _ => False
  | .general _ vs => ∀ w ∈ vs.toList, ∃ c, t.idx w = some c ∧ ∀ i, i < t.rows → t.at c i ≠ unbound
  | _ => True

/-- Every entry of a memo is the value of its key. -/
def MemoSound (f : List UInt64 → Bool) (m : Memo) : Prop := ∀ ids r, m.get? ids = some r → r = f ids

/-- Every memo is sound for its conjunct. -/
def MemoOk (dec : UInt64 → Term) (fs : Array FKind) (ms : Array Memo) : Prop :=
  ∀ j : Nat, MemoSound (memoVal dec fs[j]!) ms[j]!

theorem memoOk_empty (dec : UInt64 → Term) (fs : Array FKind) : MemoOk dec fs (fs.map fun _ => {}) := by
  intro j ids r h
  by_cases hj : j < fs.size
  · rw [getElem!_pos _ j (by simpa using hj)] at h
    simp at h
  · rw [getElem!_neg _ j (by simpa using hj)] at h
    simp [default] at h

theorem row_mem (t : Table) (ht : t.WF) (i : Nat) (v : String) (c : Nat) (hc : t.idx v = some c)
    (hne : t.at c i ≠ unbound) : (v, t.at c i) ∈ t.idRow i := by
  apply L4Factoidal.Storage.Sbm11.OptJoin.idLookup_mem
  rw [L4Factoidal.Storage.Sbm11.TableTheorems.lookup_idRow t ht.nodup]
  unfold Table.lookupAt
  rw [hc]
  simp only []
  rw [if_neg (by simpa using hne)]

theorem all_range_succ (f : Nat → Bool) (n : Nat) :
    (List.range (n + 1)).all f = ((List.range n).all f && f n) := by
  rw [List.range_succ, List.all_append]; simp

theorem all_range_get (fs : Array FKind) (f : FKind → Bool) :
    (List.range fs.size).all (fun j => f fs[j]!) = fs.toList.all f := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h k hk
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hk
    have := h j (by simpa using hj)
    rwa [getElem!_pos fs j (by simpa using hj), ← Array.getElem_toList] at this
  · intro h j hj
    rw [getElem!_pos fs j hj]
    exact h _ (Array.getElem_mem_toList hj)

/-- The invariant of the loop over the conjuncts. -/
def KeepInv (dec : UInt64 → Term) (t : Table) (fs : Array FKind) (fi : Nat) (s : Array Memo × Array Bool) : Prop :=
  s.2.size = t.rows ∧ (∀ i, i < t.rows → s.2[i]! = (List.range fi).all (fun j => keepOf dec t i fs[j]!)) ∧
    MemoOk dec fs s.1

theorem keepInv_step (dec : UInt64 → Term) (t : Table) (fs : Array FKind) (fi : Nat) (ms ms' : Array Memo)
    (kp kp' : Array Bool) (hI : KeepInv dec t fs fi (ms, kp)) (hsz : kp'.size = t.rows)
    (hkp : ∀ i, i < t.rows → kp'[i]! = (kp[i]! && keepOf dec t i fs[fi]!)) (hm : MemoOk dec fs ms') :
    KeepInv dec t fs (fi + 1) (ms', kp') := by
  refine ⟨hsz, fun i hi => ?_, hm⟩
  rw [hkp i hi, hI.2.1 i hi, all_range_succ]

theorem keepInv_none (dec : UInt64 → Term) (t : Table) (fs : Array FKind) (fi : Nat) (ms : Array Memo)
    (kp : Array Bool) (hI : KeepInv dec t fs fi (ms, kp)) (hk : ∀ i, i < t.rows → keepOf dec t i fs[fi]! = false) :
    KeepInv dec t fs (fi + 1) (ms, Array.replicate t.rows false) :=
  keepInv_step dec t fs fi ms ms kp _ hI (by simp) (fun i hi => by
    rw [hk i hi, Bool.and_false, getElem!_pos _ i (by simpa using hi)]; simp) hI.2.2

theorem forIn_exc' {β : Type} (P : Nat → β → Prop) (Q : β → Prop) {f : Nat → β → ExceptT String Id (ForInStep β)}
    {n : Nat} {b : β} {F : ExceptT String Id β} (hF : forIn (List.range' 0 n) b f = F) (h0 : P 0 b)
    (hs : ∀ a b, a < n → P a b →
        (∃ b', f a b = pure (.yield b') ∧ P (a + 1) b') ∨ (∃ b', f a b = pure (.done b') ∧ Q b')) :
    ∃ b', F = pure b' ∧ (P n b' ∨ Q b') := by
  subst hF
  obtain ⟨b', h1, h2⟩ := forIn_exc P Q f n 0 b h0 (fun a b _ ha hp => hs a b (by omega) hp)
  exact ⟨b', h1, by simpa using h2⟩

/-- **`filterKeep`.** Over a store whose `termOf` decodes the ids of the rows
    of `t` (`dec`), with memos sound for their conjuncts, `filterKeep` keeps
    row `i` exactly when every conjunct's test (`keepOf`) passes. -/
theorem filterKeep_spec (st : Store Id) (dec : UInt64 → Term) (t : Table) (ht : t.WF)
    (hterm : ∀ i, i < t.rows → ∀ p ∈ t.idRow i, st.termOf p.2 = pure (dec p.2))
    (fs : Array FKind) (hfs : ∀ k ∈ fs.toList, KWf t k) (ms : Array Memo) (hms : MemoOk dec fs ms) :
    ∃ keep ms', filterKeep st fs ms t = pure (keep, ms') ∧ keep.size = t.rows ∧
      ∀ i, i < t.rows → keep[i]! = fs.toList.all (keepOf dec t i) := by
  unfold filterKeep
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel,
    Nat.div_one]
  generalize hF : forIn (m := ExceptT String Id) (List.range' 0 fs.size) (ms, Array.replicate t.rows true) _ = F
  obtain ⟨⟨ms', kp⟩, h, hP | hQ⟩ := forIn_exc' (KeepInv dec t fs) (fun _ => False) hF
    ⟨by simp, fun i hi => by
      rw [getElem!_pos (Array.replicate t.rows true) i (by simpa using hi)]; simp, hms⟩ (by
      intro fi ⟨ms1, kp1⟩ hfi hI
      have hfi' : fi < fs.size := hfi
      have hkw : KWf t fs[fi]! := hfs _ (by rw [getElem!_pos fs fi hfi']; exact Array.getElem_mem_toList hfi')
      left
      generalize hk : fs[fi]! = k at hkw ⊢
      cases k with
      | idEq v c =>
        dsimp only
        cases hidx : t.idx v with
        | none =>
          exact ⟨_, rfl, keepInv_none dec t fs fi ms1 kp1 hI (fun i _ => by rw [hk]; cases c <;> simp [keepOf, hidx])⟩
        | some col =>
          cases c with
          | none => exact ⟨_, rfl, keepInv_none dec t fs fi ms1 kp1 hI (fun i _ => by rw [hk]; rfl)⟩
          | some x =>
            dsimp only
            generalize hG : forIn (m := ExceptT String Id) (List.range' 0 t.rows) kp1 _ = G
            obtain ⟨kp', h1, h2, h3⟩ := maskLoop' (fun i => t.at col i == x) hG (fun i kp _ => by
              by_cases h : (kp[i]! && t.at col i != x) = true
              · rw [if_pos h, if_pos (by simpa [bne] using h)]
              · rw [if_neg h, if_neg (by simpa [bne] using h)]) hI.1
            refine ⟨_, by rw [h1]; rfl, keepInv_step dec t fs fi ms1 ms1 kp1 kp' hI h2 (fun i hi => ?_) hI.2.2⟩
            rw [h3 i hi, hk]
            simp [keepOf, hidx]
      | idEqVar v w =>
        dsimp only
        cases hv : t.idx v with
        | none =>
          exact ⟨_, rfl, keepInv_none dec t fs fi ms1 kp1 hI (fun i _ => by rw [hk]; simp [keepOf, hv])⟩
        | some a =>
          cases hw : t.idx w with
          | none =>
            exact ⟨_, rfl, keepInv_none dec t fs fi ms1 kp1 hI (fun i _ => by rw [hk]; simp [keepOf, hv, hw])⟩
          | some b =>
            dsimp only
            generalize hG : forIn (m := ExceptT String Id) (List.range' 0 t.rows) kp1 _ = G
            obtain ⟨kp', h1, h2, h3⟩ := maskLoop' (fun i => t.at a i == t.at b i) hG (fun i kp _ => by
              by_cases h : (kp[i]! && t.at a i != t.at b i) = true
              · rw [if_pos h, if_pos (by simpa [bne] using h)]
              · rw [if_neg h, if_neg (by simpa [bne] using h)]) hI.1
            refine ⟨_, by rw [h1]; rfl, keepInv_step dec t fs fi ms1 ms1 kp1 kp' hI h2 (fun i hi => ?_) hI.2.2⟩
            rw [h3 i hi, hk]
            simp [keepOf, hv, hw]
      | str _ _ _ _ => exact hkw.elim
      | strRange _ _ _ _ _ => exact hkw.elim
      | general e vs =>
        dsimp only
        have hkw' : ∀ w ∈ vs.toList, ∃ c, t.idx w = some c ∧ ∀ i, i < t.rows → t.at c i ≠ unbound := hkw
        have hall' : ∀ w ∈ vs.toList, (t.idx w).isSome := fun w hw => by
          obtain ⟨c, hc, _⟩ := hkw' w hw; rw [hc]; rfl
        have hsz := filterMap_idx_size t vs hall'
        rw [if_neg (by simp [hsz])]
        have hm0 : MemoSound (memoVal dec (.general e vs)) ms1[fi]! := by
          have := hI.2.2 fi; rw [hk] at this; exact this
        generalize hG : forIn (m := ExceptT String Id) (List.range' 0 t.rows) (kp1, ms1[fi]!) _ = G
        obtain ⟨kp', m', h1, h2, h3, h4⟩ := maskLoopS' (MemoSound (memoVal dec (.general e vs)))
          (fun i => keepOf dec t i (.general e vs)) hG (by
            intro i kp m hi hm
            dsimp only
            have hkeep : keepOf dec t i (.general e vs) = refFilter e (genMu dec vs (genKey t vs i)) := by
              simp only [keepOf, hsz, bne_self_eq_false, Bool.false_eq_true, if_false]
            have hkey : (Array.map (fun c => t.at c i) (Array.filterMap t.idx vs)).toList = genKey t vs i := rfl
            rw [hkey]
            by_cases hkp : kp[i]! = true
            · simp only [hkp, Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and]
              cases hg : m.get? (genKey t vs i) with
              | some r =>
                have hr : r = keepOf dec t i (.general e vs) := by rw [hm _ r hg, hkeep]; rfl
                refine ⟨m, hm, ?_⟩
                simp only [pure_bind]
                rw [hr]
                cases keepOf dec t i (FKind.general e vs) <;> rfl
              | none =>
                have hl : (vs.filterMap t.idx).toList = vs.toList.map (fun w => (t.idx w).getD 0) := by
                  rw [Array.toList_filterMap]; exact filterMap_eq_map _ 0 _ hall'
                have hcol : ∀ k (hk : k < vs.size), (Array.filterMap t.idx vs)[k]! = (t.idx vs[k]).getD 0 := by
                  intro k hk
                  rw [getElem!_pos _ k (by rw [hsz]; exact hk), ← Array.getElem_toList]
                  simp only [hl, List.getElem_map, Array.getElem_toList]
                have hmu : ∀ (body : Nat → Binding → ExceptT String Id (ForInStep Binding)),
                    (∀ k acc, k < vs.size → body k acc = (do
                      let x ← st.termOf (t.at (Array.filterMap t.idx vs)[k]! i)
                      pure (ForInStep.yield (acc ++ [(vs[k]!, x)])))) →
                    forIn (List.range' 0 vs.size) [] body = pure (genMu dec vs (genKey t vs i)) := by
                  intro body hb
                  rw [listLoop' (fun k => some (vs[k]!, dec (t.at (Array.filterMap t.idx vs)[k]! i))) rfl
                    (fun k acc hk => by
                      rw [hb k acc hk]
                      obtain ⟨c, hc, hne⟩ := hkw' vs[k] (Array.getElem_mem_toList hk)
                      rw [hcol k hk, hc, Option.getD_some,
                        hterm i hi _ (row_mem t ht i vs[k] c hc (hne i hi))]
                      rfl)]
                  congr 1
                  unfold genMu
                  rw [show (fun k => some (vs[k]!, dec (t.at (Array.filterMap t.idx vs)[k]! i))) =
                    (some ∘ fun k => (vs[k]!, dec (t.at (Array.filterMap t.idx vs)[k]! i))) from rfl,
                    List.filterMap_eq_map]
                  apply List.map_congr_left
                  intro k hk
                  rw [List.mem_range] at hk
                  rw [(genKey_get t vs i hall' k hk).1, hcol k hk]
                rw [hmu _ (fun k acc hk => rfl)]
                refine ⟨m.insert (genKey t vs i) (refFilter e (genMu dec vs (genKey t vs i))), ?_, ?_⟩
                · intro ids r' h'
                  rw [Std.HashMap.get?_insert] at h'
                  split at h'
                  · next he =>
                    cases h'
                    rw [beq_iff_eq] at he
                    subst he
                    rfl
                  · exact hm ids r' h'
                · simp only [pure_bind]
                  rw [← hkeep]
                  cases keepOf dec t i (FKind.general e vs) <;> rfl
            · refine ⟨m, hm, ?_⟩
              have hkp' : kp[i]! = false := by simpa using hkp
              simp only [hkp', Bool.not_false, if_true, Bool.false_and, Bool.false_eq_true, if_false]) hI.1 hm0
        refine ⟨_, by rw [h1]; rfl, keepInv_step dec t fs fi ms1 _ kp1 kp' hI h2 (fun i hi => by rw [h3 i hi, hk]) ?_⟩
        intro j
        rw [set!_get']
        split
        · next hj =>
          obtain ⟨rfl, _⟩ := hj
          rw [hk]
          split
          · intro ids r h; simp at h
          · exact h4
        · exact hI.2.2 j
      | residual env e vs =>
        dsimp only
        have hm0 : MemoSound (memoVal dec (.residual env e vs)) ms1[fi]! := by
          have := hI.2.2 fi; rw [hk] at this; exact this
        generalize hG : forIn (m := ExceptT String Id) (List.range' 0 t.rows) (kp1, ms1[fi]!) _ = G
        obtain ⟨kp', m', h1, h2, h3, h4⟩ := maskLoopS' (MemoSound (memoVal dec (.residual env e vs)))
          (fun i => keepOf dec t i (.residual env e vs)) hG (by
            intro i kp m hi hm
            dsimp only
            have hkeep : keepOf dec t i (.residual env e vs) = residualHolds env e (resMu dec vs (resKey t vs i)) :=
              rfl
            generalize hK : (Array.map _ (Array.map t.idx vs)).toList = K
            have hKr : K = resKey t vs i := by rw [← hK]; rfl
            subst hKr
            by_cases hkp : kp[i]! = true
            · simp only [hkp, Bool.not_true, Bool.false_eq_true, if_false, Bool.true_and]
              cases hg : m.get? (resKey t vs i) with
              | some r =>
                have hr : r = keepOf dec t i (.residual env e vs) := by rw [hm _ r hg, hkeep]; rfl
                refine ⟨m, hm, ?_⟩
                simp only [pure_bind]
                rw [hr]
                cases keepOf dec t i (FKind.residual env e vs) <;> rfl
              | none =>
                have hmu : ∀ (body : Nat → Binding → ExceptT String Id (ForInStep Binding)),
                    (∀ k acc, k < vs.size → body k acc = (match (Array.map t.idx vs)[k]! with
                      | some c =>
                        if (t.at c i != L4Factoidal.Storage.Sbm11.OptJoin.unbound) = true then do
                          let x ← st.termOf (t.at c i)
                          pure (ForInStep.yield (acc ++ [(vs[k]!, x)]))
                        else pure (ForInStep.yield acc)
                      | none => pure (ForInStep.yield acc))) →
                    forIn (List.range' 0 vs.size) [] body = pure (resMu dec vs (resKey t vs i)) := by
                  intro body hb
                  rw [listLoop' (fun k => match (Array.map t.idx vs)[k]! with
                      | some c => if t.at c i != unbound then some (vs[k]!, dec (t.at c i)) else none
                      | none => none) rfl
                    (fun k acc hk => by
                      rw [hb k acc hk]
                      cases hc : (Array.map t.idx vs)[k]! with
                      | none => rfl
                      | some c =>
                        dsimp only
                        by_cases hne : (t.at c i != unbound) = true
                        · have hidx : t.idx vs[k] = some c := by
                            rw [getElem!_pos _ k (by simpa using hk), Array.getElem_map] at hc; exact hc
                          rw [if_pos hne, if_pos hne,
                            hterm i hi _ (row_mem t ht i vs[k] c hidx (by simpa using hne))]
                          rfl
                        · rw [if_neg hne, if_neg hne])]
                  congr 1
                  unfold resMu
                  apply L4Factoidal.Storage.Sbm11.OptJoin.filterMap_congr'
                  intro k hk
                  rw [List.mem_range] at hk
                  have hkey' : (resKey t vs i)[k]! = (match t.idx vs[k] with
                      | some c => t.at c i
                      | none => unbound) := by
                    unfold resKey
                    rw [getElem!_toList_map _ _ k (by simpa using hk), Array.getElem_map]
                  rw [hkey', getElem!_pos _ k (by simpa using hk), Array.getElem_map]
                  cases t.idx vs[k] with
                  | none => simp
                  | some c => rfl
                generalize hB : forIn (m := ExceptT String Id) (List.range' 0 vs.size) [] _ = B
                obtain rfl : B = pure (resMu dec vs (resKey t vs i)) := by
                  rw [← hB]; exact hmu _ (fun k acc hk => rfl)
                refine ⟨m.insert (resKey t vs i) (residualHolds env e (resMu dec vs (resKey t vs i))), ?_, ?_⟩
                · intro ids r' h'
                  rw [Std.HashMap.get?_insert] at h'
                  split at h'
                  · next he =>
                    cases h'
                    rw [beq_iff_eq] at he
                    subst he
                    rfl
                  · exact hm ids r' h'
                · simp only [pure_bind]
                  rw [← hkeep]
                  cases keepOf dec t i (FKind.residual env e vs) <;> rfl
            · refine ⟨m, hm, ?_⟩
              have hkp' : kp[i]! = false := by simpa using hkp
              simp only [hkp', Bool.not_false, if_true, Bool.false_and, Bool.false_eq_true, if_false]) hI.1 hm0
        refine ⟨_, by rw [h1]; rfl, keepInv_step dec t fs fi ms1 _ kp1 kp' hI h2 (fun i hi => by rw [h3 i hi, hk]) ?_⟩
        intro j
        rw [set!_get']
        split
        · next hj =>
          obtain ⟨rfl, _⟩ := hj
          rw [hk]
          split
          · intro ids r h; simp at h
          · exact h4
        · exact hI.2.2 j)
  · refine ⟨kp, ms', ?_, hP.1, fun i hi => by rw [hP.2.1 i hi, all_range_get]⟩
    rw [h]; rfl
  · exact hQ.elim

end keep

/-! ## One conjunct as the FILTER of the id path classifies it -/

section kinds
open L4Factoidal.Qlvr (Table)
open L4Factoidal.Storage.Sbm11.OptJoin (decRow RowIds unbound)
open L4Factoidal.Storage.Sbm11.IdLeaf (CidOk)

/-- How `IdGroup.filterM` evaluates an EXISTS-free conjunct `cj` over `t`:
    the reference on the decoded terms (`residualKind`), or, for a
    `backendLocal` conjunct whose variables are bound in every row, what
    `compileFilter` compiles it to. -/
def KindOf (env : EvalEnv) (cid : Term → Option UInt64) (t : Table) (cj : Expr) (k : FKind) : Prop :=
  k = residualKind env cj ∨
    (cj.backendLocal = true ∧ (∀ w ∈ ((residualVars cj).getD #[]).toList, IdGroup.colBound t w = true) ∧ KOk cid cj k)

/-- **L5d: a FILTER conjunct on ids.** For a conjunct as `filterM`
    classifies it (`KindOf`), the test of `applyFilters` in every row is the
    reference FILTER of the conjunct on the decoded row
    (`ebvOrFalse (Expr.evalIn env ...)`), and the kind is one `filterKeep_spec`
    covers. Hypotheses: on the dictionary (`CidOk` on `ok`, `hcidN`) and on
    the decoding (`hdec`), and the ids of the rows in `ok`. -/
theorem kind_sem (dec : UInt64 → Term) (ok : UInt64 → Prop) (cid : Term → Option UInt64) (VE : Prop)
    (hcid : ∀ c, ((cid c).isSome = true ∨ VE) → CidOk dec ok c (cid c))
    (hcidN : ∀ t x, cid t = some x → dec x = normalizeTerm t)
    (hdec : ∀ x y, ok x → ok y → (dec x).eqb (dec y) = (x == y))
    (t : Table) (ht : t.WF) (hrows : ∀ i, i < t.rows → RowIds ok (t.idRow i))
    (env : EvalEnv) (cj : Expr) (hcj : CjOk cj) (k : FKind) (hk : KindOf env cid t cj k)
    (hve : ∀ v, k = .idEq v none → VE) :
    KWf t k ∧ ∀ i, i < t.rows → keepOf dec t i k = ebvOrFalse (Expr.evalIn env (decRow dec (t.idRow i)) cj) := by
  obtain ⟨vs, hvs⟩ : ∃ vs, residualVars cj = some vs := Option.isSome_iff_exists.mp hcj.rv
  rcases hk with rfl | ⟨hbl, hcb, hk⟩
  · refine ⟨trivial, fun i _ => ?_⟩
    simp only [residualKind, hvs, Option.getD_some]
    exact keep_residual dec t ht i env cj hcj vs hvs
  · rw [hvs, Option.getD_some] at hcb
    have hb : ∀ w ∈ vs.toList, ∃ c, t.idx w = some c ∧ ∀ i, i < t.rows → t.at c i ≠ unbound :=
      fun w hw => colBound_spec t w (hcb w hw)
    refine ⟨?_, fun i hi => keep_compiled dec ok cid VE hcid hcidN hdec t ht i (hrows i hi) env cj k hk hve hcj hbl vs hvs
      (fun w hw => by obtain ⟨c, hc, hne⟩ := hb w hw; exact ⟨c, hc, hne i hi⟩)⟩
    rcases hk with ⟨_, _, _, _, _, rfl⟩ | ⟨_, _, _, rfl⟩ | ⟨_, _, _, _, _, rfl⟩ | ⟨vs', hev, rfl⟩
    · trivial
    · trivial
    · trivial
    · intro w hw
      have hr := exprVars_sound cj vs' hev w hw
      rcases residualVars_spec cj vs hvs w hr with h | h
      · exact hb w h
      · exact absurd h (hcj.nofx w hr)

end kinds

end L4Factoidal.Storage.Sbm11.FilterIdTheorems

#print axioms L4Factoidal.Storage.Sbm11.FilterIdTheorems.vc_const
#print axioms L4Factoidal.Storage.Sbm11.FilterIdTheorems.eq_ids
#print axioms L4Factoidal.Storage.Sbm11.FilterIdTheorems.same_ids
#print axioms L4Factoidal.Storage.Sbm11.FilterIdTheorems.var_ids
#print axioms L4Factoidal.Storage.Sbm11.FilterIdTheorems.compile_spec
#print axioms L4Factoidal.Storage.Sbm11.FilterIdTheorems.keep_compiled
#print axioms L4Factoidal.Storage.Sbm11.FilterIdTheorems.filterKeep_spec
#print axioms L4Factoidal.Storage.Sbm11.FilterIdTheorems.kind_sem
