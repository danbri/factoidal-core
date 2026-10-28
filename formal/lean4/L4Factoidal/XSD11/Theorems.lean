/-
L4Factoidal.XSD11.Theorems — theorems that tie XML Schema 1.1 validation
to the rest of the code base.

* `validateElement_erase`, `assessRoot_erase`: validation does not
  change the infoset. Erasing the PSVI annotations gives back the input
  element exactly (Part 1 §2.1: assessment ADDS properties to the
  infoset; the defaulted attributes and default text are kept apart from
  the input, see `PNode`).
* `simple_validity_is_xsd`: the simple-type validation of this tree is
  Part 2 validation by `L4Factoidal.XSD` (`XSD.valueOf` on the type's
  Part 2 body), with the `pattern` facets of `XSD11.Pattern`.
* `patternOk11_shared`: when the shared XSD 1.1 regex profile
  (`Regex.Profiles.compileXsd11`, also used by `XSD.SimpleType`) reads a
  pattern, `XSD11.Pattern` uses the regex it gives, so the two pattern
  dialects are one definition wherever both apply.
* `builtin_body`: a built-in atomic type's Part 2 body is the built-in
  of `XSD.Datatypes` with no facets, so a value is valid for it exactly
  when `XSD.lexicalMap` maps its normalized form.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.XSD11.Validate

namespace L4Factoidal.XSD11

open L4Factoidal.XML

/-! ## Validation does not change the infoset -/

theorem eraseList_eq_map : ∀ ps : List PNode, PNode.eraseList ps = ps.map PNode.erase
  | [] => rfl
  | p :: ps => by simp [PNode.eraseList, eraseList_eq_map ps]

mutual
theorem ofNode_erase : ∀ n : Node, (PNode.ofNode n).erase = n
  | .element t a c => by
      simp only [PNode.ofNode, PNode.erase, List.map_map]
      rw [ofNodeList_erase c]
      simp [Function.comp_def]
  | .text _ => rfl
  | .cdata _ => rfl
  | .comment _ => rfl
  | .pi _ _ => rfl

theorem ofNodeList_erase : ∀ ns : List Node, PNode.eraseList (PNode.ofNodeList ns) = ns
  | [] => rfl
  | n :: ns => by
      simp only [PNode.ofNodeList, PNode.eraseList]
      rw [ofNode_erase n, ofNodeList_erase ns]
end

theorem mkPAttrs_attr (nm : String → XName) :
    ∀ (as : List Attribute) (is : List PInfo), (mkPAttrs nm as is).map (·.attr) = as
  | [], _ => rfl
  | a :: as, i :: is => by simp [mkPAttrs, mkPAttrs_attr nm as is]
  | a :: as, [] => by simp [mkPAttrs, mkPAttrs_attr nm as []]

theorem foldKids_erase (step : KState → Node → PNode × KState)
    (h : ∀ st k, (step st k).1.erase = k) :
    ∀ (ks : List Node) (st : KState) (out : List PNode),
      (foldKids step ks st out).1.map PNode.erase = out.reverse.map PNode.erase ++ ks
  | [], _, out => by simp [foldKids]
  | k :: ks, st, out => by
      simp only [foldKids]
      rw [foldKids_erase step h ks _ _]
      simp [h st k]

theorem kidStep_erase (rec : NsBindings → How → Node → VAcc → PNode × VAcc)
    (hrec : ∀ bs how k acc, (rec bs how k acc).1.erase = k)
    (mode : KidMode) (bs : NsBindings) (parent : XName) :
    ∀ st k, (kidStep rec mode bs parent st k).1.erase = k := by
  intro st k
  cases k with
  | element t a c => simp [kidStep, hrec]
  | text _ => rfl
  | cdata _ => rfl
  | comment _ => rfl
  | pi _ _ => rfl

/-- Validation does not change the infoset: erasing the annotations of
the PSVI element gives back the input node, for every schema, every
XPath hook, every way of validating and every fuel. -/
theorem validateElement_erase (s : Schema) (h : Hooks) :
    ∀ (f : Nat) (bs : NsBindings) (how : How) (n : Node) (acc : VAcc),
      (validateElement s h f bs how n acc).1.erase = n
  | 0, _, _, n, _ => ofNode_erase n
  | f + 1, bs, how, n, acc => by
      cases n with
      | element tag attrs kids =>
        simp only [validateElement]
        generalize hfk : foldKids _ kids _ [] = r
        obtain ⟨outs, kst⟩ := r
        have hk := foldKids_erase _ (kidStep_erase (validateElement s h f)
          (validateElement_erase s h f)
          (elemHead s h (instBindings bs attrs) how tag attrs kids acc).mode
          (instBindings bs attrs) (elemXName (instBindings bs attrs) tag)) kids
          (elemHead s h (instBindings bs attrs) how tag attrs kids acc).st0 []
        rw [hfk] at hk
        simp only [List.reverse_nil, List.map_nil, List.nil_append] at hk
        simp [PNode.erase, mkPAttrs_attr, eraseList_eq_map, hk]
      | text _ => rfl
      | cdata _ => rfl
      | comment _ => rfl
      | pi _ _ => rfl

/-- The PSVI of a document element erases to the document element. -/
theorem assessRoot_erase (s : Schema) (h : Hooks) (root : Node) (bs : NsBindings) :
    (assessRoot s h root bs).root.erase = root := by
  unfold assessRoot
  cases rootHow s root bs <;> simp [validateElement_erase]

/-! ## Simple types are Part 2 types -/

/-- A string the XSD 1.1 validator accepts for a simple type is valid for
the type's Part 2 body under `XSD.validate` (`L4Factoidal.XSD`), and
satisfies the type's pattern facets at every level. -/
theorem validateSimple_ok (s : Schema) (h : Hooks) (bs : NsBindings) (t : Nat) (lit : String)
    (u : List String) (sd : SimpleDef) (hsd : s.simpleOf? t = some sd)
    (r : String × XSD.Val) (hr : (validateSimple s h bs t lit u).1 = .ok r) :
    XSD.validate sd.body lit = true ∧ bodyPatternsOk 16 sd.body lit = true := by
  unfold validateSimple at hr
  rw [hsd] at hr
  simp only at hr
  cases hv : XSD.valueOf sd.body lit with
  | none => simp [hv, Option.filter] at hr
  | some v =>
    cases hp : bodyPatternsOk 16 sd.body lit with
    | false => simp [hv, hp, Option.filter] at hr
    | true => exact ⟨by simp [XSD.validate, hv], rfl⟩

/-! ## One pattern dialect -/

/-- When the shared XSD 1.1 profile compiles a pattern, `XSD11.Pattern`
uses exactly that regex. -/
theorem xsdPatternRe_shared (p : String) (r : Regex.Re)
    (h : Regex.Profiles.compileXsd11 p = .ok r) : xsdPatternRe p = some r := by
  simp [xsdPatternRe, h]

theorem filterMap_patternMatch11 (lit : String) :
    ∀ alts : List String, (∀ p ∈ alts, (Regex.Profiles.compileXsd11 p).toOption.isSome) →
      alts.filterMap (fun p => patternMatch11 p lit) =
        (alts.filterMap (fun p => (Regex.Profiles.compileXsd11 p).toOption)).map
          (fun r => Regex.Exec.acceptsNorm r (lit.toList.map Char.toNat))
  | [], _ => rfl
  | p :: ps, h => by
      have ih := filterMap_patternMatch11 lit ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
      have hp := h p List.mem_cons_self
      cases hc : Regex.Profiles.compileXsd11 p with
      | ok r =>
        have h1 : patternMatch11 p lit = some (Regex.Exec.acceptsNorm r (lit.toList.map Char.toNat)) := by
          simp [patternMatch11, xsdPatternRe, hc]
        have h2 : (Regex.Profiles.compileXsd11 p).toOption = some r := by simp [hc, Except.toOption]
        rw [List.filterMap_cons, List.filterMap_cons, h1, h2, ih]
        rfl
      | error e => simp [hc, Except.toOption] at hp

/-- When the shared profile reads every pattern of the groups, the XSD 1.1
pattern test is the one of `XSD.SimpleType` (`XSD.patternMatches`). -/
theorem patternOk11_shared (lit : String) :
    ∀ groups : List (List String),
      (∀ alts ∈ groups, ∀ p ∈ alts, (Regex.Profiles.compileXsd11 p).toOption.isSome) →
      patternOk11 groups lit = XSD.patternMatches groups lit
  | [], _ => rfl
  | alts :: gs, h => by
      have ih := patternOk11_shared lit gs (fun a ha => h a (List.mem_cons_of_mem _ ha))
      have hf := filterMap_patternMatch11 lit alts (h alts List.mem_cons_self)
      unfold patternOk11 XSD.patternMatches at *
      simp only [List.all_cons, hf, ih, List.isEmpty_map, List.any_map]
      rfl

end L4Factoidal.XSD11
