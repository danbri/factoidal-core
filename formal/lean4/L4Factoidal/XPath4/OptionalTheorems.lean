/-
L4Factoidal.XPath4.OptionalTheorems — bridge theorems for the optional
features of XPath 4.0 that the qt4tests runner (`Harness/Qt4Run.lean`)
turns on: the namespace axis and the XML 1.1 character repertoire.

Proved here (no `sorry`, no new axioms):

* `nsNodesOf_sound` — every namespace node of an element (XDM 4.0 §6.4,
  `XPath4.nsNodesOf`, the nodes of the namespace axis) is an in-scope
  binding of the `XML.Namespaces` scope the element's record was made
  from (`XML.lookupPrefix`), or the fixed `xml` binding.
* `nsNodesOf_complete` — every in-scope binding of that scope to a
  namespace URI is a namespace node (for a scope of at most 4094
  entries, the slot bound of `XPath4.nsSlot`).
* `firstBinds_mem` — the first binding of a prefix is the one in force
  (the shadowing rule of `XML.lookupPrefix`, Namespaces in XML 1.0 §6.1).
* `isXmlCp_eq_xml11` — the characters that XPath 4.0 strings may hold
  (`XPath4.isXmlCp`) are XML 1.1 `[2] Char` of `XML.isXml11CharCode`,
  as XDM 4.0 §4.1.6 requires ("all characters allowed by XML 1.1 must
  be accepted").
* `isXmlCp_of_xml10`, `xml11_agrees_xml10` — on a character that XML 1.0
  `[2] Char` admits, the XML 1.1 and XML 1.0 predicates of `XML.Document`
  agree, so the XML 1.1 repertoire changes nothing for a text written
  only in XML 1.0 characters.

Not proved here (https://github.com/danbri/factoidal/issues/1154 stays
the record): that `XPath4.buildNode` makes `inscope` equal to
`convScope` of the scope `XML.applyDeclarations` computes for the same
element. The `#guard`s at the end test it on sample documents.
-/
import L4Factoidal.XPath4.Doc
import L4Factoidal.XPath4.Lib
import L4Factoidal.XML.Namespaces

namespace L4Factoidal.XPath4.OptionalTheorems

open L4Factoidal.XPath4
open L4Factoidal.XML

/-! ## Namespace nodes and `XML.Namespaces` -/

/-- The XDM form of an `XML.Namespaces` scope: an undeclaration
    `(p, none)` is the binding of `p` to the zero-length URI. -/
def convScope (xs : NsScope) : List (String × String) :=
  xs.map (fun b => (b.1, b.2.getD ""))

/-- The step of `nsNodesOf` that keeps the first binding of each prefix. -/
def firstStep (acc : List (String × String)) (b : String × String) : List (String × String) :=
  if acc.any (·.1 == b.1) then acc else acc ++ [b]

/-- The first binding of each prefix, in scope order. -/
def firstBinds (sc : List (String × String)) : List (String × String) :=
  sc.foldl firstStep []

theorem nsNodesOf_eq (r : NRec) (h : r.kind = .element) :
    nsNodesOf r =
      (let sc := ((firstBinds r.inscope).filter (fun (_, u) => u != "")).take (nsSlot - 2)
       if sc.any (·.1 == "xml") then sc else sc ++ [("xml", nsXML)]) := by
  unfold nsNodesOf firstBinds
  simp [h]
  rfl

theorem firstStep_foldl_mem (sc acc : List (String × String)) (p u : String) :
    (p, u) ∈ sc.foldl firstStep acc ↔
      ((p, u) ∈ acc ∨ (acc.any (·.1 == p) = false ∧ sc.find? (·.1 == p) = some (p, u))) := by
  induction sc generalizing acc with
  | nil => simp
  | cons b rest ih =>
    obtain ⟨q, w⟩ := b
    simp only [List.foldl_cons]
    rw [ih]
    by_cases ha : acc.any (·.1 == q) = true
    · have hs : firstStep acc (q, w) = acc := by simp [firstStep, ha]
      rw [hs]
      by_cases hq : q = p
      · subst hq; simp [ha]
      · have : (q == p) = false := by simpa using hq
        simp [this]
    · have ha' : acc.any (·.1 == q) = false := Bool.eq_false_iff.2 ha
      have hs : firstStep acc (q, w) = acc ++ [(q, w)] := by simp [firstStep, ha']
      rw [hs]
      by_cases hq : q = p
      · subst hq
        simp only [List.any_append, List.any_cons, List.any_nil, beq_self_eq_true, Bool.or_true,
          Bool.true_or, ha', List.mem_append, List.mem_singleton, List.find?_cons]
        constructor
        · rintro ((h | h) | ⟨h, _⟩)
          · exact Or.inl h
          · cases h; exact Or.inr ⟨trivial, rfl⟩
          · exact absurd h (by simp)
        · rintro (h | ⟨_, h⟩)
          · exact Or.inl (Or.inl h)
          · simp at h
            cases h
            exact Or.inl (Or.inr rfl)
      · have hqp : (q == p) = false := by simpa using hq
        have hpq : ((q, w) : String × String) ≠ (p, u) := by
          intro h; cases h; exact hq rfl
        simp only [List.any_append, List.any_cons, List.any_nil, hqp, Bool.or_false,
          List.mem_append, List.mem_singleton, List.find?_cons]
        have hpq' : ((p, u) : String × String) ≠ (q, w) := fun h => hpq h.symm
        simp [hpq']

/-- The first binding of a prefix is the one in force. -/
theorem firstBinds_mem (sc : List (String × String)) (p u : String) :
    (p, u) ∈ firstBinds sc ↔ sc.find? (·.1 == p) = some (p, u) := by
  unfold firstBinds
  rw [firstStep_foldl_mem]
  simp

theorem find_convScope (xs : NsScope) (p : String) :
    (convScope xs).find? (·.1 == p) = (xs.find? (·.1 == p)).map (fun b => (b.1, b.2.getD "")) := by
  unfold convScope
  rw [List.find?_map]
  rfl

theorem find_key {xs : NsScope} {p : String} {b : String × Option String}
    (h : xs.find? (·.1 == p) = some b) : b.1 = p := by
  have := List.find?_some h
  simpa using this

/-- Every namespace node is an in-scope binding of the scope, or the
    `xml` binding. -/
theorem nsNodesOf_sound (r : NRec) (xs : NsScope) (hk : r.kind = .element)
    (hs : r.inscope = convScope xs) (p u : String) (h : (p, u) ∈ nsNodesOf r) :
    (lookupPrefix xs p = some u ∧ u ≠ "") ∨ (p = "xml" ∧ u = nsXML) := by
  rw [nsNodesOf_eq r hk] at h
  simp only at h
  have core : (p, u) ∈ (((firstBinds r.inscope).filter (fun (_, u) => u != "")).take (nsSlot - 2)) →
      lookupPrefix xs p = some u ∧ u ≠ "" := by
    intro hm
    have hm := List.mem_of_mem_take hm
    rw [List.mem_filter] at hm
    obtain ⟨hm, hne⟩ := hm
    rw [firstBinds_mem, hs, find_convScope] at hm
    simp only [Option.map_eq_some_iff] at hm
    obtain ⟨b, hb, hbe⟩ := hm
    have hk := find_key hb
    obtain ⟨bp, bu⟩ := b
    simp at hbe hk
    subst hk
    refine ⟨?_, by simpa using hne⟩
    unfold lookupPrefix
    rw [hb]
    cases bu with
    | none => simp at hbe; subst hbe; simp at hne
    | some v => simp at hbe; simp [hbe]
  split at h
  · exact Or.inl (core h)
  · rw [List.mem_append] at h
    rcases h with h | h
    · exact Or.inl (core h)
    · simp at h; exact Or.inr h

theorem firstStep_foldl_length (sc acc : List (String × String)) :
    (sc.foldl firstStep acc).length ≤ acc.length + sc.length := by
  induction sc generalizing acc with
  | nil => simp
  | cons b rest ih =>
    simp only [List.foldl_cons, List.length_cons]
    have := ih (firstStep acc b)
    unfold firstStep at this ⊢
    split at this <;> simp_all <;> omega

/-- Every in-scope binding to a namespace URI is a namespace node (for a
    scope of at most `nsSlot - 2` entries). -/
theorem nsNodesOf_complete (r : NRec) (xs : NsScope) (hk : r.kind = .element)
    (hs : r.inscope = convScope xs) (hlen : xs.length ≤ nsSlot - 2)
    (p u : String) (hl : lookupPrefix xs p = some u) (hne : u ≠ "") :
    (p, u) ∈ nsNodesOf r := by
  rw [nsNodesOf_eq r hk]
  simp only
  have hmem : (p, u) ∈ ((firstBinds r.inscope).filter (fun (_, u) => u != "")).take (nsSlot - 2) := by
    rw [List.take_of_length_le]
    · rw [List.mem_filter, firstBinds_mem, hs, find_convScope]
      unfold lookupPrefix at hl
      cases hb : xs.find? (·.1 == p) with
      | none => rw [hb] at hl; simp at hl
      | some b =>
        rw [hb] at hl
        have hk := find_key hb
        obtain ⟨bp, bu⟩ := b
        simp at hl hk
        subst hk hl
        simp [hne]
    · refine Nat.le_trans (List.length_filter_le _ _) ?_
      have h2 := firstStep_foldl_length r.inscope []
      have h3 : r.inscope.length = xs.length := by rw [hs]; simp [convScope]
      unfold firstBinds
      simp at h2
      omega
  split
  · exact hmem
  · exact List.mem_append_left _ hmem

/-! ## The XML 1.1 character repertoire -/

theorem isXmlCp_eq_xml11 (n : Nat) : isXmlCp n = isXml11CharCode n := rfl

theorem isXmlCp_of_xml10 (n : Nat) (h : isXmlCharCode n = true) : isXmlCp n = true := by
  unfold isXmlCharCode at h
  unfold isXmlCp
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h ⊢
  omega

theorem xml11_agrees_xml10 (n : Nat) (h : isXmlCharCode n = true) :
    XmlVersion.v11.isCharCode n = XmlVersion.v10.isCharCode n := by
  simp only [XmlVersion.isCharCode, h]
  exact isXmlCp_of_xml10 n h

/-! ## Tests: the scope of `Doc.ofDocument` against `XML.Namespaces` -/

/-- The `XML.Namespaces` scope of the document element of `s`. -/
def rootScope (s : String) : Option NsScope :=
  match parseXML s with
  | .ok d => match d.root with
    | .element _ attrs _ => applyDeclarations "1.0" initialScope attrs
    | _ => none
  | .error _ => none

/-- The namespace nodes of the document element of `s`, as the
    namespace axis gives them. -/
def rootNsNodes (s : String) : List (String × String) :=
  match Doc.ofString s with
  | .ok d => match (d.nodes.toList.find? (fun r => r.kind == .element)) with
    | some r => nsNodesOf r
    | none => []
  | .error _ => []

/-- Every prefix bound in the `XML.Namespaces` scope of the root has a
    namespace node with that URI, and every namespace node is bound. -/
def agrees (s : String) : Bool :=
  match rootScope s with
  | some xs =>
    let ns := rootNsNodes s
    (xs.all (fun (p, _) => match lookupPrefix xs p with
      | some u => ns.contains (p, u)
      | none => !(ns.any (·.1 == p)))) &&
    ns.all (fun (p, u) => lookupPrefix xs p == some u)
  | none => false

#guard agrees "<a xmlns='urn:d' xmlns:p='urn:p' xmlns:q='urn:q'/>"
#guard agrees "<a/>"
#guard agrees "<p:a xmlns:p='urn:p'><b/></p:a>"
#guard agrees "<a xmlns:xml='http://www.w3.org/XML/1998/namespace' xmlns=''/>"

end L4Factoidal.XPath4.OptionalTheorems
