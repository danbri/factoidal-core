/-
L4Factoidal.XPath4.XIncludeTheorems — the `xinclude` option of `fn:doc`
and `fn:parse-xml` changes nothing for a document that has no element in
the XInclude namespace.

Proved here (no `sorry`, no new axioms):

* `expand_noXi` — `XInclude.expand` gives back the node itself when no
  element of the subtree is in the namespace `XInclude.xiNs` (with the
  in-scope namespace bindings of each element, `XInclude.scopeOf`).

Theorems on `XInclude.expandX`, the processor with XPointer, named for
XInclude 1.1 (W3C Working Group Note 2013) and the XPointer
Recommendations of 2003 (`xinc11_`, `xinc11_xptr2003_`):

* `xinc11_expandX_noXi` — the same for `expandX`: a document with no
  XInclude element is its own result.
* `xinc11_xptr2003_noSubresource_resource`,
  `xinc11_xptr2003_syntaxError_resource` — an XPointer 2003 pointer that
  identifies no subresource, or that is not a `Pointer`, is a resource
  error of XInclude (so `xi:fallback` applies).
* `xinc11_xptr2003_attr_fatal` — a pointer whose result has an attribute
  node is a fatal error.
* `xinc11_text_xpointer_fatal`, `xinc11_fragment_fatal` — `parse="text"`
  with `xpointer`, and an `href` with a fragment identifier, are errors
  found before any resource is read.
-/
import L4Factoidal.XPath4.XInclude

namespace L4Factoidal.XPath4.XIncludeTheorems

open L4Factoidal.XML
open L4Factoidal.XPath4.XInclude

/-- No element of the subtree is in the XInclude namespace (within the
    depth `f`). -/
def noXi : Nat → List (String × String) → Node → Bool
  | 0, _, _ => false
  | f + 1, sc, .element tag attrs kids =>
    let sc := scopeOf sc attrs
    (nameOf sc tag).1 != xiNs && kids.attach.all (fun ⟨k, _⟩ => noXi f sc k)
  | _ + 1, _, _ => true

theorem mapM_ok_singleton {α : Type} (g : α → Except XiErr (List α)) (xs : List α)
    (h : ∀ x ∈ xs, g x = .ok [x]) :
    (xs.mapM g).map List.flatten = .ok xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    have hx := h x (by simp)
    have hr := ih (fun y hy => h y (by simp [hy]))
    simp only [List.mapM_cons, hx]
    cases hm : rest.mapM g with
    | error e => rw [hm] at hr; simp [Except.map] at hr
    | ok ys =>
      rw [hm] at hr
      simp [Except.map] at hr
      simp [bind, Except.bind, pure, Except.pure, Except.map, hr]

theorem expand_noXi (fetch : String → Option String) (parseRoot : String → Except String Node)
    (f : Nat) (chain : List String) (base : String) (sc : List (String × String)) (n : Node)
    (h : noXi f sc n = true) :
    expand fetch parseRoot f chain base sc n = .ok [n] := by
  induction f generalizing sc n with
  | zero => simp [noXi] at h
  | succ f ih =>
    cases n with
    | element tag attrs kids =>
      simp only [noXi, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at h
      obtain ⟨hns, hk⟩ := h
      have hkids : ∀ k ∈ kids, expand fetch parseRoot f chain base (scopeOf sc attrs) k = .ok [k] := by
        intro k hk'
        exact ih (scopeOf sc attrs) k (hk ⟨k, hk'⟩ (by simp))
      have hm := mapM_ok_singleton (expand fetch parseRoot f chain base (scopeOf sc attrs)) kids hkids
      simp only [expand]
      have h1 : ((nameOf (scopeOf sc attrs) tag).1 == xiNs) = false := by simpa using hns
      simp only [h1, Bool.false_and]
      cases hmm : kids.mapM (expand fetch parseRoot f chain base (scopeOf sc attrs)) with
      | error e => rw [hmm] at hm; simp [Except.map] at hm
      | ok ys =>
        rw [hmm] at hm
        simp [Except.map] at hm
        simp [bind, Except.bind, pure, Except.pure, hm]
    | _ => simp [expand]

theorem xinc11_expandX_noXi (cfg : Cfg) (here : Document)
    (f : Nat) (chain : List String) (base : String) (sc : List (String × String))
    (anc : List Node) (n : Node) (h : noXi f sc n = true) :
    expandX cfg here f chain base sc anc n = .ok [n] := by
  induction f generalizing sc anc n with
  | zero => simp [noXi] at h
  | succ f ih =>
    cases n with
    | element tag attrs kids =>
      simp only [noXi, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true] at h
      obtain ⟨hns, hk⟩ := h
      have hkids : ∀ k ∈ kids, expandX cfg here f chain base (scopeOf sc attrs)
          (.element tag attrs kids :: anc) k = .ok [k] := by
        intro k hk'
        exact ih (scopeOf sc attrs) _ k (hk ⟨k, hk'⟩ (by simp))
      have hm := mapM_ok_singleton (expandX cfg here f chain base (scopeOf sc attrs)
        (.element tag attrs kids :: anc)) kids hkids
      simp only [expandX]
      have h1 : ((nameOf (scopeOf sc attrs) tag).1 == xiNs) = false := by simpa using hns
      simp only [h1, Bool.false_and]
      cases hmm : kids.mapM (expandX cfg here f chain base (scopeOf sc attrs)
          (.element tag attrs kids :: anc)) with
      | error e => rw [hmm] at hm; simp [Except.map] at hm
      | ok ys =>
        rw [hmm] at hm
        simp [Except.map] at hm
        simp [bind, Except.bind, pure, Except.pure, hm]
    | _ => simp [expandX]

theorem xinc11_xptr2003_noSubresource_resource (cfg : Cfg) (ev : Document → String → XPointer.Outcome)
    (d : Document) (p : String) (hc : cfg.pointer = some ev) (he : ev d p = .noSubresource) :
    ∃ m, select cfg d p = .error (.resource m) := by
  simp [select, hc, he]

theorem xinc11_xptr2003_syntaxError_resource (cfg : Cfg) (ev : Document → String → XPointer.Outcome)
    (d : Document) (p msg : String) (hc : cfg.pointer = some ev) (he : ev d p = .syntaxError msg) :
    ∃ m, select cfg d p = .error (.resource m) := by
  simp [select, hc, he]

theorem xinc11_xptr2003_attr_fatal (cfg : Cfg) (ev : Document → String → XPointer.Outcome)
    (d : Document) (p : String) (a : Attribute) (hs : List XPointer.Hit)
    (hc : cfg.pointer = some ev) (he : ev d p = .hits (.attr a :: hs)) :
    ∃ m, select cfg d p = .error (.fatal m) := by
  simp [select, hc, he, List.mapM_cons, bind, Except.bind]

theorem xinc11_text_xpointer_fatal (sc : List (String × String)) (attrs : List Attribute)
    (kids : List Node) (hp : attrOf attrs "parse" = some "text")
    (hx : (attrOf attrs "xpointer").isSome = true) :
    (includeError sc attrs kids).isSome = true := by
  simp only [includeError]
  repeat' split
  all_goals simp_all

theorem xinc11_fragment_fatal (sc : List (String × String)) (attrs : List Attribute)
    (kids : List Node) (hh : ((attrOf attrs "href").getD "").contains '#' = true) :
    (includeError sc attrs kids).isSome = true := by
  simp only [includeError]
  repeat' split
  all_goals simp_all

end L4Factoidal.XPath4.XIncludeTheorems
