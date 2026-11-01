/-
L4Factoidal.XPath4.XIncludeTheorems — the `xinclude` option of `fn:doc`
and `fn:parse-xml` changes nothing for a document that has no element in
the XInclude namespace.

Proved here (no `sorry`, no new axioms):

* `expand_noXi` — `XInclude.expand` gives back the node itself when no
  element of the subtree is in the namespace `XInclude.xiNs` (with the
  in-scope namespace bindings of each element, `XInclude.scopeOf`).
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

end L4Factoidal.XPath4.XIncludeTheorems
