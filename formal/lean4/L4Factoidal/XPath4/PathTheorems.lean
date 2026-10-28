/-
L4Factoidal.XPath4.PathTheorems — XPath 4.0 (`L4Factoidal.XPath4`, over
the node table of `Doc.ofNodes`) and XPath 1.0 (`L4Factoidal.XPath.Full`,
over the XML tree) select corresponding nodes for the step `child::*` from
the document node. Tracking: https://github.com/danbri/factoidal/issues/1143.

Proved (no `sorry`, no new axioms):

* `child_star_agree` — for every `ns` that fits the fuel of `Doc.ofNodes`,
  the candidate list of the XPath 4.0 step `child::*` at the document node
  (`(env.axis .child root).filter (env.testMatches .child · (.name .any))`,
  the list that `eval` filters with the predicates, `XPath4/Eval.lean`
  case `.step`) and the candidate list of the XPath 1.0 step `child::*` at
  the root (`(axisItems ns .child (.doc ns 0)).filter (matchesTest ns nsctx
  .child .anyName)`, the list that `evalStep` filters with the predicates,
  `XPath/Eval.lean`) have the same length, and entry `t` of the first is a
  record of `d` that was built (`BuiltA`) from the XML node of entry `t` of
  the second, which is `ns[i]` at address `[i]`.

Not proved here:

* The steps with predicates and the full `eval`/`evalStep`: `evalStep` and
  `applyPreds` of XPath 1.0 are `partial def`s, which a proof cannot
  unfold, so the theorem is stated on the candidate lists.
* A name test `child::q`: XPath 4.0 expands the element name with
  `splitName` (`String.splitOn`) and the fold `elemScope`; XPath 1.0 with
  `splitQName` and `scopeAtPath`/`applyDeclarations`. The agreement of
  those two namespace readings needs lemmas about the legacy
  `String.splitOn`, which the core library does not have.
* `child::text()` and `child::node()`: `Doc.ofNodes` merges adjacent text
  and CDATA nodes and drops empty text (`mergeText`, XDM 4.0 §6.7.1) and
  XPath 1.0 does not, so the lists differ for those inputs.
-/
import L4Factoidal.XPath4.DocTheorems2
import L4Factoidal.XPath4.Core
import L4Factoidal.XPath.Eval

namespace L4Factoidal.XPath4

namespace DocProof

open L4Factoidal.XML

/-- Two lists of the same length whose entries are related pairwise. -/
def ListRel {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | x :: xs, y :: ys => R x y ∧ ListRel R xs ys
  | _, _ => False

theorem ListRel.length {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β}, ListRel R xs ys → xs.length = ys.length
  | [], [], _ => rfl
  | _ :: _, _ :: _, ⟨_, h⟩ => by simp [h.length]

theorem ListRel.get {α β : Type} {R : α → β → Prop} :
    ∀ {xs : List α} {ys : List β} (h : ListRel R xs ys) (t : Nat) (ht : t < xs.length),
      R (xs[t]'ht) (ys[t]'(h.length ▸ ht))
  | [], [], _, _, ht => absurd ht (Nat.not_lt_zero _)
  | _ :: _, _ :: _, ⟨h1, _⟩, 0, _ => h1
  | _ :: _, _ :: _, ⟨_, h2⟩, t + 1, ht => h2.get t (by simpa using ht)

theorem ListRel.mono {α β : Type} {R S : α → β → Prop} (hrs : ∀ x y, R x y → S x y) :
    ∀ {xs : List α} {ys : List β}, ListRel R xs ys → ListRel S xs ys
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨hrs _ _ h1, ListRel.mono hrs h2⟩

theorem ListRel.map_left {α α' β : Type} {R : α' → β → Prop} (f : α → α') :
    ∀ {xs : List α} {ys : List β}, ListRel (fun x y => R (f x) y) xs ys → ListRel R (xs.map f) ys
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨h1, ListRel.map_left f h2⟩

theorem ListRel.comp {α β γ : Type} {R : α → β → Prop} {S : γ → β → Prop} :
    ∀ {xs : List α} {ys : List β} {zs : List γ}, ListRel R xs ys → ListRel S zs ys →
      ListRel (fun x z => ∃ y, R x y ∧ S z y) xs zs
  | [], [], [], _, _ => trivial
  | _ :: _, _ :: _, _ :: _, ⟨h1, h2⟩, ⟨h3, h4⟩ => ⟨⟨_, h1, h3⟩, ListRel.comp h2 h4⟩

def isElem (n : Node) : Bool := nodeKind n == .element

/-- `mergeText` changes only text and CDATA nodes: the element nodes are
    the same, in the same order. -/
theorem mergeText_filter_elem : ∀ (l : List Node), (mergeText l).filter isElem = l.filter isElem
  | [] => rfl
  | n :: rest => by
    have ih := mergeText_filter_elem rest
    simp only [mergeText]
    split
    · split
      · rename_i b r hr
        rw [List.filter_cons_of_neg (by simp [isElem, nodeKind]),
          List.filter_cons_of_neg (by simp [isElem, nodeKind])]
        rw [hr, List.filter_cons_of_neg (by simp [isElem, nodeKind])] at ih
        exact ih
      · rw [List.filter_cons_of_neg (by simp [isElem, nodeKind])]
        split
        · exact ih
        · rw [List.filter_cons_of_neg (by simp [isElem, nodeKind])]; exact ih
    · split
      · rename_i b r hr
        rw [List.filter_cons_of_neg (by simp [isElem, nodeKind]),
          List.filter_cons_of_neg (by simp [isElem, nodeKind])]
        rw [hr, List.filter_cons_of_neg (by simp [isElem, nodeKind])] at ih
        exact ih
      · rw [List.filter_cons_of_neg (by simp [isElem, nodeKind])]
        split
        · exact ih
        · rw [List.filter_cons_of_neg (by simp [isElem, nodeKind])]; exact ih
    · by_cases he : isElem n = true
      · rw [List.filter_cons_of_pos he, List.filter_cons_of_pos he, ih]
      · rw [List.filter_cons_of_neg he, List.filter_cons_of_neg he, ih]

theorem kind_getD {a : Array NRec} {c : Nat} {k : NKind} (h : a[c]?.map NRec.kind = some k) :
    (a.getD c default).kind = k := by
  cases hc : a[c]? with
  | none => rw [hc] at h; cases h
  | some r => rw [hc] at h; cases h; rw [getD_of_get? hc]

/-- The element children of a built child list correspond to the element
    nodes of the node list. -/
theorem BuiltList.filter_elem {a : Array NRec} {sc p} : ∀ {lo cs ks hi},
    BuiltList a sc p lo cs ks hi →
    ListRel (fun c k => ∃ e, BuiltA a sc (some p) c e k)
      (cs.filter (fun c => (a.getD c default).kind == .element)) (ks.filter isElem)
  | _, _, _, _, .nil => trivial
  | _, _, _, _, .cons (k := k) h t => by
    have hk := kind_getD h.kind
    by_cases he : isElem k = true
    · rw [List.filter_cons_of_pos he, List.filter_cons_of_pos (by rw [hk]; exact he)]
      exact ⟨⟨_, h⟩, t.filter_elem⟩
    · rw [List.filter_cons_of_neg he, List.filter_cons_of_neg (by rw [hk]; exact he)]
      exact t.filter_elem

open L4Factoidal.XPath.Full in
theorem matchesTest_anyName (d : L4Factoidal.XPath.Full.Doc) (nsctx : List (String × String)) :
    matchesTest d nsctx .child .anyName = fun (it : XPath.Full.Item) => it.kind == .element := rfl

open L4Factoidal.XPath.Full in
theorem item_kind_tree (l : Loc) (n : Node) :
    ((XPath.Full.Item.tree l n).kind == .element) = isElem n := by
  cases n <;> rfl

open L4Factoidal.XPath.Full in
/-- The element children of the XPath 1.0 root, by address. -/
theorem xp1_children_elem : ∀ (l : List Node) (k : Nat),
    ListRel (fun (it : XPath.Full.Item) (n : Node) => ∃ i, it = .tree { path := [k + i], doc := 0 } n ∧ l[i]? = some n)
      (((l.zipIdx k).map (fun (x : Node × Nat) => (XPath.Full.Item.tree { path := [x.2], doc := 0 } x.1 : XPath.Full.Item))).filter
        (fun (it : XPath.Full.Item) => it.kind == .element))
      (l.filter isElem)
  | [], _ => trivial
  | x :: l, k => by
    have ih := xp1_children_elem l (k + 1)
    have ih' : ListRel (fun (it : XPath.Full.Item) (n : Node) => ∃ i, it = .tree { path := [k + i], doc := 0 } n ∧
        (x :: l)[i]? = some n)
      (((l.zipIdx (k + 1)).map (fun (x : Node × Nat) => (XPath.Full.Item.tree { path := [x.2], doc := 0 } x.1 : XPath.Full.Item))).filter
        (fun (it : XPath.Full.Item) => it.kind == .element)) (l.filter isElem) := by
      refine ih.mono (fun it n ⟨i, h1, h2⟩ => ⟨i + 1, ?_, ?_⟩)
      · rw [h1, Nat.add_assoc, Nat.add_comm 1 i]
      · simpa using h2
    simp only [List.zipIdx_cons, List.map_cons]
    by_cases he : isElem x = true
    · rw [List.filter_cons_of_pos (by rw [item_kind_tree]; exact he), List.filter_cons_of_pos he]
      exact ⟨⟨0, by simp⟩, ih'⟩
    · rw [List.filter_cons_of_neg (by rw [item_kind_tree]; exact he), List.filter_cons_of_neg he]
      exact ih'

end DocProof

open DocProof
open L4Factoidal.XML (Node)

theorem Env.testMatches_child_any (e : Env) (m : NodeRef) :
    e.testMatches .child m (.name .any) = ((e.nrec m).kind == .element) := by
  simp [Env.testMatches, Env.testMatches1, nameTestMatches]

/-- XPath 4.0 and XPath 1.0 agree on `child::*` at the document node: the
    two candidate lists (before predicates) have the same length, and
    entry `t` of the XPath 4.0 list is a node of document 0 whose record
    was built from the XML node `n = ns[i]` that entry `t` of the XPath 1.0
    list holds at address `[i]`. -/
theorem child_star_agree (ns : List Node) (uri : String) (hfit : ∀ n ∈ ns, Fits 100000 n)
    (nsctx : List (String × String)) :
    ListRel (fun (m : NodeRef) (it : XPath.Full.Item) =>
        m.doc = 0 ∧ m.rt = none ∧ ∃ i n e, it = .tree { path := [i], doc := 0 } n ∧ ns[i]? = some n ∧
          BuiltA (Doc.ofNodes ns uri).nodes [("xml", nsXML)] (some 0) m.idx e n)
      (((({ docs := #[Doc.ofNodes ns uri] } : Env).axis .child (NodeRef.mk' 0 0))).filter
        (fun m => ({ docs := #[Doc.ofNodes ns uri] } : Env).testMatches .child m (.name .any)))
      ((XPath.Full.axisItems ns .child (.doc ns 0)).filter
        (XPath.Full.matchesTest ns nsctx .child .anyName)) := by
  obtain ⟨cs, h0, hb⟩ := DocProof.ofNodes_built ns uri hfit
  have hax : ({ docs := #[Doc.ofNodes ns uri] } : Env).axis .child (NodeRef.mk' 0 0) =
      cs.toList.map (fun c => (NodeRef.mk' 0 0).at c) := by
    show ((Doc.ofNodes ns uri).get 0).children.toList.map _ = _
    simp only [Doc.get, getD_of_get? h0]
  have h1 : (XPath.Full.axisItems ns .child (.doc ns 0)) =
      (ns.zipIdx 0).map (fun (x : Node × Nat) => (XPath.Full.Item.tree { path := [x.2], doc := 0 } x.1 : XPath.Full.Item)) := by
    show List.map _ _ = _
    apply List.map_congr_left
    intro x _
    rfl
  rw [hax, h1, matchesTest_anyName, List.filter_map]
  simp only [Function.comp_def, Env.testMatches_child_any]
  have hr := (hb.filter_elem).comp (by rw [mergeText_filter_elem]; exact xp1_children_elem ns 0)
  refine ListRel.map_left _ (hr.mono (fun c it ⟨n, ⟨e, hbe⟩, ⟨i, hit, hn⟩⟩ => ⟨rfl, rfl, i, n, e, ?_, hn, hbe⟩))
  · rw [hit, Nat.zero_add]

-- The two candidate lists on a small document (one element child of the
-- document node, beside a comment), so the statement above is not about
-- empty lists only.
#guard match L4Factoidal.XML.parseXML "<!--c--><a><b/>t</a>" with
  | .ok doc =>
    let d := Doc.ofNodes doc.children
    let env : Env := { docs := #[d] }
    ((env.axis .child (NodeRef.mk' 0 0)).filter (fun m => env.testMatches .child m (.name .any))).length == 1 &&
    ((XPath.Full.axisItems doc.children .child (.doc doc.children 0)).filter
      (XPath.Full.matchesTest doc.children [] .child .anyName)).length == 1
  | .error _ => false

end L4Factoidal.XPath4
