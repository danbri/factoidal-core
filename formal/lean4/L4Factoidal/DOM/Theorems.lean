/-
L4Factoidal.DOM.Theorems — properties of the DOM arena
(`L4Factoidal/DOM/Arena.lean`) that hold on every arena.

- `ensurePreInsertValidity_rejects_ancestor`: when `node` is a host-including
  inclusive ancestor of `parent`, ensure pre-insert validity (DOM §4.2.3) throws
  a HierarchyRequestError, whatever `child` and the excluded children are. This
  is the rule that keeps an insertion from making a cycle.
- `preInsert_rejects_ancestor`, `appendChild_self`: the same for pre-insert and
  for `n.appendChild(n)`, which give back the arena unchanged; and
  `replace_rejects_ancestor` for replace.
- `remove_parent_none`, `remove_not_child`: after "remove", the node has no
  parent and is not among the children of its old parent.

The tree invariant (`Dom.wellFormed`) is checked after every operation of the
differential test (`tests/dom/run.sh`); that every operation keeps it is not
proved yet: https://github.com/danbri/factoidal/issues/1216.
-/
import L4Factoidal.DOM.Arena

namespace L4Factoidal.DOM.Dom

theorem ensurePreInsertValidity_rejects_ancestor (d : Dom) (node parent : NodeId)
    (child : Option NodeId) (excl : List NodeId)
    (h : d.isHostIncludingInclusiveAncestor node parent = true) :
    d.ensurePreInsertValidity node parent child excl = .error .hierarchyRequest := by
  unfold ensurePreInsertValidity
  by_cases h1 : ((d.get parent).type == .document || (d.get parent).type == .fragment ||
      (d.get parent).type == .element) = true
  · simp only [h1, h] ; rfl
  · simp only [Bool.not_eq_true] at h1
    simp only [h1] ; rfl

/-- Pre-insert of an ancestor throws, and the arena is unchanged. -/
theorem preInsert_rejects_ancestor (d : Dom) (node parent : NodeId) (child : Option NodeId)
    (h : d.isHostIncludingInclusiveAncestor node parent = true) :
    d.preInsert node parent child = (d, .error .hierarchyRequest) := by
  unfold preInsert
  rw [ensurePreInsertValidity_rejects_ancestor d node parent child [] h]

/-- Replace with an ancestor throws, and the arena is unchanged. -/
theorem replace_rejects_ancestor (d : Dom) (child node parent : NodeId)
    (h : d.isHostIncludingInclusiveAncestor node parent = true) :
    d.replace child node parent = (d, .error .hierarchyRequest) := by
  unfold replace
  rw [ensurePreInsertValidity_rejects_ancestor d node parent (some child) [child] h]

/-- Every node is a host-including inclusive ancestor of itself. -/
theorem hostIncluding_self (d : Dom) (n : NodeId) : d.isHostIncludingInclusiveAncestor n n = true := by
  unfold isHostIncludingInclusiveAncestor
  rw [show 2 * d.size + 2 = (2 * d.size + 1) + 1 by omega]
  simp [hostWalk]

/-- `n.appendChild(n)` throws a HierarchyRequestError. -/
theorem appendChild_self (d : Dom) (n : NodeId) : d.appendChild n n = (d, .error .hierarchyRequest) :=
  preInsert_rejects_ancestor d n n none (hostIncluding_self d n)

theorem get_setNode_self (d : Dom) (i : NodeId) (f : Node → Node) (hi : i < d.size) :
    (d.setNode i f).get i = f (d.get i) := by
  simp [get, setNode, size] at *
  simp [hi, Array.getElem_modify]

theorem get_setNode_other (d : Dom) (i j : NodeId) (f : Node → Node) (hij : i ≠ j) :
    (d.setNode i f).get j = d.get j := by
  simp [get, setNode, Array.getD_eq_getD_getElem?, Array.getElem?_modify, hij]

theorem size_setNode (d : Dom) (i : NodeId) (f : Node → Node) : (d.setNode i f).size = d.size := by
  simp [setNode, size]

theorem remove_parent_none (d : Dom) (n : NodeId) (hn : n < d.size) :
    ((d.remove n).get n).parent = none := by
  unfold remove
  split
  · assumption
  · rw [get_setNode_self _ _ _ (by rw [size_setNode]; exact hn)]

theorem remove_not_child (d : Dom) (n p : NodeId) (hp : (d.get n).parent = some p) (hpn : p ≠ n)
    (hpsize : p < d.size) : n ∉ ((d.remove n).get p).kids := by
  unfold remove
  rw [hp]
  simp only
  rw [get_setNode_other _ _ _ _ (Ne.symm hpn), get_setNode_self _ _ _ hpsize]
  simp [Array.mem_filter]

end L4Factoidal.DOM.Dom
