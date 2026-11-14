import L4Factoidal.Rendering.Fragment

/-! `offsetParent` (CSSOM View §7 "Extensions to the HTMLElement interface"): the
ancestor that `offsetLeft` and `offsetTop` are measured from. The decision is here; the
host only wraps the node. -/
namespace L4Factoidal.Rendering.Layout
open DOM CSS

/-- An ancestor at which the walk of `offsetParent` stops: a positioned element, the
`body`, or, for an element that is not positioned itself (`plain`), a `td`, `th` or
`table`. -/
def isOffsetAncestor (dom : Dom) (styles : Array Computed) (plain : Bool) (a : Nat) : Bool :=
  let n := dom.get a
  n.type == .element &&
    ((styles[a]?.map (·.pos.isPositioned)).getD false || DOM.Dom.isHtmlElement n "body" ||
     (plain && (DOM.Dom.isHtmlElement n "td" || DOM.Dom.isHtmlElement n "th" || DOM.Dom.isHtmlElement n "table")))

/-- The nearest node from `id` upwards (itself included) that `isOffsetAncestor` accepts. -/
def offsetAncestor (dom : Dom) (styles : Array Computed) (plain : Bool) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel+1, id =>
    if isOffsetAncestor dom styles plain id then some id
    else (dom.get id).parent.bind (offsetAncestor dom styles plain fuel)

/-- CSSOM View §7 `offsetParent`: none for a node that is not an element, has no box
(`display: none`), is fixed, is the `body` or is the root element; else the nearest
ancestor that is positioned, or the `body`, or (for an element that is not positioned)
a table cell or table. -/
def offsetParent (dom : Dom) (styles : Array Computed) (id : Nat) : Option Nat :=
  let n := dom.get id
  match styles[id]? with
  | none => none
  | some s =>
    let root := (n.parent.map fun p => (dom.get p).type != .element).getD true
    if n.type != .element || s.display == .none || s.pos.position == .fixed ||
        DOM.Dom.isHtmlElement n "body" || root then none
    else n.parent.bind (offsetAncestor dom styles (s.pos.position == .static) (dom.size+1))

/-- Kind: soundness. Says: the walk answers only a node that `isOffsetAncestor` accepts.
Does not say: that it is the nearest such ancestor (it is, by the order of the walk; not
stated here). -/
theorem offsetAncestor_sound (dom : Dom) (styles : Array Computed) (plain : Bool) (fuel start a : Nat)
    (found : offsetAncestor dom styles plain fuel start = some a) :
    isOffsetAncestor dom styles plain a = true := by
  induction fuel generalizing start with
  | zero => simp [offsetAncestor] at found
  | succ fuel ih =>
    simp only [offsetAncestor] at found
    split at found
    · rename_i condition
      simp only [Option.some.injEq] at found
      rw [← found]; exact condition
    · cases parent : (dom.get start).parent with
      | none => simp [parent] at found
      | some p => exact ih p (by simpa [parent] using found)

/-- Kind: soundness. Says: an element's offset parent, when it has one, is an element
that is positioned, or the `body`, or a table cell or table: never an arbitrary ancestor.
Does not say: that the offsets a host reports are measured from it (the read answer in
`WebDocument.readAnswer` does that; tested). -/
theorem offsetParent_sound (dom : Dom) (styles : Array Computed) (id a : Nat)
    (found : offsetParent dom styles id = some a) :
    ∃ plain, isOffsetAncestor dom styles plain a = true := by
  unfold offsetParent at found
  split at found
  · simp at found
  · rename_i s _
    simp only at found
    split at found
    · simp at found
    · cases parent : (dom.get id).parent with
      | none => simp [parent] at found
      | some p =>
        rw [parent] at found
        exact ⟨_, offsetAncestor_sound dom styles _ _ p a (by simpa using found)⟩

end L4Factoidal.Rendering.Layout
