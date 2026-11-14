/-
L4Factoidal.DOM.Focus — which element takes the focus (HTML §6.6 "Focus").

Specification: HTML Living Standard §6.6.2 (focusable areas), §6.6.3 (the `tabindex`
attribute), §6.6.4 (the focusing steps, "get the focusable area"), DOM §4.8
(`delegatesFocus`).

The focused element is the page's state (it is mirrored into `Node.states` bit 8 so that
`:focus`, `:focus-visible` and `:focus-within` match). What `element.focus()` focuses is
decided here from the tree: the element when it is a focusable area, else, for a shadow host
whose shadow root delegates focus, the first focusable area inside.

Not decided here: whether the element is being rendered (a `display: none` element is not
focusable in a browser; here it is, an open item), and sequential (Tab) navigation.
-/
import L4Factoidal.DOM.Forms
import L4Factoidal.DOM.Shadow

namespace L4Factoidal.DOM.Focus
open L4Factoidal.DOM L4Factoidal.DOM.Forms

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\x0C' || c == '\r'

/-- A valid integer of a `tabindex` attribute (the rules for parsing integers, HTML §2.3.4.1). -/
def tabindex? (s : String) : Option Int :=
  let cs := s.toList.dropWhile isWs
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | '+' :: r => (false, r)
    | r => (false, r)
  let ds := cs.takeWhile fun c => '0' ≤ c && c ≤ '9'
  if ds.isEmpty then none
  else
    let v : Int := (ds.foldl (fun n c => n * 10 + (c.toNat - 48)) 0 : Nat)
    some (if neg then -v else v)

/-- An editing host: `contenteditable` in the true or plaintext-only state. -/
def editingHost (d : Dom) (k : NodeId) : Bool :=
  match attr? d k "contenteditable" with
  | some v => let l := Dom.asciiLower v; l == "" || l == "true" || l == "plaintext-only"
  | none => false

/-- A focusable area (HTML §6.6.2): an HTML element that is not a disabled form control and
that has a `tabindex` with a valid integer, or is one of the elements focusable by default:
`a` and `area` with `href`, `button`, `input` other than hidden, `select`, `textarea`, the
`summary` of a `details`, `iframe`, an editing host; an SVG `a` with `href`. -/
def focusable (d : Dom) (k : NodeId) : Bool :=
  let x := d.get k
  x.type == .element && !disabledControl d k &&
  (((attr? d k "tabindex").bind tabindex?).isSome ||
    (isHtml d k ["a", "area"] && (attr? d k "href").isSome) ||
    isHtml d k ["button", "select", "textarea", "iframe"] ||
    (isHtml d k ["input"] && inputType d k != "hidden") ||
    isDetailsSummary d k || (x.ns == some htmlNS && editingHost d k) ||
    (x.ns == some svgNS && x.lname == "a" && x.attrs.any fun a => a.lname == "href"))

/-- The first focusable area among the shadow-including descendants of `k`, in
shadow-including tree order (a shadow root's tree before the host's children). -/
def firstFocusableGo (d : Dom) : Nat → List NodeId → Option NodeId
  | 0, _ => none
  | _, [] => none
  | fuel + 1, x :: rest =>
    if focusable d x then some x
    else
      let nd := d.get x
      let shadow := match nd.shadow with | some s => [s] | none => []
      firstFocusableGo d fuel (shadow ++ nd.kids.toList ++ rest)

/-- "Get the focusable area" for `element.focus()` (HTML §6.6.4): the element when it is a
focusable area; for a shadow host whose shadow root has `delegatesFocus`, the first
focusable area in its shadow tree; else none (the focus does not move). -/
def focusTarget (d : Dom) (k : NodeId) : Option NodeId :=
  if focusable d k then some k
  else match (d.get k).shadow with
    | some s =>
      if ((d.get s).shadowInit.map (·.delegatesFocus)).getD false then
        firstFocusableGo d (d.size + 1) [s]
      else none
    | none => none

/-- The focus delegate of `k` (HTML §6.6.4, used by the dialog focusing steps): the first
focusable area among its shadow-including descendants, `k` itself excluded. -/
def focusDelegate (d : Dom) (k : NodeId) : Option NodeId :=
  let nd := d.get k
  firstFocusableGo d (d.size + 1) ((match nd.shadow with | some s => [s] | none => []) ++ nd.kids.toList)

/-- Wire form for the page objects (`node_query` op 189): with `q` "" the node that `focus()`
on `k` focuses, with "d" the focus delegate of `k`; "" for none. -/
def answer (d : Dom) (k : NodeId) (q : String) : String :=
  match (if q == "d" then focusDelegate d k else focusTarget d k) with
  | some t => toString t
  | none => ""

/-! ## What is proved -/

/-- Says: the walk answers only focusable areas. Does not say: that it is the first in tree
order on every arena (it is on a well-formed one, where the fuel suffices). -/
theorem firstFocusableGo_focusable (d : Dom) (fuel : Nat) (work : List NodeId) (t : NodeId)
    (h : firstFocusableGo d fuel work = some t) : focusable d t = true := by
  induction fuel generalizing work with
  | zero => simp [firstFocusableGo] at h
  | succ n ih =>
    cases work with
    | nil => simp [firstFocusableGo] at h
    | cons x rest =>
      simp only [firstFocusableGo] at h
      split at h
      · rename_i hx
        simp only [Option.some.injEq] at h
        subst h
        exact hx
      · exact ih _ h

/-- Says: `focus()` only ever focuses a focusable area: whatever element it is called on,
the node that takes the focus satisfies `focusable`. -/
theorem focusTarget_focusable (d : Dom) (k t : NodeId) (h : focusTarget d k = some t) :
    focusable d t = true := by
  unfold focusTarget at h
  split at h
  · rename_i hk
    simp only [Option.some.injEq] at h
    subst h
    exact hk
  · split at h
    · split at h
      · exact firstFocusableGo_focusable d _ _ t h
      · simp at h
    · simp at h

/-- Says: a focus delegate is a focusable area. -/
theorem focusDelegate_focusable (d : Dom) (k t : NodeId) (h : focusDelegate d k = some t) :
    focusable d t = true := firstFocusableGo_focusable d _ _ t h

/-- Refusal. Says: a disabled form control is not a focusable area, so (with the theorems
above) script can never focus one. -/
theorem disabled_not_focusable (d : Dom) (k : NodeId) (h : disabledControl d k = true) :
    focusable d k = false := by
  simp [focusable, h]

/-! ## Tests -/

private def el (lname : String) (attrs : List (String × String)) (parent : Option NodeId) (kids : List NodeId)
    (shadow : Option NodeId := none) : Node :=
  { type := .element, ns := some htmlNS, lname, parent, kids := kids.toArray, shadow,
    attrs := (attrs.map fun (k, v) => ({ lname := k, value := v } : Attr)).toArray }

/-- 0 document > div(1), button(2), button disabled(3), div tabindex=-1(4), a(5), a href(6),
div host(7) [shadow root 8 delegatesFocus > span(9), input(10)], div host(11) [shadow root 12 > input(13)],
input type=hidden(14), div contenteditable(15). -/
private def tree : Dom :=
  { nodes := #[
      { type := .document, kids := #[1, 2, 3, 4, 5, 6, 7, 11, 14, 15] },
      el "div" [] (some 0) [], el "button" [] (some 0) [], el "button" [("disabled", "")] (some 0) [],
      el "div" [("tabindex", "-1")] (some 0) [], el "a" [] (some 0) [], el "a" [("href", "x")] (some 0) [],
      el "div" [] (some 0) [] (some 8),
      { type := .fragment, host := some 7, kids := #[9, 10], shadowInit := some { delegatesFocus := true } },
      el "span" [] (some 8) [], el "input" [] (some 8) [],
      el "div" [] (some 0) [] (some 12),
      { type := .fragment, host := some 11, kids := #[13], shadowInit := some {} },
      el "input" [] (some 12) [],
      el "input" [("type", "hidden")] (some 0) [], el "div" [("contenteditable", "")] (some 0) []] }

#guard !focusable tree 1 && focusable tree 2 && !focusable tree 3 && focusable tree 4 && !focusable tree 5 && focusable tree 6
#guard !focusable tree 14 && focusable tree 15
#guard focusTarget tree 7 == some 10 && focusTarget tree 11 == none && focusTarget tree 2 == some 2 && focusTarget tree 1 == none
#guard answer tree 7 "" == "10" && answer tree 1 "" == "" && answer tree 0 "d" == "2" && answer tree 11 "d" == "13" && answer tree 1 "d" == ""
#guard tabindex? " -1" == some (-1) && tabindex? "3px" == some 3 && tabindex? "x" == none && tabindex? "" == none

end L4Factoidal.DOM.Focus
