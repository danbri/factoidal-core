/-
L4Factoidal.DOM.Editing.Inline — the inline formatting commands of the editing draft.

Specification: W3C Editing APIs draft, "Inline formatting commands": the definitions
(effectively contained, modifiable and simple modifiable elements, formattable nodes,
equivalent and loosely equivalent values, effective and specified command value) and the
algorithms (record and restore the values, clear the value, push down values, force the
value, set the selection's value), and the commands built on them: `backColor`, `bold`,
`createLink`, `fontName`, `fontSize`, `foreColor`, `hiliteColor`, `italic`,
`removeFormat`, `strikethrough`, `subscript`, `superscript`, `underline`, `unlink`.

A command name is its ASCII-lowercase string; a command value is `Option String` (`none`
is the draft's null).

Proved: the state overrides (`getState_setState`: a toggle with nothing to format is read
back by the next state query; `setState_toggle`), and the laws of equivalent values
(`equivalentValues_refl`). Tested only (the WPT cases in `tests/editing`): the tree
algorithms.
-/
import L4Factoidal.DOM.Editing.Core

namespace L4Factoidal.DOM.Editing
open L4Factoidal.DOM L4Factoidal.DOM.Range

/-! ## Command tables -/

/-- The "relevant CSS property" of a command. -/
def relevantCssProperty (command : String) : Option String :=
  match command with
  | "backcolor" | "hilitecolor" => some "background-color"
  | "bold" => some "font-weight"
  | "fontname" => some "font-family"
  | "fontsize" => some "font-size"
  | "forecolor" => some "color"
  | "italic" => some "font-style"
  | _ => none

/-- The "inline command activated values" of a command. -/
def inlineActivatedValues (command : String) : Option (List String) :=
  match command with
  | "bold" => some ["bold", "600", "700", "800", "900"]
  | "italic" => some ["italic", "oblique"]
  | "strikethrough" => some ["line-through"]
  | "subscript" => some ["subscript"]
  | "superscript" => some ["superscript"]
  | "underline" => some ["underline"]
  | _ => none

/-- The commands with the standard inline value behaviour. -/
def isStandardInlineValueCommand (command : String) : Bool :=
  ["backcolor", "fontname", "forecolor", "hilitecolor"].contains command

/-- "Equivalent values" of a command. -/
def equivalentValues (command : String) (a b : Option String) : Bool :=
  match a, b with
  | none, none => true
  | some x, some y =>
    if command == "bold" then
      x == y || (x == "bold" && y == "700") || (x == "700" && y == "bold") ||
        (x == "normal" && y == "400") || (x == "400" && y == "normal")
    else if command == "backcolor" || command == "forecolor" || command == "hilitecolor" then
      decide (parseColor x = parseColor y)
    else x == y
  | _, _ => false

/-- Law. Says: a value is equivalent to itself, for every command. Does not say:
symmetry or transitivity (both hold for the three kinds of command, not stated here). -/
theorem equivalentValues_refl (command : String) (a : Option String) : equivalentValues command a a = true := by
  cases a with
  | none => rfl
  | some x => simp only [equivalentValues]; split <;> (try split) <;> simp

/-- The pixel text of a legacy size keyword ("medium" is "16px"). -/
def keywordPx (k : String) : Option String :=
  match cssSizeToLegacy k with
  | some _ => (sizeKeywords.find? (·.1 == k)).map fun (_, px) => pxText px
  | none => none

/-- "Loosely equivalent values": equivalent, or for `fontSize` a pixel size and the
keyword of that size. -/
def looselyEquivalentValues (command : String) (a b : Option String) : Bool :=
  equivalentValues command a b ||
    (command == "fontsize" && match a, b with
      | some x, some y => keywordPx y == some x || keywordPx x == some y
      | _, _ => false)

/-! ## State and value overrides -/

/-- The overrides hold for one active range: a different range forgets them. -/
def resetOverrides : M Unit := modify fun e =>
  if e.ovRange == some (activeOf e) then e
  else { e with stateOv := [], valueOv := [], ovRange := some (activeOf e) }

def getStateOverride (command : String) : M (Option Bool) := do
  resetOverrides
  rd fun e => (e.stateOv.find? (·.1 == command)).map (·.2)

def setStateOverride (command : String) (v : Bool) : M Unit := do
  resetOverrides
  modify fun e => { e with stateOv := (command, v) :: e.stateOv.filter (·.1 != command) }

def unsetStateOverride (command : String) : M Unit := do
  resetOverrides
  modify fun e => { e with stateOv := e.stateOv.filter (·.1 != command) }

def getValueOverride (command : String) : M (Option String) := do
  resetOverrides
  rd fun e => (e.valueOv.find? (·.1 == command)).map (·.2)

def setValueOverride (command : String) (v : String) : M Unit := do
  resetOverrides
  let names := if command == "backcolor" || command == "hilitecolor" then ["backcolor", "hilitecolor"] else [command]
  modify fun e => { e with valueOv := names.map (·, v) ++ e.valueOv.filter (fun p => !names.contains p.1) }

def unsetValueOverride (command : String) : M Unit := do
  resetOverrides
  let names := if command == "backcolor" || command == "hilitecolor" then ["backcolor", "hilitecolor"] else [command]
  modify fun e => { e with valueOv := e.valueOv.filter (fun p => !names.contains p.1) }

/-- The state overrides as a pure list, for the theorems. -/
def setStateList (ov : List (String × Bool)) (command : String) (v : Bool) : List (String × Bool) :=
  (command, v) :: ov.filter (·.1 != command)

def getStateList (ov : List (String × Bool)) (command : String) : Option Bool :=
  (ov.find? (·.1 == command)).map (·.2)

/-- State override. Says: after a command's state override is set, the override read for
that command is the value set. Does not say: what the state is when the active range
changes (the overrides are then dropped). -/
theorem getState_setState (ov : List (String × Bool)) (command : String) (v : Bool) :
    getStateList (setStateList ov command v) command = some v := by
  simp [getStateList, setStateList]

/-- Toggle. Says: setting the override to the negation of the override that is read
gives the negation back: with nothing to format, a second toggle undoes the first. Does
not say: that the selection's formatting toggles when there are nodes to format (tested
by the WPT cases). -/
theorem setState_toggle (ov : List (String × Bool)) (command : String) (b : Bool)
    (_h : getStateList ov command = some b) :
    getStateList (setStateList ov command (!b)) command = some (!b) := by
  simp [getStateList, setStateList]

/-! ## Definitions -/

/-- "Effectively contained" in a range. -/
def isEffectivelyContainedF (d : Dom) (r : Rng) : Nat → NodeId → Bool
  | 0, _ => false
  | fuel + 1, n =>
    if r.collapsed then false
    else if contained d r n then true
    else if n == r.start.node && isText d n && nodeLength d n != r.start.offset then true
    else if n == r.stop.node && isText d n && r.stop.offset != 0 then true
    else
      hasKids d n && (kidsOf d n).all (isEffectivelyContainedF d r fuel) &&
        (!isAncestor d n r.start.node || !isText d r.start.node || r.start.offset == 0) &&
        (!isAncestor d n r.stop.node || !isText d r.stop.node || r.stop.offset == nodeLength d r.stop.node)

def isEffectivelyContained (d : Dom) (r : Rng) (n : NodeId) : Bool :=
  isEffectivelyContainedF d r (d.size + 1) n

/-- The nodes effectively contained in `r` that `cond` accepts, in tree order (with
descendants of accepted nodes). -/
def allEffectivelyContained (e : Ed) (r : Rng) (cond : NodeId → Bool) : Array NodeId := Id.run do
  let d := e.dom
  let mut node := r.start.node
  for _ in [0:d.size + 1] do
    match parentOf d node with
    | some p => if isEffectivelyContained d r p then node := p else break
    | none => break
  let stop := nextNodeDesc d r.stop.node
  let mut out : Array NodeId := #[]
  let mut cur := some node
  for _ in [0:d.size + 1] do
    match cur with
    | none => break
    | some c =>
      if !isBefore d (some c) stop then break
      if isEffectivelyContained d r c && cond c then out := out.push c
      cur := nextNode d c
  return out

/-- As `allEffectivelyContained`, without the descendants of an accepted node. -/
def effectivelyContained (e : Ed) (r : Rng) (cond : NodeId → Bool) : Array NodeId := Id.run do
  let d := e.dom
  let mut node := r.start.node
  for _ in [0:d.size + 1] do
    match parentOf d node with
    | some p => if isEffectivelyContained d r p then node := p else break
    | none => break
  let stop := nextNodeDesc d r.stop.node
  let mut out : Array NodeId := #[]
  let mut cur := some node
  for _ in [0:d.size + 1] do
    match cur with
    | none => break
    | some c =>
      if !isBefore d (some c) stop then break
      if isEffectivelyContained d r c && cond c then
        out := out.push c
        cur := nextNodeDesc d c
      else cur := nextNode d c
  return out

/-- The number of declarations of the element's `style` attribute. -/
def styleLength (d : Dom) (n : NodeId) : Nat := (styleDecls d n).length

/-- "Modifiable element". -/
def isModifiableElement (d : Dom) (n : NodeId) : Bool :=
  isHtmlEl d n &&
    (let tag := (d.get n).lname
     let na := attrCount d n
     (["b", "em", "i", "s", "span", "strike", "strong", "sub", "sup", "u"].contains tag &&
        (na == 0 || (na == 1 && hasAttr d n "style"))) ||
     ((tag == "font" || tag == "a") &&
        (let c := na - (if hasAttr d n "style" then 1 else 0)
         let c := if tag == "font" then
            c - (if hasAttr d n "color" then 1 else 0) - (if hasAttr d n "face" then 1 else 0) -
              (if hasAttr d n "size" then 1 else 0)
           else c
         let c := if tag == "a" && hasAttr d n "href" then c - 1 else c
         c == 0)))

/-- "Simple modifiable element". -/
def isSimpleModifiableElement (d : Dom) (n : NodeId) : Bool := Id.run do
  if !isHtmlEl d n then return false
  let tag := (d.get n).lname
  if !(["a", "b", "em", "font", "i", "s", "span", "strike", "strong", "sub", "sup", "u"].contains tag) then return false
  let na := attrCount d n
  if na == 0 then return true
  if na > 1 then return false
  let hasStyle := hasAttr d n "style"
  let len := styleLength d n
  if hasStyle && len == 0 then return true
  if tag == "a" && hasAttr d n "href" then return true
  if tag == "font" && (hasAttr d n "color" || hasAttr d n "face" || hasAttr d n "size") then return true
  if (tag == "b" || tag == "strong") && hasStyle && len == 1 && styleGet d n "font-weight" != "" then return true
  if (tag == "i" || tag == "em") && hasStyle && len == 1 && styleGet d n "font-style" != "" then return true
  let td := lower (styleGet d n "text-decoration")
  if (tag == "a" || tag == "font" || tag == "span") && hasStyle && len == 1 && td == "" then return true
  if ["a", "font", "s", "span", "strike", "u"].contains tag && hasStyle && len == 1 &&
      (td == "line-through" || td == "underline" || td == "overline" || td == "none") then return true
  return false

/-- "Formattable node": an editable visible node that is a Text node, an `img` or a `br`. -/
def isFormattableNode (e : Ed) (n : NodeId) : Bool :=
  isEditable e n && isVisible e n && (isText e.dom n || isHtml e.dom n ["img", "br"])

def containsSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- "Effective command value" of a node. -/
def effectiveCommandValue (e : Ed) (node : NodeId) (command : String) : Option String := Id.run do
  let d := e.dom
  let mut node := node
  if !isEl d node then
    match parentOf d node with
    | some p => if isEl d p then node := p else return none
    | none => return none
  if command == "createlink" || command == "unlink" then
    return ((chain d node).toList.reverse.find? fun a => isHtml d a ["a"] && hasAttr d a "href").bind fun a => attr d a "href"
  if command == "backcolor" || command == "hilitecolor" then
    for _ in [0:d.size + 1] do
      if (styleOf e.env d node).background.a == 0 then
        match parentOf d node with
        | some p => if isEl d p then node := p else break
        | none => break
      else break
    return some (styleOf e.env d node).background.text
  if command == "subscript" || command == "superscript" then
    let mut sub := false
    let mut sup := false
    let mut cur := some node
    for _ in [0:d.size + 1] do
      match cur with
      | some c =>
        if !isInlineNode e c then break
        if isHtml d c ["sub"] then sub := true
        else if isHtml d c ["sup"] then sup := true
        cur := parentOf d c
      | none => break
    return if sub && sup then some "mixed" else if sub then some "subscript" else if sup then some "superscript" else none
  if command == "strikethrough" then
    return if (chain d node).any (fun a => isEl d a && containsSub (styleOf e.env d a).textDecoration "line-through")
      then some "line-through" else none
  if command == "underline" then
    return if (chain d node).any (fun a => isEl d a && containsSub (styleOf e.env d a).textDecoration "underline")
      then some "underline" else none
  let st := styleOf e.env d node
  match command with
  | "bold" => return some (toString st.fontWeight)
  | "italic" => return some st.fontStyle
  | "fontname" => return some st.fontFamily
  | "fontsize" => return some (pxText st.fontSize)
  | "forecolor" => return some st.color.text
  | _ => return none

/-- "Specified command value" of an element. -/
def specifiedCommandValue (e : Ed) (el : NodeId) (command : String) : Option String := Id.run do
  let d := e.dom
  if (command == "backcolor" || command == "hilitecolor") && displayOf e el != "inline" then return none
  if command == "createlink" || command == "unlink" then
    return if isHtml d el ["a"] then attr d el "href" else none
  if command == "subscript" || command == "superscript" then
    return if isHtml d el ["sup"] then some "superscript" else if isHtml d el ["sub"] then some "subscript" else none
  let td := styleGet d el "text-decoration"
  if command == "strikethrough" && td != "" then
    return if containsSub td "line-through" then some "line-through" else none
  if command == "strikethrough" && isHtml d el ["s", "strike"] then return some "line-through"
  if command == "underline" && td != "" then
    return if containsSub td "underline" then some "underline" else none
  if command == "underline" && isHtml d el ["u"] then return some "underline"
  let some property := relevantCssProperty command | return none
  let v := styleGet d el property
  if v != "" then return some v
  if isHtml d el ["font"] then
    if property == "color" then
      if let some c := attr d el "color" then return some c
    if property == "font-family" then
      if let some f := attr d el "face" then return some f
    if property == "font-size" then
      if let some sz := attr d el "size" then
        -- `parseInt`: an optional sign and digits
        let cs := trimChars sz.toList
        let (neg, ds) := match cs with
          | '-' :: r => (true, r)
          | '+' :: r => (false, r)
          | r => (false, r)
        let ds := ds.takeWhile Char.isDigit
        if !ds.isEmpty then
          let n := ds.foldl (fun n c => n * 10 + (c.toNat - 48)) 0
          let n := if neg then 1 else max 1 (min 7 n)
          return some (legacySizeToCss n)
  if property == "font-weight" && isHtml d el ["b", "strong"] then return some "bold"
  if property == "font-style" && isHtml d el ["i", "em"] then return some "italic"
  return none

/-! ## Recording and restoring values -/

def recordedCommands : List String :=
  ["subscript", "bold", "fontname", "fontsize", "forecolor", "hilitecolor", "italic", "strikethrough", "underline"]

/-- The nearest inclusive ancestor element of `n` with a specified value for `command`. -/
def specifiedAncestor (e : Ed) (n : NodeId) (command : String) : Option NodeId :=
  let d := e.dom
  let start := if isEl d n then some n else parentOf d n
  match start with
  | none => none
  | some s => ((chain d s).toList.reverse.takeWhile (isEl d)).find? fun a => (specifiedCommandValue e a command).isSome

/-- "Record the values" of a list of nodes: for each node and each recorded command, the
specified value of the nearest ancestor that has one. -/
def recordValues (e : Ed) (nodes : Array NodeId) : Array (NodeId × String × Option String) :=
  (nodes.toList.flatMap fun n => recordedCommands.map fun c =>
    (n, c, (specifiedAncestor e n c).bind fun a => specifiedCommandValue e a c)).toArray

/-- Record. Says: `recordValues` makes one entry per node and recorded command (nine a
node), in the nodes' order. Does not say: that restoring the entries on an unchanged tree
changes nothing (tested, not proved). -/
theorem recordValues_size (e : Ed) (nodes : Array NodeId) :
    (recordValues e nodes).size = nodes.size * recordedCommands.length := by
  unfold recordValues
  have h9 : recordedCommands.length = 9 := rfl
  simp only [List.size_toArray, h9]
  rw [← Array.length_toList]
  induction nodes.toList with
  | nil => simp
  | cons h t ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_map, List.length_cons, ih, h9]
    omega

/-! ## Clearing, pushing down and forcing values -/

/-- "Clear the value" of an element: the nodes that take its place. -/
def clearValue (el : NodeId) (command : String) : M (Array NodeId) := do
  let e ← get
  let d := e.dom
  if !isEditable e el then return #[]
  if (specifiedCommandValue e el command).isNone then return #[]
  if isSimpleModifiableElement d el then
    let children := kidsOf d el
    let some p := parentOf d el | return #[]
    for c in children do
      let i ← rd fun e => indexOf e.dom el
      movePreservingRanges c p (some i)
    removeNode el
    return children
  let td := styleGet d el "text-decoration"
  if command == "strikethrough" && containsSub td "line-through" then
    let rest := trimStr (" ".intercalate ((td.splitOn " ").filter fun w => w != "line-through" && w != ""))
    styleSet el "text-decoration" rest
    if (← rd fun e => attr e.dom el "style") == some "" then removeAttr el "style"
  let td := ← rd fun e => styleGet e.dom el "text-decoration"
  if command == "underline" && containsSub td "underline" then
    let rest := trimStr (" ".intercalate ((td.splitOn " ").filter fun w => w != "underline" && w != ""))
    styleSet el "text-decoration" rest
    if (← rd fun e => attr e.dom el "style") == some "" then removeAttr el "style"
  if let some property := relevantCssProperty command then
    if (← rd fun e => styleGet e.dom el property) != "" then
      styleSet el property ""
    if (← rd fun e => attr e.dom el "style") == some "" then removeAttr el "style"
  if isHtml d el ["font"] then
    if command == "forecolor" then removeAttr el "color"
    if command == "fontname" then removeAttr el "face"
    if command == "fontsize" then removeAttr el "size"
  if isHtml d el ["a"] && (command == "createlink" || command == "unlink") then removeAttr el "href"
  let e ← get
  if (specifiedCommandValue e el command).isNone then return #[]
  let r ← setTagName el "span"
  return #[r]

/-- "Reorder modifiable descendants" of a node. -/
def reorderModifiableDescendants (node : Option NodeId) (command : String) (newValue : Option String) : M Unit := do
  let some node := node | return
  let e ← get
  let d := e.dom
  let mut candidate := node
  for _ in [0:d.size + 1] do
    if isModifiableElement d candidate && (kidsOf d candidate).size == 1 &&
        isModifiableElement d (kidsOf d candidate)[0]! &&
        (!isSimpleModifiableElement d candidate ||
          !equivalentValues command (specifiedCommandValue e candidate command) newValue) then
      candidate := (kidsOf d candidate)[0]!
    else break
  if candidate == node || !isSimpleModifiableElement d candidate ||
      !equivalentValues command (specifiedCommandValue e candidate command) newValue ||
      !looselyEquivalentValues command (effectiveCommandValue e candidate command) newValue then return
  let some cp := parentOf d candidate | return
  for c in kidsOf d candidate do
    let i ← rd fun e => indexOf e.dom candidate
    movePreservingRanges c cp (some i)
  let d ← rd (·.dom)
  let some np := parentOf d node | return
  insertBefore np candidate (d.nextSibling node)
  movePreservingRanges node candidate none

/-- The children of `node` that "force the value" goes on to: those with no specified
value for the command, or with one equivalent to the new value. -/
def forceChildren (e : Ed) (node : NodeId) (command : String) (newValue : Option String) : Array NodeId :=
  (kidsOf e.dom node).filter fun c =>
    !(isEl e.dom c &&
      (match specifiedCommandValue e c command with
        | some v => !equivalentValues command newValue (some v)
        | none => false))

/-- "Force the value" of a node. `fuel` bounds the recursion by the tree's depth. -/
def forceValue : Nat → NodeId → String → Option String → M Unit
  | 0, _, _, _ => pure ()
  | fuel + 1, node, command, newValue => do
    let e ← get
    let d := e.dom
    if (parentOf d node).isNone then return
    let some nv := newValue | return
    if isAllowedChildOfName e (.node node) "span" then
      reorderModifiableDescendants (d.previousSibling node) command newValue
      reorderModifiableDescendants ((← rd (·.dom)).nextSibling node) command newValue
      let _ ← wrap #[node]
        (fun e n => isSimpleModifiableElement e.dom n &&
          equivalentValues command (specifiedCommandValue e n command) newValue &&
          looselyEquivalentValues command (effectiveCommandValue e n command) newValue)
        (pure none)
    let e ← get
    let d := e.dom
    if isInvisible e node then return
    if looselyEquivalentValues command (effectiveCommandValue e node command) newValue then return
    if !isAllowedChildOfName e (.node node) "span" then
      for c in forceChildren e node command newValue do forceValue fuel c command newValue
      return
    let mut newParent : Option NodeId := none
    if !e.css then
      if command == "bold" && (nv == "bold" || nv == "700") then newParent := some (← createElement "b")
      if command == "italic" && nv == "italic" then newParent := some (← createElement "i")
      if command == "strikethrough" && nv == "line-through" then newParent := some (← createElement "strike")
      if command == "underline" && nv == "underline" then newParent := some (← createElement "u")
      if command == "forecolor" then
        if let some c := simpleColor nv then
          let f ← createElement "font"
          setAttr f "color" c
          newParent := some f
      if command == "fontname" then
        let f ← createElement "font"
        setAttr f "face" nv
        newParent := some f
    if command == "createlink" || command == "unlink" then
      let a ← createElement "a"
      setAttr a "href" nv
      newParent := some a
      let mut ancestor := parentOf d node
      for _ in [0:d.size + 1] do
        match ancestor with
        | some anc =>
          let dd ← rd (·.dom)
          let anc ← if isHtml dd anc ["a"] then setTagName anc "span" else pure anc
          ancestor := parentOf (← rd (·.dom)) anc
        | none => break
    if command == "fontsize" && (cssSizeToLegacy nv).isSome && (!e.css || nv == "xxx-large") then
      let f ← createElement "font"
      setAttr f "size" (toString ((cssSizeToLegacy nv).getD 3))
      newParent := some f
    if (command == "subscript" || command == "superscript") && nv == "subscript" then
      newParent := some (← createElement "sub")
    if (command == "subscript" || command == "superscript") && nv == "superscript" then
      newParent := some (← createElement "sup")
    let np ← match newParent with
      | some p => pure p
      | none => createElement "span"
    let d ← rd (·.dom)
    let some p := parentOf d node | return
    insertBefore p np (some node)
    let e ← get
    if let some property := relevantCssProperty command then
      if !looselyEquivalentValues command (effectiveCommandValue e np command) newValue then
        styleSet np property nv
    let e ← get
    if command == "strikethrough" && nv == "line-through" &&
        effectiveCommandValue e np "strikethrough" != some "line-through" then
      styleSet np "text-decoration" "line-through"
    if command == "underline" && nv == "underline" && effectiveCommandValue e np "underline" != some "underline" then
      styleSet np "text-decoration" "underline"
    movePreservingRanges node np none
    let e ← get
    let d := e.dom
    if isEl d node && !equivalentValues command (effectiveCommandValue e node command) newValue then
      let some npp := parentOf d np | return
      movePreservingRanges node npp (some (indexOf d np))
      removeNode np
      let e ← get
      for c in forceChildren e node command newValue do forceValue fuel c command newValue

/-- "Push down values" to a node. -/
def pushDownValues (node : NodeId) (command : String) (newValue : Option String) : M Unit := do
  let e ← get
  let d := e.dom
  let some p := parentOf d node | return
  if !isEl d p then return
  if looselyEquivalentValues command (effectiveCommandValue e node command) newValue then return
  let mut current := some p
  let mut ancestorList : Array NodeId := #[]
  for _ in [0:d.size + 1] do
    match current with
    | some c =>
      if isEditable e c && isEl d c && !looselyEquivalentValues command (effectiveCommandValue e c command) newValue then
        ancestorList := ancestorList.push c
        current := parentOf d c
      else break
    | none => break
  if ancestorList.isEmpty then return
  let top := ancestorList.back!
  let mut propagated := specifiedCommandValue e top command
  if propagated.isNone && propagated != newValue then return
  if newValue.isSome then
    match parentOf d top with
    | some tp =>
      if !looselyEquivalentValues command (effectiveCommandValue e tp command) newValue then return
    | none => return
  let fuel := d.size + 1
  let mut list := ancestorList
  for _ in [0:ancestorList.size] do
    let some cur := list.back? | break
    list := list.pop
    let e ← get
    let d := e.dom
    let spec := specifiedCommandValue e cur command
    if spec.isSome then propagated := spec
    let children := kidsOf d cur
    if spec.isSome then
      let _ ← clearValue cur command
    for child in children do
      if child == node then continue
      let e ← get
      if isEl e.dom child then
        if let some cv := specifiedCommandValue e child command then
          if !equivalentValues command propagated (some cv) then continue
      if some child == list.back? then continue
      forceValue fuel child command propagated

/-- "Restore the values" recorded by `recordValues`. -/
def restoreValues (values : Array (NodeId × String × Option String)) : M Unit := do
  for (node, command, value) in values do
    let e ← get
    let ancestor := specifiedAncestor e node command
    match value, ancestor with
    | none, some _ => pushDownValues node command none
    | _, some a =>
      if !equivalentValues command (specifiedCommandValue e a command) value then
        forceValue (e.dom.size + 1) node command value
    | some _, none => forceValue (e.dom.size + 1) node command value
    | none, none => pure ()

/-- Split the Text nodes at the ends of the active range, so that the range holds whole
nodes (the two steps at the start of "set the selection's value"). -/
def splitRangeEnds : M Unit := do
  let e ← get
  let r := activeOf e
  let d := e.dom
  if isEditable e r.start.node && isText d r.start.node && r.start.offset != 0 &&
      r.start.offset != nodeLength d r.start.node then
    let sameNode := r.start.node == r.stop.node
    let newEnd := r.stop.offset - r.start.offset
    let nn ← splitText r.start.node r.start.offset
    if nn != r.start.node then
      let r2 ← getActive
      setActive ⟨⟨nn, 0⟩, if sameNode then ⟨nn, newEnd⟩ else r2.stop⟩
  let e ← get
  let r := activeOf e
  let d := e.dom
  if isEditable e r.stop.node && isText d r.stop.node && r.stop.offset != 0 &&
      r.stop.offset != nodeLength d r.stop.node then
    let _ ← splitText r.stop.node r.stop.offset
    setActive r

/-- "Set the selection's value" for a command. -/
def setSelectionValue (command : String) (newValue : Option String) : M Unit := do
  let e ← get
  let r := activeOf e
  if !(allEffectivelyContained e r fun _ => true).any (isFormattableNode e) then
    if let some vals := inlineActivatedValues command then
      setStateOverride command (match newValue with
        | some v => vals.contains v
        | none => false)
    if command == "subscript" then unsetStateOverride "superscript"
    if command == "superscript" then unsetStateOverride "subscript"
    match newValue with
    | none => unsetValueOverride command
    | some v =>
      if command == "createlink" || isStandardInlineValueCommand command || command == "fontsize" then
        setValueOverride command v
    return
  splitRangeEnds
  let e ← get
  for el in allEffectivelyContained e (activeOf e) fun n => isEditable e n && isEl e.dom n do
    let _ ← clearValue el command
  let e ← get
  for node in allEffectivelyContained e (activeOf e) (isEditable e) do
    pushDownValues node command newValue
    let e ← get
    if (parentOf e.dom node).isSome && isAllowedChildOfName e (.node node) "span" then
      forceValue (e.dom.size + 1) node command newValue

/-! ## State, indeterminacy and value of the inline commands -/

/-- The effective values of the formattable nodes effectively contained in the active range. -/
def formattableValues (e : Ed) (command : String) : Array (Option String) :=
  (allEffectivelyContained e (activeOf e) (isFormattableNode e)).map fun n => effectiveCommandValue e n command

/-- The state of a command with inline command activated values (no override). -/
def inlineState (e : Ed) (command : String) (vals : List String) : Bool :=
  let nodes := allEffectivelyContained e (activeOf e) (isFormattableNode e)
  let on := fun (v : Option String) => match v with
    | some s => vals.contains s
    | none => false
  if nodes.isEmpty then on (effectiveCommandValue e (activeOf e).start.node command)
  else nodes.all fun n => on (effectiveCommandValue e n command)

def inlineIndeterm (e : Ed) (command : String) (vals : List String) : Bool :=
  let values := formattableValues e command
  let matching := values.filter fun v => match v with
    | some s => vals.contains s
    | none => false
  matching.size ≥ 1 && values.size - matching.size ≥ 1

/-- The value of a standard inline value command (no override). -/
def standardValue (e : Ed) (command : String) : String :=
  let nodes := allEffectivelyContained e (activeOf e) (isFormattableNode e)
  let ref := (nodes[0]?).getD (activeOf e).start.node
  (effectiveCommandValue e ref command).getD ""

def standardIndeterm (e : Ed) (command : String) : Bool := Id.run do
  let values := formattableValues e command
  for i in [1:values.size] do
    if values[i]! != values[i - 1]! then return true
  return false

/-- "Normalize" a `fontSize` value: a legacy size number, absolute or relative, as a keyword. -/
def normalizeFontSize (value : String) : Option String :=
  let cs := trimChars value.toList
  let (mode, rest) := match cs with
    | '+' :: r => (1, r)
    | '-' :: r => (2, r)
    | r => (0, r)
  let ip := rest.takeWhile Char.isDigit
  let after := rest.dropWhile Char.isDigit
  let fracOk := match after with
    | [] => true
    | '.' :: f =>
      let fd := f.takeWhile Char.isDigit
      !fd.isEmpty && (match f.dropWhile Char.isDigit with
        | [] => true
        | c :: ex => (c == 'e' || c == 'E') &&
          (let ex := match ex with
            | '+' :: r => r
            | '-' :: r => r
            | r => r
           !ex.isEmpty && ex.all Char.isDigit))
    | c :: ex => (c == 'e' || c == 'E') &&
      (let ex := match ex with
        | '+' :: r => r
        | '-' :: r => r
        | r => r
       !ex.isEmpty && ex.all Char.isDigit)
  if ip.isEmpty || !fracOk then none
  else
    let n := ip.foldl (fun n c => n * 10 + (c.toNat - 48)) 0
    let n := if mode == 1 then n + 3 else if mode == 2 then 3 - n else n
    some (legacySizeToCss (max 1 (min 7 n)))

/-- "Legacy font size for" a size: a number, a keyword or a length. -/
def legacyFontSize (size : String) : Option String :=
  match normalizeFontSize size with
  | some k => (cssSizeToLegacy k).map toString
  | none =>
    if size == "xxx-large" then some "7"
    else (parseFontSize 16000 size).map fun px => toString (legacyOfPx px)

#guard normalizeFontSize "4" == some "large"
#guard normalizeFontSize "+1" == some "large"
#guard normalizeFontSize "-9" == some "x-small"
#guard normalizeFontSize "abc" == none
#guard legacyFontSize "16px" == some "3"
#guard legacyFontSize "x-large" == some "5"

/-- Is the colour value of `backColor`, `foreColor` or `hiliteColor` usable; the value
with a `#` added to bare hexadecimal digits. -/
def colorCommandValue (value : String) : Option String :=
  let cs := value.toList
  let value := if (cs.length == 3 || cs.length == 6) && cs.all (fun c => (hexVal c).isSome) then "#" ++ value else value
  let l := lower value
  let functional := (l.startsWith "rgb(" || l.startsWith "rgba(" || l.startsWith "hsl(" || l.startsWith "hsla(") &&
    l.endsWith ")"
  if functional || (simpleColor value).isSome || l == "transparent" then some value else none

def removeFormatNames : List String :=
  ["abbr", "acronym", "b", "bdi", "bdo", "big", "blink", "cite", "code", "dfn", "em", "font", "i", "ins", "kbd",
   "mark", "nobr", "q", "s", "samp", "small", "span", "strike", "strong", "sub", "sup", "tt", "u", "var"]

/-- The `removeFormat` command. -/
def removeFormat : M Unit := do
  let e ← get
  let cand := fun (e : Ed) (n : NodeId) => isEditable e n && isHtml e.dom n removeFormatNames
  for el in allEffectivelyContained e (activeOf e) (cand e) do
    let d ← rd (·.dom)
    match parentOf d el with
    | some p =>
      for c in kidsOf d el do
        let i ← rd fun e => indexOf e.dom el
        movePreservingRanges c p (some i)
      removeNode el
    | none => pure ()
  splitRangeEnds
  let e ← get
  for node in allEffectivelyContained e (activeOf e) (isEditable e) do
    for _ in [0:e.dom.size + 1] do
      let e ← get
      match parentOf e.dom node with
      | some p => if cand e p && inSameEditingHost e p node then splitParent #[node] else break
      | none => break
  for command in recordedCommands do
    setSelectionValue command none

/-- The `unlink` command. -/
def unlink : M Unit := do
  let e ← get
  let d := e.dom
  let r := activeOf e
  let isLink := fun (n : NodeId) => isHtml d n ["a"] && hasAttr d n "href"
  let mut links : Array NodeId := ((chain d r.start.node).filter isLink)
  let stop := nextNodeDesc d r.stop.node
  let mut cur := some r.start.node
  for _ in [0:d.size + 1] do
    match cur with
    | none => break
    | some c =>
      if some c == stop then break
      if isLink c && (contained d r c || isAncestor d c r.stop.node || c == r.stop.node) then links := links.push c
      cur := nextNode d c
  for l in links do
    let _ ← clearValue l "unlink"

/-- The `createLink` command. -/
def createLink (value : String) : M Unit := do
  let e ← get
  let d := e.dom
  for node in allEffectivelyContained e (activeOf e) fun _ => true do
    for a in ancestors d node do
      if isEditable e a && isHtml d a ["a"] && hasAttr d a "href" then setAttr a "href" value
  setSelectionValue "createlink" (some value)

/-! ## The inline commands as actions, and their state and value with overrides -/

/-- The selection has a range whose boundary points are Text or Element nodes. -/
def hasActive (e : Ed) : Bool :=
  match (e.live.ranges[0]?).join with
  | some r =>
    let ok := fun (n : NodeId) => isText e.dom n || isEl e.dom n
    ok r.start.node && ok r.stop.node
  | none => false

/-- The state of an inline command: its override, else the state of the selection. -/
def inlineQueryState (command : String) : M Bool := do
  match inlineActivatedValues command with
  | none => return false
  | some vals =>
    if !(← rd hasActive) then return false
    if let some v := ← getStateOverride command then return v
    rd fun e => inlineState e command vals

/-- The value of `fontName`, `fontSize`, `foreColor`, `hiliteColor` or `backColor`: its
override, else the value of the selection. -/
def inlineQueryValue (command : String) : M String := do
  if !(← rd hasActive) then return ""
  if let some v := ← getValueOverride command then
    return if command == "fontsize" then (legacyFontSize v).getD "" else v
  rd fun e =>
    if command == "fontsize" then
      let nodes := allEffectivelyContained e (activeOf e) (isFormattableNode e)
      let ref := (nodes[0]?).getD (activeOf e).start.node
      match effectiveCommandValue e ref "fontsize" with
      | some px => (legacyFontSize px).getD ""
      | none => ""
    else standardValue e command

/-- The action of an inline formatting command; `none` when `command` is not one. -/
def inlineAction (command value : String) : M (Option Bool) := do
  match command with
  | "backcolor" | "forecolor" | "hilitecolor" =>
    match colorCommandValue value with
    | some v => setSelectionValue command (some v); return some true
    -- a value that is not a colour changes nothing; browsers (and the WPT expectations)
    -- answer true where the draft answers false
    | none => return some true
  | "bold" =>
    let on ← inlineQueryState "bold"
    setSelectionValue "bold" (some (if on then "normal" else "bold")); return some true
  | "italic" =>
    let on ← inlineQueryState "italic"
    setSelectionValue "italic" (some (if on then "normal" else "italic")); return some true
  | "strikethrough" =>
    let on ← inlineQueryState "strikethrough"
    setSelectionValue "strikethrough" (if on then none else some "line-through"); return some true
  | "underline" =>
    let on ← inlineQueryState "underline"
    setSelectionValue "underline" (if on then none else some "underline"); return some true
  | "subscript" | "superscript" =>
    let on ← inlineQueryState command
    setSelectionValue command none
    if !on then setSelectionValue command (some command)
    return some true
  | "createlink" => if value.isEmpty then return some false else createLink value; return some true
  | "fontname" => setSelectionValue "fontname" (some value); return some true
  | "fontsize" =>
    match normalizeFontSize value with
    | some v => setSelectionValue "fontsize" (some v); return some true
    | none => return some false
  | "removeformat" => removeFormat; return some true
  | "unlink" => unlink; return some true
  | _ => return none

/-! ## Recording and restoring overrides, states and values -/

/-- A recorded override: a state or a value. -/
inductive Ov where
  | state (b : Bool)
  | value (s : String)
  deriving BEq, Repr, Inhabited

def stateCommands : List String := ["bold", "italic", "strikethrough", "subscript", "superscript", "underline"]
def valueCommands : List String := ["fontname", "fontsize", "forecolor", "hilitecolor"]

/-- "Record current overrides". -/
def recordCurrentOverrides : M (List (String × Ov)) := do
  let mut out : List (String × Ov) := []
  if let some v := ← getValueOverride "createlink" then out := out ++ [("createlink", .value v)]
  for c in stateCommands do
    if let some b := ← getStateOverride c then out := out ++ [(c, .state b)]
  for c in valueCommands do
    if let some v := ← getValueOverride c then out := out ++ [(c, .value v)]
  return out

/-- The first formattable node effectively contained in the active range. -/
def firstFormattable (e : Ed) : Option NodeId :=
  (allEffectivelyContained e (activeOf e) (isFormattableNode e))[0]?

/-- "Record current states and values". -/
def recordCurrentStatesAndValues : M (List (String × Ov)) := do
  let e ← get
  let some node := firstFormattable e | return []
  let mut out : List (String × Ov) := []
  if let some v := effectiveCommandValue e node "createlink" then out := out ++ [("createlink", .value v)]
  for c in stateCommands do
    let on := match inlineActivatedValues c, effectiveCommandValue e node c with
      | some vals, some v => vals.contains v
      | _, _ => false
    out := out ++ [(c, .state on)]
  for c in valueCommands do
    out := out ++ [(c, .value (← inlineQueryValue c))]
  if let some v := effectiveCommandValue e node "fontsize" then out := out ++ [("fontsize", .value v)]
  return out

/-- "Restore states and values". -/
def restoreStatesAndValues (overrides : List (String × Ov)) : M Unit := do
  let e ← get
  match firstFormattable e with
  | some node0 =>
    let mut node := node0
    for (command, ov) in overrides do
      match ov with
      | .state b =>
        if (← inlineQueryState command) != b then
          let _ ← inlineAction command ""
        else continue
      | .value v =>
        if command != "createlink" && command != "fontsize" then
          if !equivalentValues command (some (← inlineQueryValue command)) (some v) then
            let _ ← inlineAction command v
          else continue
        else if command == "createlink" then
          let vo ← getValueOverride "createlink"
          let e ← get
          let differs := match vo with
            | some x => x != v
            | none => effectiveCommandValue e node "createlink" != some v
          if differs then
            let _ ← inlineAction "createlink" v
          else continue
        else
          let vo ← getValueOverride "fontsize"
          let e ← get
          let differs := match vo with
            | some x => x != v
            | none => !looselyEquivalentValues command (effectiveCommandValue e node "fontsize") (some v)
          if differs then
            match legacyFontSize v with
            | some l => let _ ← inlineAction "fontsize" l
            | none => pure ()
          else continue
      let e ← get
      node := (firstFormattable e).getD node
  | none =>
    for (command, ov) in overrides do
      match ov with
      | .state b => setStateOverride command b
      | .value v => setValueOverride command v

end L4Factoidal.DOM.Editing
