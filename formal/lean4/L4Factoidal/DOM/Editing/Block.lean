/-
L4Factoidal.DOM.Editing.Block — the block formatting commands of the editing draft.

Specification: W3C Editing APIs draft, "Block formatting commands": the definitions
(indentation element, single-line container), the algorithms (fix disallowed ancestors,
normalize sublists, the selection's list state, alignment value, indent, outdent, toggle
lists, justify the selection), and the commands `formatBlock`, `indent`, `outdent`,
`insertOrderedList`, `insertUnorderedList`, `justifyCenter`, `justifyFull`,
`justifyLeft`, `justifyRight`.

Proved: `alignmentValue_mem` (the alignment value is one of left, right, center,
justify), `containedNodes_contained` is tested, not proved. Tested only (the WPT cases):
the tree algorithms.
-/
import L4Factoidal.DOM.Editing.Inline

namespace L4Factoidal.DOM.Editing
open L4Factoidal.DOM L4Factoidal.DOM.Range

/-! ## Contained nodes -/

/-- The first node a walk over the nodes contained in `r` starts at, and the node it
stops before. -/
def containedWalk (d : Dom) (r : Rng) : Option NodeId × Option NodeId :=
  let sn := r.start.node
  let first :=
    if hasKids d sn && r.start.offset < (kidsOf d sn).size then (kidsOf d sn)[r.start.offset]?
    else if r.start.offset == nodeLength d sn then nextNodeDesc d sn
    else nextNode d sn
  let en := r.stop.node
  let stop :=
    if hasKids d en && r.stop.offset < (kidsOf d en).size then (kidsOf d en)[r.stop.offset]?
    else nextNodeDesc d en
  (first, stop)

/-- The nodes contained in `r` that `cond` accepts, without the descendants of an
accepted node. -/
def containedNodes (d : Dom) (r : Rng) (cond : NodeId → Bool) : Array NodeId := Id.run do
  let (first, stop) := containedWalk d r
  let mut out : Array NodeId := #[]
  let mut cur := first
  for _ in [0:d.size + 1] do
    match cur with
    | none => break
    | some c =>
      if !isBefore d (some c) stop then break
      if contained d r c && cond c then
        out := out.push c
        cur := nextNodeDesc d c
      else cur := nextNode d c
  return out

/-- The nodes contained in `r` that `cond` accepts, descendants included. -/
def allContainedNodes (d : Dom) (r : Rng) (cond : NodeId → Bool) : Array NodeId := Id.run do
  let (first, stop) := containedWalk d r
  let mut out : Array NodeId := #[]
  let mut cur := first
  for _ in [0:d.size + 1] do
    match cur with
    | none => break
    | some c =>
      if !isBefore d (some c) stop then break
      if contained d r c && cond c then out := out.push c
      cur := nextNode d c
  return out

/-! ## Definitions -/

/-- A property name without a vendor prefix (`-moz-margin-start` is `margin-start`). -/
def stripVendor (s : String) : String :=
  match s.toList with
  | '-' :: rest => String.ofList ((rest.dropWhile (· != '-')).drop 1)
  | _ => s

/-- "Indentation element": a `blockquote`, or a `div` with a margin in its style. -/
def isIndentationElement (d : Dom) (n : NodeId) : Bool :=
  isHtml d n ["blockquote"] ||
    (isHtml d n ["div"] && (styleDecls d n).any fun (k, _) => (stripVendor k).startsWith "margin")

/-- "Simple indentation element": an indentation element with no attribute but `style`
and `dir`, and no style but margin, border and padding. -/
def isSimpleIndentationElement (d : Dom) (n : NodeId) : Bool :=
  isIndentationElement d n &&
    (d.get n).attrs.all (fun a => a.ns.isNone && (a.lname == "style" || a.lname == "dir")) &&
    (styleDecls d n).all fun (k, _) =>
      let k := stripVendor k
      k.startsWith "margin" || k.startsWith "border" || k.startsWith "padding"

def isNonListSingleLineContainer (d : Dom) (n : NodeId) : Bool :=
  isHtml d n ["address", "div", "h1", "h2", "h3", "h4", "h5", "h6", "listing", "p", "pre", "xmp"]

def isSingleLineContainer (d : Dom) (n : NodeId) : Bool :=
  isNonListSingleLineContainer d n || isHtml d n ["li", "dt", "dd"]

/-- "Block node of" a node: the nearest inclusive ancestor that is a block node. -/
def blockNodeOf (e : Ed) (n : NodeId) : NodeId :=
  ((chain e.dom n).toList.reverse.find? (isBlockNode e)).getD n

/-- The directionality of an element from the `dir` attributes of its ancestors (HTML
§3.2.6.4, without `auto`). -/
def isRtl (d : Dom) (n : NodeId) : Bool :=
  match (chain d n).toList.reverse.findSome? fun a =>
      match (attr d a "dir").map lower with
      | some "rtl" => some true
      | some "ltr" => some false
      | _ => none with
  | some b => b
  | none => false

/-- "Alignment value" of a node: left, right, center or justify. -/
def alignmentValue (e : Ed) (node : NodeId) : String :=
  let d := e.dom
  match (chain d node).toList.reverse.find? fun a => isEl d a && !(["inline", "none"].contains (displayOf e a)) with
  | none => "left"
  | some el =>
    let v := (styleOf e.env d el).textAlign
    let v := if v.startsWith "-moz-" then (v.drop 5).toString else if v.startsWith "-webkit-" then (v.drop 8).toString else v
    let v := if v == "auto" then "start" else v
    if v == "start" then (if isRtl d el then "right" else "left")
    else if v == "end" then (if isRtl d el then "left" else "right")
    else if v == "center" then "center"
    else if v == "justify" then "justify"
    else if v == "right" then "right"
    else "left"

/-- Alignment. Says: the alignment value of every node is one of the four values the
`justify` commands set. Does not say: which one a given style gives (tested). -/
theorem alignmentValue_mem (e : Ed) (node : NodeId) :
    alignmentValue e node ∈ ["left", "right", "center", "justify"] := by
  unfold alignmentValue
  simp only
  repeat' split
  all_goals simp

/-- The nodes whose alignment the `justify` commands report: editable, visible, without
children, in the block-extended active range. -/
def alignmentNodes (e : Ed) : Array NodeId :=
  allContainedNodes e.dom (blockExtend e (activeOf e)) fun n => isEditable e n && isVisible e n && !hasKids e.dom n

def justifyAlignment (command : String) : Option String :=
  match command with
  | "justifycenter" => some "center"
  | "justifyfull" => some "justify"
  | "justifyleft" => some "left"
  | "justifyright" => some "right"
  | _ => none

def hasDescendant (d : Dom) (n : NodeId) (p : NodeId → Bool) : Bool := (d.treeOrder n false).any p

/-- "The selection's list state": none, ol, ul, mixed, mixed ol or mixed ul. -/
def selectionListState (e : Ed) : String :=
  let d := e.dom
  let r := blockExtend e (activeOf e)
  let nodes := containedNodes d r fun n =>
    isEditable e n && !isIndentationElement d n &&
      (isHtml d n ["ol", "ul"] || isHtmlO d (parentOf d n) ["ol", "ul"] || isAllowedChildOfName e (.node n) "li")
  let inList := fun (tag : String) (n : NodeId) =>
    isHtml d n [tag] || isHtmlO d (parentOf d n) [tag] ||
      (isHtmlO d (parentOf d n) ["li"] && isHtmlO d ((parentOf d n).bind (parentOf d)) [tag])
  let has := fun (tag : String) (n : NodeId) => isHtml d n [tag] || hasDescendant d n (fun m => isHtml d m [tag])
  if nodes.isEmpty then "none"
  else if nodes.all (inList "ol") && !nodes.any (has "ul") then "ol"
  else if nodes.all (inList "ul") && !nodes.any (has "ol") then "ul"
  else
    let hasOl := nodes.any fun n => inList "ol" n || has "ol" n
    let hasUl := nodes.any fun n => inList "ul" n || has "ul" n
    if hasOl && hasUl then "mixed" else if hasOl then "mixed ol" else if hasUl then "mixed ul" else "none"

def formattableBlockNames : List String :=
  ["address", "dd", "div", "dt", "h1", "h2", "h3", "h4", "h5", "h6", "p", "pre"]

/-- The block type `formatBlock` reports for a node: the name of its nearest formattable
block ancestor in its editing host, or "". -/
def formatBlockType (e : Ed) (n : NodeId) : String := Id.run do
  let d := e.dom
  let mut node := n
  for _ in [0:d.size + 1] do
    match parentOf d node with
    | some p =>
      if isEditable e p && inSameEditingHost e node p && !isHtml d node formattableBlockNames then node := p else break
    | none => break
  if isEditable e node && isHtml d node formattableBlockNames &&
      !hasDescendant d node (isProhibitedParagraphChild d) then return (d.get node).lname
  return ""

def formatBlockNodes (e : Ed) : Array NodeId :=
  allContainedNodes e.dom (blockExtend e (activeOf e)) fun n => isVisible e n && isEditable e n && !hasKids e.dom n

/-- The state of a block command (no override applies). -/
def blockState (e : Ed) (command : String) : Bool :=
  match command with
  | "insertorderedlist" => selectionListState e == "ol"
  | "insertunorderedlist" => selectionListState e == "ul"
  | _ =>
    match justifyAlignment command with
    | some a =>
      let nodes := alignmentNodes e
      !nodes.isEmpty && nodes.all fun n => alignmentValue e n == a
    | none => false

def blockIndeterm (e : Ed) (command : String) : Bool :=
  match command with
  | "insertorderedlist" => let s := selectionListState e; s == "mixed" || s == "mixed ol"
  | "insertunorderedlist" => let s := selectionListState e; s == "mixed" || s == "mixed ul"
  | "formatblock" =>
    let types := (formatBlockNodes e).map (formatBlockType e)
    match types[0]? with
    | some t => types.any (· != t)
    | none => false
  | _ =>
    match justifyAlignment command with
    | some a =>
      let nodes := alignmentNodes e
      nodes.any (fun n => alignmentValue e n == a) && nodes.any (fun n => alignmentValue e n != a)
    | none => false

def blockValue (e : Ed) (command : String) : String :=
  match command with
  | "formatblock" =>
    match (formatBlockNodes e)[0]? with
    | some n => formatBlockType e n
    | none => ""
  | _ =>
    match justifyAlignment command with
    | some _ =>
      match (alignmentNodes e)[0]? with
      | some n => alignmentValue e n
      | none => "left"
    | none => ""

/-! ## Algorithms -/

/-- "Fix disallowed ancestors" of a node. `fuel` bounds the one recursion (after the node
becomes a default single-line container). -/
def fixDisallowedAncestors : Nat → NodeId → M Unit
  | 0, _ => pure ()
  | fuel + 1, node => do
    let e ← get
    let d := e.dom
    if !isEditable e node then return
    if (ancestors d node).all fun a => !inSameEditingHost e node a || !isAllowedChild e (.node node) a then
      if isHtml d node ["dd", "dt"] then
        let _ ← wrap #[node] (fun e s => isHtml e.dom s ["dl"] && attrCount e.dom s == 0)
          (do return some (← createElement "dl"))
        return
      match editingHostOf e node with
      | some h => if !isAllowedChild e (.name "p") h then return
      | none => return
      if !isProhibitedParagraphChild d node then return
      let node ← setTagName node e.sep
      fixDisallowedAncestors fuel node
      let e ← get
      for child in (kidsOf e.dom node).filter (isProhibitedParagraphChild e.dom) do
        let e ← get
        let values := recordValues e #[child]
        splitParent #[child]
        restoreValues values
      return
    let values := recordValues e #[node]
    for _ in [0:d.size + 1] do
      let e ← get
      match parentOf e.dom node with
      | some p =>
        if isAllowedChild e (.node node) p then break
        let before := e.log.size
        splitParent #[node]
        if (← rd fun e => e.log.size) == before then break
      | none => break
    restoreValues values

def fixDisallowedAncestorsO (n : Option NodeId) : M Unit := do
  match n with
  | some n => fixDisallowedAncestors ((← rd fun e => e.dom.size) + 1) n
  | none => pure ()

/-- "Normalize sublists" of a list item: its child lists become its next siblings. -/
def normalizeSublists (item : NodeId) : M Unit := do
  let e ← get
  let d := e.dom
  if !isHtml d item ["li"] || !isEditable e item || !isEditableO e (parentOf d item) then return
  let some parent := parentOf d item | return
  let mut newItem : Option NodeId := none
  for _ in [0:d.size + 1] do
    let d ← rd (·.dom)
    if !(kidsOf d item).any (fun c => isHtml d c ["ol", "ul"]) then break
    let some child := lastChild d item | break
    if isHtml d child ["ol", "ul"] ||
        (newItem.isNone && isText d child && (d.get child).data.toList.all isWs) then
      newItem := none
      movePreservingRanges child parent (some (1 + indexOf d item))
    else
      let ni ← match newItem with
        | some ni => pure ni
        | none => do
          let ni ← createElement "li"
          insertBefore parent ni (d.nextSibling item)
          pure ni
      newItem := some ni
      movePreservingRanges child ni (some 0)

/-- "Indent" a list of sibling nodes. -/
def indentNodes (nodeList : Array NodeId) : M Unit := do
  if nodeList.isEmpty then return
  let d ← rd (·.dom)
  let first := nodeList[0]!
  match parentOf d first with
  | some p =>
    if isHtml d p ["ol", "ul"] then
      let tag := (d.get p).lname
      let _ ← wrap nodeList (fun e n => isHtml e.dom n [tag]) (do return some (← createElement tag))
      return
  | none => pure ()
  let np ← wrap nodeList (fun e n => isSimpleIndentationElement e.dom n) (do return some (← createElement "blockquote"))
  fixDisallowedAncestorsO np

/-- "Outdent" a node. `fuel` bounds the recursion on the indentation ancestor. -/
def outdentNode : Nat → NodeId → M Unit
  | 0, _ => pure ()
  | fuel + 1, node => do
    let e ← get
    let d := e.dom
    if !isEditable e node then return
    if isSimpleIndentationElement d node then
      removePreservingDescendants node
      return
    if isIndentationElement d node then
      removeAttr node "dir"
      let ds := (styleDecls d node).filter fun (k, _) =>
        !(k.startsWith "margin" || k.startsWith "padding" || k.startsWith "border")
      if ds.isEmpty then
        if hasAttr d node "style" then removeAttr node "style"
      else setAttr node "style" (serializeDecls ds)
      let _ ← setTagName node "div"
      return
    let walk := fun (stop : NodeId → Bool) => Id.run do
      let mut cur := parentOf d node
      let mut list : Array NodeId := #[]
      for _ in [0:d.size + 1] do
        match cur with
        | some c =>
          if isEditable e c && isEl d c && !stop c && !isHtml d c ["ol", "ul"] then
            list := list.push c
            cur := parentOf d c
          else break
        | none => break
      return (cur, list)
    let (cur1, list1) := walk (isSimpleIndentationElement d)
    let (currentAncestor, ancestorList) :=
      if !(match cur1 with
        | some c => isEditable e c && isSimpleIndentationElement d c
        | none => false) then walk (isIndentationElement d)
      else (cur1, list1)
    let ancestorIsIndent := match currentAncestor with
      | some c => isEditable e c && isIndentationElement d c
      | none => false
    if isHtml d node ["ol", "ul"] && !ancestorIsIndent then
      removeAttr node "reversed"
      removeAttr node "start"
      removeAttr node "type"
      let children := kidsOf d node
      let e ← get
      if attrCount e.dom node > 0 && !isHtmlO e.dom (parentOf e.dom node) ["ol", "ul"] then
        let _ ← setTagName node "div"
      else
        let values := recordValues e children
        removePreservingDescendants node
        restoreValues values
      for c in children do fixDisallowedAncestorsO (some c)
      return
    if !ancestorIsIndent then return
    let some original := currentAncestor | return
    let mut list := ancestorList.push original
    for _ in [0:ancestorList.size + 1] do
      let some cur := list.back? | break
      list := list.pop
      let e ← get
      let d := e.dom
      let target := if parentOf d node == some cur then node else (list.back?).getD node
      if isInlineNode e target && !isHtml d target ["br"] && isHtmlO d (d.nextSibling target) ["br"] then
        match d.nextSibling target with
        | some br => removeNode br
        | none => pure ()
      let d ← rd (·.dom)
      let kids := kidsOf d cur
      let i := indexOf d target
      indentNodes (kids.extract 0 i)
      indentNodes (kids.extract (i + 1) kids.size)
    outdentNode fuel original

/-- The `li` ancestors of the active range's ends that list commands normalize first. -/
def listItemsOfRange (d : Dom) (r : Rng) : Array NodeId := Id.run do
  let common := commonAncestor d r
  let mut items : List NodeId := []
  let mut cur := some r.stop.node
  for _ in [0:d.size + 1] do
    match cur with
    | some c =>
      if c == common then break
      if isHtml d c ["li"] then items := c :: items
      cur := parentOf d c
    | none => break
  cur := some r.start.node
  for _ in [0:d.size + 1] do
    match cur with
    | some c =>
      if isHtml d c ["li"] then items := c :: items
      cur := parentOf d c
    | none => break
  return items.toArray

/-- Take from the front of `nodes` the run that starts at index `i`: `first`, then each
next node while it is the next sibling of the last taken and `more` accepts it. -/
def takeRun (d : Dom) (nodes : Array NodeId) (i : Nat) (more : NodeId → NodeId → Bool) : Array NodeId × Nat := Id.run do
  let mut sub : Array NodeId := #[nodes[i]!]
  let mut j := i + 1
  for _ in [0:nodes.size] do
    match nodes[j]? with
    | some n =>
      if d.nextSibling sub.back! == some n && more sub.back! n then
        sub := sub.push n
        j := j + 1
      else break
    | none => break
  return (sub, j)

/-- "Toggle lists" with tag name `ol` or `ul`. -/
def toggleLists (tagName : String) : M Unit := do
  let e ← get
  let mode := if selectionListState e == tagName then "disable" else "enable"
  let other := if tagName == "ol" then "ul" else "ol"
  let r := activeOf e
  for item in listItemsOfRange e.dom r do normalizeSublists item
  let e ← get
  let newRange := blockExtend e (activeOf e)
  -- the block-extended range is kept live while the tree changes
  let k ← addRange newRange
  if mode == "enable" then
    for list in allContainedNodes e.dom newRange fun n => isEditable e n && isHtml e.dom n [other] do
      let e ← get
      let d := e.dom
      if (isEditableO e (d.previousSibling list) && isHtmlO d (d.previousSibling list) [tagName]) ||
          (isEditableO e (d.nextSibling list) && isHtmlO d (d.nextSibling list) [tagName]) then
        let children := kidsOf d list
        let values := recordValues e children
        splitParent children
        let _ ← wrap children (fun e n => isHtml e.dom n [tagName]) (pure none)
        restoreValues values
      else
        let _ ← setTagName list tagName
  let e ← get
  let d := e.dom
  let newRange ← rangeAt k
  let mut nodeList := containedNodes d newRange fun n =>
    isEditable e n && !isIndentationElement d n &&
      (isHtml d n ["ol", "ul"] || isHtmlO d (parentOf d n) ["ol", "ul"] || isAllowedChildOfName e (.node n) "li")
  dropRanges k
  if mode == "enable" then
    nodeList := nodeList.filter fun n => !isHtml d n ["ol", "ul"] || isHtmlO d (parentOf d n) ["ol", "ul"]
  let fuel := d.size + 1
  if mode == "disable" then
    let mut i := 0
    for _ in [0:nodeList.size] do
      if i ≥ nodeList.size then break
      let d ← rd (·.dom)
      if isHtml d nodeList[i]! [tagName] then
        outdentNode fuel nodeList[i]!
        i := i + 1
        continue
      let (sublist, j) := takeRun d nodeList i fun _ n => !isHtml d n [tagName]
      i := j
      let e ← get
      let values := recordValues e sublist
      splitParent sublist
      for n in sublist do fixDisallowedAncestorsO (some n)
      restoreValues values
  else
    let mut i := 0
    for _ in [0:nodeList.size] do
      if i ≥ nodeList.size then break
      let mut sublist : Array NodeId := #[]
      for _ in [0:nodeList.size] do
        if i ≥ nodeList.size then break
        let d ← rd (·.dom)
        if !sublist.isEmpty && d.nextSibling sublist.back! != some nodeList[i]! then break
        let n := nodeList[i]!
        if isHtml d n ["p", "div"] then
          sublist := sublist.push (← setTagName n "li")
          i := i + 1
        else if isHtml d n ["li", "ol", "ul"] then
          sublist := sublist.push n
          i := i + 1
        else
          let e ← get
          let (nodesToWrap, j) := takeRun d nodeList i fun last n =>
            isInlineNode e n && isInlineNode e last && !isHtml d last ["br"]
          i := j
          match ← wrap nodesToWrap (fun _ _ => false) (do return some (← createElement "li")) with
          | some li => sublist := sublist.push li
          | none => pure ()
      if sublist.isEmpty then continue
      let e ← get
      let d := e.dom
      let p0 := parentOf d sublist[0]!
      if isHtmlO d p0 [tagName] || sublist.all (fun n => isHtml d n ["ol", "ul"]) then continue
      if isHtmlO d p0 [other] then
        let values := recordValues e sublist
        splitParent sublist
        let _ ← wrap sublist (fun e n => isHtml e.dom n [tagName]) (do return some (← createElement tagName))
        restoreValues values
        continue
      let np ← wrap sublist (fun e n => isHtml e.dom n [tagName]) (do
        let e ← get
        let d := e.dom
        let p := parentOf d sublist[0]!
        let prev := p.bind d.previousSibling
        if !isEditableO e p || !(p.map (isSimpleIndentationElement d)).getD false ||
            !isEditableO e prev || !isHtmlO d prev [tagName] then
          return some (← createElement tagName)
        let some list := prev | return none
        match lastChild d list with
        | some lc => normalizeSublists lc
        | none => pure ()
        let e ← get
        let d := e.dom
        if !isEditableO e (lastChild d list) || !isHtmlO d (lastChild d list) [tagName] then
          let nl ← createElement tagName
          appendChild list nl
        return lastChild (← rd (·.dom)) list)
      fixDisallowedAncestorsO np

/-- "Justify the selection" to an alignment. -/
def justifySelection (alignment : String) : M Unit := do
  let e ← get
  let d := e.dom
  let newRange := blockExtend e (activeOf e)
  let elements := allContainedNodes d newRange fun n =>
    isEl d n && isEditable e n && (hasAttr d n "align" || styleGet d n "text-align" != "" || isHtml d n ["center"])
  for el in elements do
    removeAttr el "align"
    if (← rd fun e => styleGet e.dom el "text-align") != "" then styleSet el "text-align" ""
    if (← rd fun e => attr e.dom el "style") == some "" then removeAttr el "style"
    let d ← rd (·.dom)
    if isHtml d el ["div", "span", "center"] && attrCount d el == 0 then removePreservingDescendants el
    let d ← rd (·.dom)
    if isHtml d el ["center"] && attrCount d el > 0 && (parentOf d el).isSome then
      let _ ← setTagName el "div"
  let e ← get
  let d := e.dom
  let newRange := blockExtend e (activeOf e)
  let nodeList := containedNodes d newRange fun n =>
    isEditable e n && isAllowedChildOfName e (.node n) "div" && alignmentValue e n != alignment
  let mut i := 0
  for _ in [0:nodeList.size] do
    if i ≥ nodeList.size then break
    let d ← rd (·.dom)
    let (sublist, j) := takeRun d nodeList i fun _ _ => true
    i := j
    let _ ← wrap sublist
      (fun e n =>
        let d := e.dom
        isHtml d n ["div"] && (d.get n).attrs.all fun a =>
          (a.lname == "align" && lower a.value == alignment) ||
          (a.lname == "style" && styleLength d n == 1 && styleGet d n "text-align" == alignment))
      (do
        let np ← createElement "div"
        setAttr np "style" ("text-align: " ++ alignment)
        return some np)

/-- The `formatBlock` command. -/
def formatBlock (value : String) : M Bool := do
  let value := if value.startsWith "<" && value.endsWith ">" then ((value.drop 1).dropEnd 1).toString else value
  let value := lower value
  if !formattableBlockNames.contains value then return false
  let e ← get
  let d := e.dom
  let newRange := blockExtend e (activeOf e)
  let nodeList := containedNodes d newRange fun n =>
    isEditable e n &&
      (isNonListSingleLineContainer d n || isAllowedChildOfName e (.node n) "p" || isHtml d n ["dd", "dt"]) &&
      !hasDescendant d n (isProhibitedParagraphChild d)
  let values := recordValues e nodeList
  for node in nodeList do
    for _ in [0:d.size + 1] do
      let e ← get
      let d := e.dom
      if (ancestors d node).any fun a =>
          isEditable e a && inSameEditingHost e a node && isHtml d a formattableBlockNames &&
            !hasDescendant d a (isProhibitedParagraphChild d) then
        let before := e.log.size
        splitParent #[node]
        if (← rd fun e => e.log.size) == before then break
      else break
  restoreValues values
  let mut i := 0
  for _ in [0:nodeList.size] do
    if i ≥ nodeList.size then break
    let e ← get
    let d := e.dom
    let mut sublist : Array NodeId := #[]
    if isSingleLineContainer d nodeList[i]! then
      sublist := kidsOf d nodeList[i]!
      let values := recordValues e sublist
      removePreservingDescendants nodeList[i]!
      restoreValues values
      i := i + 1
    else
      let (sub, j) := takeRun d nodeList i fun last n => !isSingleLineContainer d n && !isHtml d last ["br"]
      sublist := sub
      i := j
    let np ← wrap sublist
      (if value == "div" || value == "p" then fun _ _ => false
       else fun e n => isHtml e.dom n [value] && attrCount e.dom n == 0)
      (do return some (← createElement value))
    fixDisallowedAncestorsO np
  return true

/-- The `indent` command. -/
def indent : M Unit := do
  let e ← get
  let d := e.dom
  let r := activeOf e
  let common := commonAncestor d r
  let upTo := fun (start : NodeId) => Id.run do
    let mut out : List NodeId := []
    let mut cur := some start
    for _ in [0:d.size + 1] do
      match cur with
      | some c =>
        if c == common then break
        if isHtml d c ["li"] then out := c :: out
        cur := parentOf d c
      | none => break
    return out
  let items := ((chain d common).toList.filter fun c => isHtml d c ["li"]) ++ upTo r.start.node ++ upTo r.stop.node
  for item in items do normalizeSublists item
  let e ← get
  let d := e.dom
  let newRange := blockExtend e (activeOf e)
  let nodeList := containedNodes d newRange fun n =>
    isEditable e n && (isAllowedChildOfName e (.node n) "div" || isAllowedChildOfName e (.node n) "ol")
  if let some fv := (nodeList.filter (isVisible e))[0]? then
    if isHtml d fv ["li"] && isHtmlO d (parentOf d fv) ["ol", "ul"] then
      let mut sibling := d.previousSibling fv
      for _ in [0:d.size + 1] do
        match sibling with
        | some s => if isInvisible e s then sibling := d.previousSibling s else break
        | none => break
      if isHtmlO d sibling ["li"] then
        match sibling with
        | some s => normalizeSublists s
        | none => pure ()
  let mut i := 0
  for _ in [0:nodeList.size] do
    if i ≥ nodeList.size then break
    let d ← rd (·.dom)
    let (sublist, j) := takeRun d nodeList i fun _ _ => true
    i := j
    indentNodes sublist

/-- The `outdent` command. -/
def outdent : M Unit := do
  let e ← get
  for item in listItemsOfRange e.dom (activeOf e) do normalizeSublists item
  let e ← get
  let d := e.dom
  let newRange := blockExtend e (activeOf e)
  let nodeList := containedNodes d newRange fun n =>
    isEditable e n &&
      (!hasDescendant d n (isEditable e) || isHtml d n ["ol", "ul"] ||
        (isHtml d n ["li"] && isHtmlO d (parentOf d n) ["ol", "ul"]))
  let fuel := d.size + 1
  let mut i := 0
  for _ in [0:nodeList.size] do
    if i ≥ nodeList.size then break
    let d ← rd (·.dom)
    let n := nodeList[i]!
    if isHtml d n ["ol", "ul"] || !isHtmlO d (parentOf d n) ["ol", "ul"] then
      outdentNode fuel n
      i := i + 1
      continue
    let (sublist, j) := takeRun d nodeList i fun _ m => !isHtml d m ["ol", "ul"]
    i := j
    let e ← get
    let values := recordValues e sublist
    splitParent sublist
    for m in sublist do fixDisallowedAncestorsO (some m)
    restoreValues values

/-- Run an action that "preserves overrides": the overrides recorded before it are
restored when the active range is collapsed after it. -/
def preservingOverrides (act : M Bool) : M Bool := do
  let overrides ← recordCurrentOverrides
  let r ← act
  if (← getActive).collapsed then restoreStatesAndValues overrides
  return r

/-- The action of a block formatting command; `none` when `command` is not one. -/
def blockAction (command value : String) : M (Option Bool) := do
  match command with
  | "formatblock" => return some (← preservingOverrides (formatBlock value))
  | "indent" => return some (← preservingOverrides (do indent; return true))
  | "outdent" => return some (← preservingOverrides (do outdent; return true))
  | "insertorderedlist" => return some (← preservingOverrides (do toggleLists "ol"; return true))
  | "insertunorderedlist" => return some (← preservingOverrides (do toggleLists "ul"; return true))
  | _ =>
    match justifyAlignment command with
    | some a => return some (← preservingOverrides (do justifySelection a; return true))
    | none => return none

def blockCommands : List String :=
  ["formatblock", "indent", "outdent", "insertorderedlist", "insertunorderedlist", "justifycenter",
   "justifyfull", "justifyleft", "justifyright"]

end L4Factoidal.DOM.Editing
