/-
L4Factoidal.DOM.Editing.Delete — deleting the selection, and the commands that insert.

Specification: W3C Editing APIs draft: "Canonical space sequences", "canonicalize
whitespace", "Deleting the selection", the equivalent points of a boundary point,
"Automatic linking", and the commands `delete`, `forwardDelete`, `insertHorizontalRule`,
`insertHTML`, `insertImage`, `insertLineBreak`, `insertParagraph`, `insertText`. The Range
algorithms "insert" and "extract" (DOM §5.5) are here as functions of the editing state.

Proved: `canonicalSpaceSequence_length` (the sequence for `n` spaces has `n` characters),
`canonicalSpaceSequence_chars` (only U+0020 and U+00A0) and `canonicalSpaceSequence_no_pair`
(no two U+0020 are adjacent).
Tested only (the WPT cases): the tree algorithms.
-/
import L4Factoidal.DOM.Editing.Block

namespace L4Factoidal.DOM.Editing
open L4Factoidal.DOM L4Factoidal.DOM.Range

/-! ## Canonical space sequences -/

def nbsp : Char := Char.ofNat 0xa0

/-- The character at index `i` of a canonical space sequence of length `n`. -/
def spaceAt (n : Nat) (nbStart nbEnd : Bool) (i : Nat) : Char :=
  if n == 1 then (if !nbStart && !nbEnd then ' ' else nbsp)
  else if i % 2 == 0 || (nbEnd && i + 1 == n) then nbsp else ' '

/-- "Canonical space sequence" of length `n`: spaces and no-break spaces that render as
`n` spaces. One space is U+0020, unless it is at a line start (`nbStart`) or a line end
(`nbEnd`), where it would collapse. A longer run alternates, U+00A0 first, and ends with
U+00A0 at a line end. This is the sequence Blink and WebKit write
(`editing/whitespaces/chrome-compat`); the draft's sequence starts with U+0020 when it is
not at a line start. Both render the same. -/
def canonicalSpaceSequence (n : Nat) (nbStart nbEnd : Bool) : List Char :=
  (List.range n).map (spaceAt n nbStart nbEnd)

/-- Length. Says: the canonical space sequence for `n` has exactly `n` characters, so
replacing a run of `n` spaces by it keeps every offset after the run. Does not say: that
the sequence renders as `n` spaces in every font (it does by CSS white-space rules when no
two U+0020 are adjacent and none is at a collapsing edge: `canonicalSpaceSequence_no_pair`
and the `#guard` below). -/
theorem canonicalSpaceSequence_length (n : Nat) (nbStart nbEnd : Bool) :
    (canonicalSpaceSequence n nbStart nbEnd).length = n := by
  simp [canonicalSpaceSequence]

def isSpaceOrNbsp (c : Char) : Bool := c == ' ' || c == nbsp

theorem spaceAt_chars (n : Nat) (nbStart nbEnd : Bool) (i : Nat) : isSpaceOrNbsp (spaceAt n nbStart nbEnd i) = true := by
  unfold spaceAt
  repeat' split
  all_goals decide

/-- Characters. Says: the canonical space sequence holds only U+0020 and U+00A0. Does
not say: where each one is (`canonicalSpaceSequence_no_pair`, and the `#guard` below). -/
theorem canonicalSpaceSequence_chars (n : Nat) (nbStart nbEnd : Bool) :
    (canonicalSpaceSequence n nbStart nbEnd).all isSpaceOrNbsp = true := by
  simp [canonicalSpaceSequence, List.all_map, spaceAt_chars]

/-- No collapse. Says: in a sequence of two or more, of two adjacent positions one holds
U+00A0, so no two U+0020 are adjacent and the run can not collapse. Does not say: anything
about the characters next to the run in the text. -/
theorem canonicalSpaceSequence_no_pair (n : Nat) (nbStart nbEnd : Bool) (i : Nat) (h : 2 ≤ n) :
    spaceAt n nbStart nbEnd i = nbsp ∨ spaceAt n nbStart nbEnd (i + 1) = nbsp := by
  have h1 : (n == 1) = false := by simp; omega
  unfold spaceAt
  simp only [h1, Bool.false_eq_true, if_false]
  by_cases he : i % 2 = 0
  · left; simp [he]
  · right
    have : (i + 1) % 2 = 0 := by omega
    simp [this]

#guard canonicalSpaceSequence 1 false false == [' ']
#guard canonicalSpaceSequence 1 true false == [nbsp]
#guard canonicalSpaceSequence 2 false false == [nbsp, ' ']
#guard canonicalSpaceSequence 3 false false == [nbsp, ' ', nbsp]
#guard canonicalSpaceSequence 4 false true == [nbsp, ' ', nbsp, nbsp]
#guard canonicalSpaceSequence 5 true true == [nbsp, ' ', nbsp, ' ', nbsp]
-- no U+0020 at a non-breaking edge, for the first lengths
#guard (List.range 12).all fun n => [false, true].all fun a => [false, true].all fun b =>
  let s := canonicalSpaceSequence n a b
  (!a || s.head? != some ' ') && (!b || s.getLast? != some ' ')

/-! ## Characters of a Text node at UTF-16 offsets -/

/-- The character that starts at UTF-16 offset `o` of the data of `n`. -/
def charAt (d : Dom) (n : NodeId) (o : Nat) : Option Char :=
  (splitAtUnits (d.get n).data o).2.toList.head?

def isSpaceChar (c : Option Char) : Bool := c == some ' ' || c == some nbsp

def preserves (e : Ed) (textNode : NodeId) : Bool :=
  match parentOf e.dom textNode with
  | some p => ["pre", "pre-wrap"].contains (whiteSpaceOf e p)
  | none => false

def sameHostO (e : Ed) (a : NodeId) (b : Option NodeId) : Bool :=
  match b with
  | some b => inSameEditingHost e a b
  | none => false

/-! ## Equivalent points -/

def nextEquivalentPoint (e : Ed) (bp : BP) : Option BP :=
  let d := e.dom
  if nodeLength d bp.node == 0 then none
  else if bp.offset == nodeLength d bp.node && (parentOf d bp.node).isSome && isInlineNode e bp.node then
    (parentOf d bp.node).map fun p => ⟨p, 1 + indexOf d bp.node⟩
  else match (kidsOf d bp.node)[bp.offset]? with
    | some c => if nodeLength d c != 0 && isInlineNode e c then some ⟨c, 0⟩ else none
    | none => none

def previousEquivalentPoint (e : Ed) (bp : BP) : Option BP :=
  let d := e.dom
  if nodeLength d bp.node == 0 then none
  else if bp.offset == 0 && (parentOf d bp.node).isSome && isInlineNode e bp.node then
    (parentOf d bp.node).map fun p => ⟨p, indexOf d bp.node⟩
  else if bp.offset ≥ 1 then
    match (kidsOf d bp.node)[bp.offset - 1]? with
    | some c => if nodeLength d c != 0 && isInlineNode e c then some ⟨c, nodeLength d c⟩ else none
    | none => none
  else none

def firstEquivalentPoint (e : Ed) (bp : BP) : BP := Id.run do
  let mut cur := bp
  for _ in [0:2 * e.dom.size + 2] do
    match previousEquivalentPoint e cur with
    | some p => cur := p
    | none => break
  return cur

def lastEquivalentPoint (e : Ed) (bp : BP) : BP := Id.run do
  let mut cur := bp
  for _ in [0:2 * e.dom.size + 2] do
    match nextEquivalentPoint e cur with
    | some p => cur := p
    | none => break
  return cur

/-! ## Canonicalize whitespace -/

/-- "Canonicalize whitespace" at a boundary point: the run of spaces around it becomes a
canonical space sequence; with `fix`, spaces that would collapse are removed. -/
def canonicalizeWhitespace (node : NodeId) (offset : Nat) (fix : Bool := true) : M Unit := do
  let e ← get
  let d := e.dom
  if !isEditable e node && !isEditingHost e node then return
  let bound := 4 * d.size + 4 * (nodeLength d node) + 4096
  let mut sn := node
  let mut so := offset
  for _ in [0:bound] do
    let prevKid := if so ≥ 1 then (kidsOf d sn)[so - 1]? else none
    if sameHostO e sn prevKid then
      sn := prevKid.getD sn
      so := nodeLength d sn
    else if so == 0 && !followsLineBreak e sn && sameHostO e sn (parentOf d sn) then
      so := indexOf d sn
      sn := (parentOf d sn).getD sn
    else if isText d sn && !preserves e sn && so != 0 && isSpaceChar (charAt d sn (so - 1)) then
      so := so - 1
    else break
  let mut en := sn
  let mut eo := so
  let mut length := 0
  let mut collapseSpaces := so == 0 && followsLineBreak e sn
  for _ in [0:bound] do
    let e ← get
    let d := e.dom
    let kid := (kidsOf d en)[eo]?
    if sameHostO e en kid then
      en := kid.getD en
      eo := 0
    else if eo == nodeLength d en && !precedesLineBreak e en && sameHostO e en (parentOf d en) then
      eo := 1 + indexOf d en
      en := (parentOf d en).getD en
    else if isText d en && !preserves e en && eo != nodeLength d en && isSpaceChar (charAt d en eo) then
      if fix && collapseSpaces && charAt d en eo == some ' ' then
        replaceData en eo 1 ""
        continue
      collapseSpaces := charAt d en eo == some ' '
      eo := eo + 1
      length := length + 1
    else break
  if fix then
    for _ in [0:bound] do
      let e ← get
      let d := e.dom
      if position d ⟨sn, so⟩ ⟨en, eo⟩ != .before then break
      let prevKid := if eo ≥ 1 then (kidsOf d en)[eo - 1]? else none
      if sameHostO e en prevKid then
        en := prevKid.getD en
        eo := nodeLength d en
      else if eo == 0 && sameHostO e en (parentOf d en) then
        eo := indexOf d en
        en := (parentOf d en).getD en
      else if isText d en && !preserves e en && eo == nodeLength d en && eo ≥ 1 &&
          charAt d en (eo - 1) == some ' ' && precedesLineBreak e en then
        eo := eo - 1
        length := length - 1
        replaceData en eo 1 ""
      else break
  let e ← get
  let d := e.dom
  let mut replacement := canonicalSpaceSequence length (so == 0 && followsLineBreak e sn)
    (eo == nodeLength d en && precedesLineBreak e en)
  for _ in [0:bound] do
    let d ← rd (·.dom)
    if position d ⟨sn, so⟩ ⟨en, eo⟩ != .before then break
    if so < (kidsOf d sn).size then
      sn := (kidsOf d sn)[so]!
      so := 0
    else if !isText d sn || so == nodeLength d sn then
      match parentOf d sn with
      | some p => so := 1 + indexOf d sn; sn := p
      | none => break
    else
      match replacement with
      | c :: rest =>
        replacement := rest
        if charAt d sn so != some c then
          -- insert the character, then delete the one after it: a boundary point between stays
          replaceData sn so 0 (String.singleton c)
          replaceData sn (so + 1) 1 ""
        so := so + 1
      | [] => break

/-! ## Range algorithms on the editing state (DOM §5.5) -/

/-- "Insert" a node into the active range (`Range.insertNode`). -/
def rangeInsertNode (node : NodeId) : M Unit := do
  let e ← get
  let d := e.dom
  let r := activeOf e
  let sn := r.start.node
  let x := d.get sn
  if x.type == .pi || x.type == .comment || (Dom.isTextNode x && x.parent.isNone) || sn == node then return
  let refNode := if Dom.isTextNode x then some sn else x.kids[r.start.offset]?
  let parent := match refNode with
    | none => sn
    | some k => ((d.get k).parent).getD sn
  let mut ref := refNode
  if Dom.isTextNode x then
    let nn ← splitText sn r.start.offset
    ref := if nn == sn then refNode else some nn
  if ref == some node then ref := (← rd (·.dom)).nextSibling node
  if ((← rd (·.dom)).get node).parent.isSome then removeNode node
  let d ← rd (·.dom)
  let newOffset := (match ref with
    | none => nodeLength d parent
    | some k => indexOf d k) + (if (d.get node).type == .fragment then nodeLength d node else 1)
  insertBefore parent node ref
  let r ← getActive
  if r.collapsed then setActive { r with stop := ⟨parent, newOffset⟩ }

/-- Set the data of a CharacterData node. -/
def setData (n : NodeId) (data : String) : M Unit := do
  let len ← rd fun e => nodeLength e.dom n
  replaceData n 0 len data

/-- "Extract" a range (DOM §5.5): the fragment. `fuel` bounds the recursion by the
tree's depth. The caller sets any range of its own. -/
def extractRange : Nat → Rng → M NodeId
  | 0, _ => createFragment
  | fuel + 1, r => do
    let frag ← createFragment
    if r.collapsed then return frag
    let d ← rd (·.dom)
    let (sn, so, en, eo) := (r.start.node, r.start.offset, r.stop.node, r.stop.offset)
    if sn == en && Dom.isCharacterData (d.get sn) then
      let c ← cloneNode sn false
      setData c (substringUnits (d.get sn).data so (eo - so))
      appendChild frag c
      replaceData sn so (eo - so) ""
      return frag
    let kids := kidsOf d (commonAncestor d r)
    let first := if d.isInclusiveAncestor sn en then none else kids.find? (partiallyContained d r ·)
    let last := if d.isInclusiveAncestor en sn then none else kids.reverse.find? (partiallyContained d r ·)
    let inside := kids.filter (contained d r ·)
    if let some f := first then
      if Dom.isCharacterData (d.get f) then
        let len := nodeLength d sn
        let c ← cloneNode sn false
        setData c (substringUnits (d.get sn).data so (len - so))
        appendChild frag c
        replaceData sn so (len - so) ""
      else
        let c ← cloneNode f false
        appendChild frag c
        let sub ← extractRange fuel ⟨⟨sn, so⟩, ⟨f, nodeLength d f⟩⟩
        appendChild c sub
    for k in inside do appendChild frag k
    if let some l := last then
      let d ← rd (·.dom)
      if Dom.isCharacterData (d.get l) then
        let c ← cloneNode en false
        setData c (substringUnits (d.get en).data 0 eo)
        appendChild frag c
        replaceData en 0 eo ""
      else
        let c ← cloneNode l false
        appendChild frag c
        let sub ← extractRange fuel ⟨⟨l, 0⟩, ⟨en, eo⟩⟩
        appendChild c sub
    return frag

/-! ## Deleting the selection -/

/-- The block of a boundary node for block merging: its nearest block ancestor in the
editing host, when `span` may be its child and it is not a table cell. -/
def mergeBlockOf (e : Ed) (n : NodeId) : Option NodeId := Id.run do
  let d := e.dom
  let mut b := n
  for _ in [0:d.size + 1] do
    match parentOf d b with
    | some p => if inSameEditingHost e b p && isInlineNode e b then b := p else break
    | none => break
  if (!isBlockNode e b && !isEditingHost e b) || !isAllowedChild e (.name "span") b || isHtml d b ["td", "th"] then
    return none
  return some b

def collapseActive (toStart : Bool) : M Unit := do
  let r ← getActive
  if toStart then setActive ⟨r.start, r.start⟩ else setActive ⟨r.stop, r.stop⟩

/-- Where the line that starts at child `from_` of block `eb` ends: before a `br`
(`some br`), before a block node, at a line feed in a Text node whose white-space keeps
line feeds (the node, with `true`), or at the end of the block. -/
def lineEndFrom (e : Ed) (eb : NodeId) (from_ : Nat) : BP × Option NodeId × Bool := Id.run do
  let d := e.dom
  let keepsFeeds := fun (n : NodeId) => match parentOf d n with
    | some p => ["pre", "pre-wrap", "pre-line", "break-spaces"].contains (whiteSpaceOf e p)
    | none => false
  for top in (kidsOf d eb).extract from_ (kidsOf d eb).size do
    for n in d.treeOrder top true do
      if isHtml d n ["br"] then
        return (⟨(parentOf d n).getD eb, indexOf d n⟩, some n, false)
      if isEl d n && isBlockNode e n then
        return (⟨(parentOf d n).getD eb, indexOf d n⟩, none, false)
      if isText d n && keepsFeeds n then
        let (pre, post) := ((d.get n).data.toList.span (· != '\n'))
        if !post.isEmpty then return (⟨n, utf16Length (String.ofList pre)⟩, some n, true)
  return (⟨eb, nodeLength d eb⟩, none, false)

/-- Move the line that starts at child `from_` of block `eb` into `dest` (before its child
`before`, else at its end), inside a `span` with the white-space `ws` of `eb`; the line
break that ended the line is removed, and so is what the move left empty in `eb`. -/
def moveFirstLine (dest : NodeId) (before : Option NodeId) (eb : NodeId) (from_ : Nat) (ws : String) : M Unit := do
  let e ← get
  let d := e.dom
  let (stop, breaker, isFeed) := lineEndFrom e eb from_
  let frag ← extractRange (d.size + 1) ⟨⟨eb, from_⟩, stop⟩
  let d ← rd (·.dom)
  if hasKids d frag then
    let span ← createElement "span"
    setAttr span "style" ("white-space: " ++ ws)
    appendChild span frag
    insertBefore dest span before
  match breaker with
  | some b => if isFeed then replaceData b 0 1 "" else removeNode b
  | none => pure ()
  -- what the move left empty where the line was
  for _ in [0:d.size + 1] do
    let e ← get
    let d := e.dom
    match (kidsOf d eb)[from_]? with
    | some c =>
      let empty := (d.treeOrder c true).all fun m =>
        (isText d m && (d.get m).data.isEmpty) || (isEl d m && isInlineNode e m && !isHtml d m ["br", "img"])
      if empty && isEditable e c then removeNode c else break
    | none => break

/-- "Delete the selection". -/
def deleteSelection (blockMerging : Bool := true) (stripWrappers : Bool := true) (backward : Bool := false) : M Unit := do
  if !(← rd hasActive) then return
  let r ← getActive
  modify fun e => if e.target.isNone then { e with target := some r } else e
  canonicalizeWhitespace r.start.node r.start.offset
  let r ← getActive
  canonicalizeWhitespace r.stop.node r.stop.offset
  let e ← get
  let d := e.dom
  let r := activeOf e
  let start := lastEquivalentPoint e r.start
  let stop := firstEquivalentPoint e r.stop
  let mut sn := start.node
  let mut so := start.offset
  let mut en := stop.node
  let mut eo := stop.offset
  if position d ⟨en, eo⟩ ⟨sn, so⟩ != .after then
    collapseActive (!backward)
    return
  if isText d sn && so == 0 then
    match parentOf d sn with
    | some p => so := indexOf d sn; sn := p
    | none => pure ()
  if isText d en && eo == nodeLength d en then
    match parentOf d en with
    | some p => eo := 1 + indexOf d en; en := p
    | none => pure ()
  setActive ⟨⟨sn, so⟩, ⟨en, eo⟩⟩
  let startBlock := mergeBlockOf e sn
  let endBlock := mergeBlockOf e en
  let overrides ← recordCurrentStatesAndValues
  let e ← get
  let d := e.dom
  if sn == en && isEditable e sn && isText d sn then
    replaceData sn so (eo - so) ""
    canonicalizeWhitespace sn so false
    collapseActive (!backward)
    restoreStatesAndValues overrides
    return
  if isEditable e sn && isText d sn then replaceData sn so (nodeLength d sn - so) ""
  let e ← get
  let nodeList := containedNodes e.dom (activeOf e) fun n =>
    isEditable e n && !isHtml e.dom n ["thead", "tbody", "tfoot", "tr", "th", "td"]
  for node in nodeList do
    let d ← rd (·.dom)
    let some parent := parentOf d node | continue
    removeNode node
    -- The inline wrappers the removal emptied go first, then the `br` that keeps the block
    -- open goes into the parent that is left: browsers (and the WPT expectations) leave
    -- `<p><br></p>`, not `<p><b><br></b></p>`. The draft's order is the other way round.
    let mut p := parent
    let d ← rd (·.dom)
    if stripWrappers || (!isAncestor d parent sn && parent != sn) then
      for _ in [0:d.size + 1] do
        let e ← get
        let d := e.dom
        if isEditable e p && isInlineNode e p && nodeLength d p == 0 then
          match parentOf d p with
          | some g => removeNode p; p := g
          | none => break
        else break
    let e ← get
    let d := e.dom
    if !(kidsOf d (blockNodeOf e p)).any (isVisible e) && (isEditable e p || isEditingHost e p) then
      let br ← createElement "br"
      appendChild p br
  let e ← get
  if isEditable e en && isText e.dom en then replaceData en 0 eo ""
  let r ← getActive
  canonicalizeWhitespace r.start.node r.start.offset false
  let r ← getActive
  canonicalizeWhitespace r.stop.node r.stop.offset false
  let e ← get
  let (some sb, some eb) := (startBlock, endBlock)
    | do collapseActive (!backward); restoreStatesAndValues overrides
  if !blockMerging || !inSameEditingHost e sb eb || sb == eb then
    collapseActive (!backward)
    restoreStatesAndValues overrides
    return
  let d := e.dom
  let elKids := (kidsOf d sb).filter (isEl d)
  if elKids.size == 1 then
    if let some fc := firstChild d sb then
      if isCollapsedBlockProp e fc then removeNode fc
  let e ← get
  let d := e.dom
  let mut values : Array (NodeId × String × Option String) := #[]
  let mut ebCur := eb
  if isAncestor d sb eb then
    let mut ref := eb
    for _ in [0:d.size + 1] do
      match parentOf d ref with
      | some p => if p == sb then break else ref := p
      | none => break
    let bp : BP := ⟨sb, indexOf d ref⟩
    setActive ⟨bp, bp⟩
    if !hasKids d eb then
      for _ in [0:d.size + 1] do
        let e ← get
        let d := e.dom
        match parentOf d ebCur with
        | some p =>
          if isEditable e ebCur && (kidsOf d p).size == 1 && p != sb then
            removeNode ebCur
            ebCur := p
          else break
        | none => break
      let e ← get
      let d := e.dom
      if isEditable e ebCur && !isInlineNode e ebCur && isInlineNodeO e (d.previousSibling ebCur) &&
          isInlineNodeO e (d.nextSibling ebCur) then
        let br ← createElement "br"
        match parentOf d ebCur with
        | some p => insertBefore p br (d.nextSibling ebCur)
        | none => pure ()
      if (← rd fun e => isEditable e ebCur) then removeNode ebCur
      restoreStatesAndValues overrides
      return
    if !isInlineNodeO e (firstChild d eb) then
      restoreStatesAndValues overrides
      return
    if whiteSpaceOf e sb != whiteSpaceOf e eb then
      -- a block inside the start block, with another white-space: its first line leaves it
      -- in a span that keeps its white-space (browsers)
      moveFirstLine sb (some ref) eb 0 (whiteSpaceOf e eb)
      for _ in [0:d.size + 1] do
        let e ← get
        let d := e.dom
        if hasKids d ebCur || ebCur == sb || !isEditable e ebCur then break
        match parentOf d ebCur with
        | some p => removeNode ebCur; ebCur := p
        | none => break
      let d ← rd (·.dom)
      if !hasKids d sb then
        let br ← createElement "br"
        appendChild sb br
      removeExtraneousLineBreaksAtTheEndOf sb
      restoreStatesAndValues overrides
      return
    let mut children : Array NodeId := #[(firstChild d eb).getD eb]
    for _ in [0:d.size + 1] do
      if !isHtml d children.back! ["br"] && isInlineNodeO e (d.nextSibling children.back!) then
        children := children.push ((d.nextSibling children.back!).getD eb)
      else break
    values := recordValues e children
    for _ in [0:d.size + 1] do
      let e ← get
      if parentOf e.dom children[0]! == some sb then break
      let before := e.log.size
      splitParent children
      if (← rd fun e => e.log.size) == before then break
    let e ← get
    let d := e.dom
    if isEditableO e (d.previousSibling children[0]!) && isHtmlO d (d.previousSibling children[0]!) ["br"] then
      match d.previousSibling children[0]! with
      | some br => removeNode br
      | none => pure ()
  else if isAncestor d eb sb then
    let bp : BP := ⟨sb, nodeLength d sb⟩
    setActive ⟨bp, bp⟩
    let mut ref := sb
    for _ in [0:d.size + 1] do
      match parentOf d ref with
      | some p => if p == eb then break else ref := p
      | none => break
    if isInlineNodeO e (d.nextSibling ref) && isHtmlO d (lastChild d sb) ["br"] then
      match lastChild d sb with
      | some br => removeNode br
      | none => pure ()
    let e ← get
    let d := e.dom
    if whiteSpaceOf e sb != whiteSpaceOf e eb then
      -- the line after the start block, with another white-space, joins it in a span
      moveFirstLine sb none eb (indexOf d ref + 1) (whiteSpaceOf e eb)
      let d ← rd (·.dom)
      if !hasKids d sb then
        let br ← createElement "br"
        appendChild sb br
      removeExtraneousLineBreaksAtTheEndOf sb
      restoreStatesAndValues overrides
      return
    let mut nodesToMove : Array NodeId := #[]
    if let some ns := d.nextSibling ref then
      if !isBlockNode e ns then nodesToMove := nodesToMove.push ns
    if let some l := nodesToMove.back? then
      if !isHtml d l ["br"] then
        if let some ns := d.nextSibling l then
          if !isBlockNode e ns then nodesToMove := nodesToMove.push ns
    values := recordValues e nodesToMove
    for n in nodesToMove do movePreservingRanges n sb none
  else
    let bp : BP := ⟨sb, nodeLength d sb⟩
    setActive ⟨bp, bp⟩
    if isInlineNodeO e (firstChild d eb) && isHtmlO d (lastChild d sb) ["br"] then
      match lastChild d sb with
      | some br => removeNode br
      | none => pure ()
    let e ← get
    let d := e.dom
    if whiteSpaceOf e sb != whiteSpaceOf e eb then
      -- blocks with different white-space: only the first line of the end block joins the
      -- start block, in a span that keeps its white-space (browsers; the draft moves all)
      moveFirstLine sb none eb 0 (whiteSpaceOf e eb)
    else
      values := recordValues e (kidsOf d eb)
      for c in kidsOf d eb do movePreservingRanges c sb none
    for _ in [0:d.size + 1] do
      let d ← rd (·.dom)
      if hasKids d ebCur then break
      match parentOf d ebCur with
      | some p =>
        let before ← rd fun e => e.log.size
        removeNode ebCur
        if (← rd fun e => e.log.size) == before then break
        ebCur := p
      | none => break
  -- merge a list with the list of the same kind that now follows it
  let mut ancestor := sb
  for _ in [0:d.size + 1] do
    let e ← get
    let d := e.dom
    let mergeable := fun (n : NodeId) =>
      inSameEditingHost e ancestor n &&
        ((isHtml d n ["ol"] && isHtmlO d (d.nextSibling n) ["ol"]) || (isHtml d n ["ul"] && isHtmlO d (d.nextSibling n) ["ul"])) &&
        sameHostO e ancestor (d.nextSibling n)
    match (chain d ancestor).toList.reverse.find? mergeable with
    | none => break
    | some a =>
      ancestor := a
      match d.nextSibling a with
      | some ns =>
        for c in kidsOf d ns do movePreservingRanges c a none
        removeNode ns
      | none => break
  restoreValues values
  let d ← rd (·.dom)
  if !hasKids d sb then
    let br ← createElement "br"
    appendChild sb br
  removeExtraneousLineBreaksAtTheEndOf sb
  restoreStatesAndValues overrides

/-! ## Automatic linking -/

def isUrlSchemeChar (c : Char) : Bool := c.isAlphanum || c == '+' || c == '.' || c == '-'
def urlEndExcluded : List Char := ['!', '"', '\'', '(', ')', ',', '-', '.', ':', ';', '<', '>', '[', ']', '`', '{', '}']

/-- Does `cs` match the autolinkable URL pattern in full: a scheme and `://`, or
`mailto:`, then characters with no whitespace, the last not punctuation. -/
def matchesUrl (cs : List Char) : Bool :=
  let rest : Option (List Char) :=
    if (String.ofList (cs.take 7)) == "mailto:" then some (cs.drop 7)
    else match cs with
      | c :: tl =>
        if c.isAlpha then
          let after := tl.dropWhile isUrlSchemeChar
          if String.ofList (after.take 3) == "://" then some (after.drop 3) else none
        else none
      | [] => none
  match rest with
  | some r =>
    !r.isEmpty && r.all (fun c => !isWs c) && (match r.getLast? with
      | some l => !urlEndExcluded.contains l
      | none => false)
  | none => false

def isEmailLocalChar (c : Char) : Bool :=
  c.isAlphanum || "!#$%&'*+-/=?^_`{|}~.".toList.contains c

/-- Does `cs` match the valid e-mail address pattern in full. -/
def matchesEmail (cs : List Char) : Bool :=
  let local_ := cs.takeWhile isEmailLocalChar
  match cs.dropWhile isEmailLocalChar with
  | '@' :: domain =>
    !local_.isEmpty &&
      (let labels := (String.ofList domain).splitOn "."
       labels.all fun l => !l.isEmpty && l.toList.all fun c => c.isAlphanum || c == '-')
  | _ => false

/-- The leftmost start from which `cs` matches `p` to its end. -/
def leftmostMatch (p : List Char → Bool) (cs : List Char) : Option Nat :=
  (List.range cs.length).find? fun i => p (cs.drop i)

/-- "Autolink" the text that ends at a boundary point: the link's start and end offsets
(in characters of the Text node's data) and its `href`. -/
def autolinkTarget (data : List Char) (endOffset : Nat) : Option (Nat × Nat × String) :=
  let pre := data.take endOffset
  let search := (pre.reverse.takeWhile (fun c => !isWs c)).reverse
  let find := fun (p : List Char → Bool) (pfx : String) => Id.run do
    let mut eo := endOffset
    for _ in [0:endOffset + 1] do
      match leftmostMatch p (data.take eo) with
      | some i => return some (i, eo, pfx ++ String.ofList ((data.take eo).drop i))
      | none => if eo == 0 then return none else eo := eo - 1
    return none
  if (leftmostMatch (fun s => (List.range (s.length + 1)).any fun k => matchesUrl (s.take k)) search).isSome then
    find matchesUrl ""
  else if (leftmostMatch (fun s => (List.range (s.length + 1)).any fun k => matchesEmail (s.take k)) search).isSome then
    find matchesEmail "mailto:"
  else none

#guard autolinkTarget "see http://a.b/c".toList 16 == some (4, 16, "http://a.b/c")
#guard autolinkTarget "see http://a.b/c.".toList 17 == some (4, 16, "http://a.b/c")
#guard autolinkTarget "mail x@y.z".toList 10 == some (5, 10, "mailto:x@y.z")
#guard autolinkTarget "plain words".toList 11 == none

def autolink (node : NodeId) (endOffset : Nat) : M Unit := do
  let e ← get
  let d := e.dom
  let bp := firstEquivalentPoint e ⟨node, endOffset⟩
  let node := bp.node
  if !isText d node || (ancestors d node).any (fun a => isHtml d a ["a"]) then return
  let data := (d.get node).data
  -- the tests' text before a link is in the Basic Multilingual Plane: units are characters
  match autolinkTarget data.toList bp.offset with
  | none => return
  | some (s, t, href) =>
    let original ← getActive
    let k ← addRange original
    setActive ⟨⟨node, s⟩, ⟨node, t⟩⟩
    createLink href
    let r ← rangeAt k
    dropRanges k
    setActive r

/-! ## The commands -/

/-- The `delete` command (a backspace). -/
def deleteCommand : M Unit := do
  let r ← getActive
  if !r.collapsed then
    deleteSelection
    return
  canonicalizeWhitespace r.start.node r.start.offset
  let r ← getActive
  let mut node := r.start.node
  let mut offset := r.start.offset
  let bound := 4 * (← rd fun e => e.dom.size) + 8
  for _ in [0:bound] do
    let e ← get
    let d := e.dom
    let prevKid := if offset ≥ 1 then (kidsOf d node)[offset - 1]? else none
    if offset == 0 && isEditableO e (d.previousSibling node) && isInvisibleO e (d.previousSibling node) then
      match d.previousSibling node with
      | some s => removeNode s
      | none => pure ()
    else if isEditableO e prevKid && isInvisibleO e prevKid then
      removeNode (prevKid.getD node)
      offset := offset - 1
    else if (offset == 0 && isInlineNode e node) || isInvisible e node then
      match parentOf d node with
      | some p => offset := indexOf d node; node := p
      | none => break
    else if isEditableO e prevKid && isHtmlO d prevKid ["a"] then
      removePreservingDescendants (prevKid.getD node)
      return
    else if prevKid.isSome && !isBlockNodeO e prevKid && !isHtmlO d prevKid ["br", "img"] then
      node := prevKid.getD node
      offset := nodeLength d node
    else break
  let e ← get
  let d := e.dom
  let prevKid := if offset ≥ 1 then (kidsOf d node)[offset - 1]? else none
  if (isText d node && offset != 0) || (isBlockNode e node && isHtmlO d prevKid ["br", "hr", "img"]) then
    -- one character back: the whole code point (and a combining mark with its base is one unit here)
    let back := if isText d node then
        match (splitAtUnits (d.get node).data offset).1.toList.getLast? with
        | some c => unitsOf c
        | none => 1
      else 1
    setActive ⟨⟨node, offset - back⟩, ⟨node, offset⟩⟩
    deleteSelection
    return
  if isInlineNode e node then return
  if isHtml d node ["li", "dt", "dd"] && (parentOf d node).bind (firstChild d) == some node && offset == 0 then
    for a in (ancestors d node).reverse do
      if isHtml d a ["li"] then normalizeSublists a
    let e ← get
    let values := recordValues e #[node]
    splitParent #[node]
    restoreValues values
    let e ← get
    let d := e.dom
    let mut item := node
    if isHtml d item ["dd", "dt"] && (ancestors d item).all (fun a => !inSameEditingHost e item a || !isAllowedChild e (.node item) a) then
      item ← setTagName item e.sep
    fixDisallowedAncestorsO (some item)
    return
  let mut sn := node
  let mut so := offset
  for _ in [0:bound] do
    let e ← get
    let d := e.dom
    let prevKid := if so ≥ 1 then (kidsOf d sn)[so - 1]? else none
    if so == 0 then
      match parentOf d sn with
      | some p => so := indexOf d sn; sn := p
      | none => break
    else if isEditableO e prevKid && isInvisibleO e prevKid then
      removeNode (prevKid.getD sn)
      so := so - 1
    else break
  let e ← get
  let d := e.dom
  if offset == 0 && (chain d node).any (fun a => isEditable e a && inSameEditingHost e a node && isIndentationElement d a) then
    let nr := blockExtend e ⟨⟨node, 0⟩, ⟨node, 0⟩⟩
    let nodeList := containedNodes d nr fun n => isEditable e n && !hasDescendant d n (isEditable e)
    for n in nodeList do outdentNode (d.size + 1) n
    return
  let atStart := (kidsOf d sn)[so]?
  let beforeStart := if so ≥ 1 then (kidsOf d sn)[so - 1]? else none
  if isHtmlO d atStart ["table"] then return
  if isHtmlO d beforeStart ["table"] then
    setActive ⟨⟨sn, so - 1⟩, ⟨sn, so⟩⟩
    return
  if offset == 0 && (isHtmlO d beforeStart ["hr"] ||
      (isHtmlO d beforeStart ["br"] &&
        (isHtmlO d (beforeStart.bind d.previousSibling) ["br"] || !isInlineNodeO e (beforeStart.bind d.previousSibling)))) then
    setActive ⟨⟨sn, so - 1⟩, ⟨sn, so⟩⟩
    deleteSelection
    setActive ⟨⟨node, offset⟩, ⟨node, offset⟩⟩
    return
  if isHtmlO d atStart ["li", "dt", "dd"] && isInlineNodeO e (atStart.bind (firstChild d)) && so != 0 then
    if let some prevItem := beforeStart then
      if isInlineNodeO e (lastChild d prevItem) && !isHtmlO d (lastChild d prevItem) ["br"] then
        let br ← createElement "br"
        appendChild prevItem br
      let e ← get
      if isInlineNodeO e (lastChild e.dom prevItem) then
        let br ← createElement "br"
        appendChild prevItem br
  let e ← get
  let d := e.dom
  let atStart := (kidsOf d sn)[so]?
  if isHtmlO d atStart ["li", "dt", "dd"] && isHtmlO d (atStart.bind d.previousSibling) ["li", "dt", "dd"] then
    let original ← getActive
    let k ← addRange original
    let sn2 := (kidsOf d sn)[so - 1]!
    let so2 := nodeLength d sn2
    let node2 := (d.nextSibling sn2).getD sn2
    setActive ⟨⟨sn2, so2⟩, ⟨node2, 0⟩⟩
    deleteSelection
    let r ← rangeAt k
    dropRanges k
    setActive r
    return
  for _ in [0:bound] do
    let e ← get
    let d := e.dom
    if so == 0 then break
    match (kidsOf d sn)[so - 1]? with
    | some c =>
      if isEditable e c && isInvisible e c then
        removeNode c
        so := so - 1
      else
        sn := c
        so := nodeLength d c
    | none => break
  setActive ⟨⟨sn, so⟩, ⟨node, offset⟩⟩
  deleteSelection (backward := true)

def isCombining (c : Option Char) : Bool :=
  match c with
  | some c =>
    let n := c.toNat
    (0x300 ≤ n && n ≤ 0x36f) || (0x591 ≤ n && n ≤ 0x5bd) || n == 0x5c1 || n == 0x5c2
  | none => false

/-- The `forwardDelete` command. -/
def forwardDeleteCommand : M Unit := do
  let r ← getActive
  if !r.collapsed then
    deleteSelection
    return
  canonicalizeWhitespace r.start.node r.start.offset
  let r ← getActive
  let mut node := r.start.node
  let mut offset := r.start.offset
  let bound := 4 * (← rd fun e => e.dom.size) + 8
  for _ in [0:bound] do
    let e ← get
    let d := e.dom
    let kid := (kidsOf d node)[offset]?
    if offset == nodeLength d node && isEditableO e (d.nextSibling node) && isInvisibleO e (d.nextSibling node) then
      match d.nextSibling node with
      | some s => removeNode s
      | none => pure ()
    else if isEditableO e kid && isInvisibleO e kid then
      removeNode (kid.getD node)
    else if (offset == nodeLength d node && isInlineNode e node) || isInvisible e node then
      match parentOf d node with
      | some p => offset := 1 + indexOf d node; node := p
      | none => break
    else if kid.isSome && !isBlockNodeO e kid && !isHtmlO d kid ["br", "img"] &&
        !(kid.map (isCollapsedBlockProp e)).getD false then
      node := kid.getD node
      offset := 0
    else break
  let e ← get
  let d := e.dom
  if isText d node && offset != nodeLength d node then
    let first := match charAt d node offset with
      | some c => unitsOf c
      | none => 1
    let mut eo := offset + first
    for _ in [0:nodeLength d node] do
      if eo != nodeLength d node && isCombining (charAt d node eo) then eo := eo + 1 else break
    setActive ⟨⟨node, offset⟩, ⟨node, eo⟩⟩
    deleteSelection
    return
  if isInlineNode e node then return
  let kid := (kidsOf d node)[offset]?
  if isHtmlO d kid ["br", "hr", "img"] && !(kid.map (isCollapsedBlockProp e)).getD false then
    setActive ⟨⟨node, offset⟩, ⟨node, offset + 1⟩⟩
    deleteSelection
    return
  let mut en := node
  let mut eo := offset
  if (kid.map (isCollapsedBlockProp e)).getD false then eo := eo + 1
  for _ in [0:bound] do
    let e ← get
    let d := e.dom
    let k := (kidsOf d en)[eo]?
    if eo == nodeLength d en then
      match parentOf d en with
      | some p => eo := 1 + indexOf d en; en := p
      | none => break
    else if isEditableO e k && isInvisibleO e k then removeNode (k.getD en)
    else break
  let e ← get
  let d := e.dom
  let atEnd := (kidsOf d en)[eo]?
  let beforeEnd := if eo ≥ 1 then (kidsOf d en)[eo - 1]? else none
  if isHtmlO d beforeEnd ["table"] then return
  if isHtmlO d atEnd ["table"] then
    setActive ⟨⟨en, eo⟩, ⟨en, eo + 1⟩⟩
    return
  if offset == nodeLength d node && isHtmlO d atEnd ["br", "hr"] then
    setActive ⟨⟨en, eo⟩, ⟨en, eo + 1⟩⟩
    deleteSelection
    setActive ⟨⟨node, offset⟩, ⟨node, offset⟩⟩
    return
  for _ in [0:bound] do
    let e ← get
    let d := e.dom
    match (kidsOf d en)[eo]? with
    | some c =>
      if isEditable e c && isInvisible e c then removeNode c
      else
        en := c
        eo := 0
    | none => break
  setActive ⟨⟨node, offset⟩, ⟨en, eo⟩⟩
  deleteSelection

def startIsEditable (e : Ed) : Bool :=
  let n := (activeOf e).start.node
  isEditable e n || isEditingHost e n

/-- A boundary point in a Text node's start or end moves to its parent. -/
def leaveTextEdge : M Unit := do
  let e ← get
  let d := e.dom
  let r := activeOf e
  let n := r.start.node
  if isText d n then
    match parentOf d n with
    | some p =>
      if r.start.offset == 0 then
        let bp : BP := ⟨p, indexOf d n⟩
        setActive ⟨bp, bp⟩
      else if r.start.offset == nodeLength d n then
        let bp : BP := ⟨p, 1 + indexOf d n⟩
        setActive ⟨bp, bp⟩
    | none => pure ()

def collapseAfter (n : NodeId) : M Unit := do
  let d ← rd (·.dom)
  match parentOf d n with
  | some p =>
    let bp : BP := ⟨p, 1 + indexOf d n⟩
    setActive ⟨bp, bp⟩
  | none => pure ()

/-- The `insertHorizontalRule` command. -/
def insertHorizontalRule : M Unit := do
  let e ← get
  let d := e.dom
  let r := activeOf e
  let mut sn := r.start.node
  let mut so := r.start.offset
  let mut en := r.stop.node
  let mut eo := r.stop.offset
  for _ in [0:d.size + 1] do
    if so != 0 then break
    match parentOf d sn with
    | some p => so := indexOf d sn; sn := p
    | none => break
  for _ in [0:d.size + 1] do
    if eo != nodeLength d en then break
    match parentOf d en with
    | some p => eo := 1 + indexOf d en; en := p
    | none => break
  setActive ⟨⟨sn, so⟩, ⟨en, eo⟩⟩
  deleteSelection (blockMerging := false)
  if !(← rd startIsEditable) then return
  leaveTextEdge
  let hr ← createElement "hr"
  rangeInsertNode hr
  fixDisallowedAncestorsO (some hr)
  collapseAfter hr

/-- The `insertImage` command. -/
def insertImage (value : String) : M Unit := do
  deleteSelection (stripWrappers := false)
  let e ← get
  if !startIsEditable e then return
  let d := e.dom
  let r := activeOf e
  if isBlockNode e r.start.node && (kidsOf d r.start.node).size == 1 &&
      isHtmlO d (firstChild d r.start.node) ["br"] && r.start.offset == 0 then
    match firstChild d r.start.node with
    | some br => removeNode br
    | none => pure ()
  let img ← createElement "img"
  setAttr img "src" value
  rangeInsertNode img
  collapseAfter img

/-- Does the white-space of the content at the active range's start keep line feeds
(`pre`, `pre-wrap`, `pre-line`, `break-spaces`). -/
def keepsNewlines (e : Ed) : Bool :=
  let n := (activeOf e).start.node
  let el := if isEl e.dom n then some n else parentOf e.dom n
  match el with
  | some el => ["pre", "pre-wrap", "pre-line", "break-spaces"].contains (whiteSpaceOf e el)
  | none => false

/-- A line break at the (collapsed) active range. Where white-space keeps line feeds it
is a U+000A character in the text, as browsers do (the draft always inserts a `br`); a
line feed that ends its block gets a `br` after it, so that the new line shows. Else a
`br`, and a second one when the first would be a collapsed line break. -/
def lineBreakAtCaret : M Unit := do
  let e ← get
  let d := e.dom
  let sn := (activeOf e).start.node
  if isEl d sn && !isAllowedChild e (.name "br") sn then return
  if !isEl d sn then
    match parentOf d sn with
    | some p => if !isAllowedChild e (.name "br") p then return
    | none => return
  if keepsNewlines e then
    let r := activeOf e
    let mut node := r.start.node
    let mut offset := r.start.offset
    if offset ≥ 1 then
      if let some k := (kidsOf d node)[offset - 1]? then
        if isText d k then
          node := k
          offset := nodeLength d k
    if let some k := (kidsOf d node)[offset]? then
      if isText d k then
        node := k
        offset := 0
    setActive ⟨⟨node, offset⟩, ⟨node, offset⟩⟩
    let text ← if isText d node then do
        replaceData node offset 0 "\n"
        pure node
      else do
        let t ← createText "\n"
        rangeInsertNode t
        offset := 0
        pure t
    let caret : BP := ⟨text, offset + 1⟩
    setActive ⟨caret, caret⟩
    let e ← get
    let d := e.dom
    if caret.offset == nodeLength d text && !contentAfter e text then
      let br ← createElement "br"
      match parentOf d text with
      | some p => insertBefore p br (d.nextSibling text)
      | none => pure ()
    return
  leaveTextEdge
  let br ← createElement "br"
  rangeInsertNode br
  collapseAfter br
  if (← rd fun e => isCollapsedLineBreak e br) then
    let br2 ← createElement "br"
    rangeInsertNode br2
    collapseAfter br

/-- The `insertLineBreak` command. -/
def insertLineBreak : M Unit := do
  deleteSelection (stripWrappers := false)
  if !(← rd startIsEditable) then return
  lineBreakAtCaret

/-- Give an empty block its line: a `br`, inside shallow copies of `wrappers` (innermost
first, without `id`). The node the `br` is in. The draft appends the `br` alone; browsers
(and the WPT expectations) keep the inline formatting of the line that was split. -/
def appendEmptyLine (target : NodeId) (wrappers : List NodeId) : M NodeId := do
  let mut parent := target
  for a in wrappers.reverse do
    let c ← cloneNode a false
    removeAttr c "id"
    appendChild parent c
    parent := c
  let br ← createElement "br"
  appendChild parent br
  return parent

/-- The `insertParagraph` command. -/
def insertParagraph : M Unit := do
  deleteSelection
  let e ← get
  if !startIsEditable e then return
  let d := e.dom
  let r := activeOf e
  let mut node := r.start.node
  let mut offset := r.start.offset
  if isText d node && offset != 0 && offset != nodeLength d node then
    let _ ← splitText node offset
  let d ← rd (·.dom)
  if isText d node && offset == nodeLength d node then
    match parentOf d node with
    | some p => offset := 1 + indexOf d node; node := p
    | none => pure ()
  if isText d node || (d.get node).type == .comment then
    match parentOf d node with
    | some p => offset := indexOf d node; node := p
    | none => pure ()
  setActive ⟨⟨node, offset⟩, ⟨node, offset⟩⟩
  let e ← get
  let d := e.dom
  -- a single-line container that is a block, or an editable `span` laid out as a block
  -- (browsers split by the box, where the draft goes by the element name alone)
  let inlineBox := fun (c : NodeId) => ["inline", "inline-block", "inline-table"].contains (displayOf e c)
  let flexItem := fun (c : NodeId) => match parentOf d c with
    | some p => ["flex", "inline-flex", "grid", "inline-grid"].contains (displayOf e p)
    | none => false
  let splittable := fun (c : NodeId) =>
    (isSingleLineContainer d c && !inlineBox c) ||
      (isHtml d c ["span"] && isEditable e c && (displayOf e c == "block" || flexItem c))
  let mut container := node
  for _ in [0:d.size + 1] do
    match parentOf d container with
    | some p =>
      if !splittable container && isEditable e p && inSameEditingHost e node p then container := p else break
    | none => break
  if isEditable e container && splittable container && sameHostO e node (parentOf d container) &&
      isHtml d container ["p", "div"] then
    let mut outer := container
    for _ in [0:d.size + 1] do
      match parentOf d outer with
      | some p => if !isHtml d outer ["dd", "dt", "li"] && isEditable e p then outer := p else break
      | none => break
    if isHtml d outer ["dd", "dt", "li"] then container := outer
  if !isEditable e container || !inSameEditingHost e container node || !splittable container then
    -- in an editing host that is an inline box, or that can not have the default
    -- paragraph element as a child (a `span`, a `p`), no paragraph can be made: a line
    -- break (browsers; the draft wraps the line in a new block inside the host)
    match editingHostOf e node with
    | some h =>
      if isInlineNode e h || !isAllowedChild e (.name e.sep) h then
        lineBreakAtCaret
        return
    | none => pure ()
    let tag := e.sep
    let nr := blockExtend e (activeOf e)
    -- the line to wrap: nodes a `p` may hold, and (as browsers) a single-line container
    -- that is an inline box, which is content of the line, not a paragraph
    let lineNode := fun (n : NodeId) =>
      isAllowedChildOfName e (.node n) "p" || (isSingleLineContainer d n && inlineBox n && isEditable e n)
    let mut nodeList := (containedNodes d nr lineNode).extract 0 1
    if nodeList.isEmpty then
      if !isAllowedChild e (.name tag) (activeOf e).start.node then return
      let c ← createElement tag
      rangeInsertNode c
      let br ← createElement "br"
      appendChild c br
      setActive ⟨⟨c, 0⟩, ⟨c, 0⟩⟩
      return
    for _ in [0:d.size + 1] do
      match d.nextSibling nodeList.back! with
      | some ns => if lineNode ns then nodeList := nodeList.push ns else break
      | none => break
    match ← wrap nodeList (fun _ _ => false) (do return some (← createElement tag)) with
    | some c => container := c
    | none => return
  let e ← get
  let d := e.dom
  if isHtml d container ["address", "listing", "pre"] then
    let br ← createElement "br"
    rangeInsertNode br
    setActive ⟨⟨node, offset + 1⟩, ⟨node, offset + 1⟩⟩
    let d ← rd (·.dom)
    let inContainer := match nextNode d br with
      | some nx => isAncestor d container nx
      | none => false
    if !inContainer then
      let br2 ← createElement "br"
      rangeInsertNode br2
      setActive ⟨⟨node, offset + 1⟩, ⟨node, offset + 1⟩⟩
    return
  if isHtml d container ["li", "dt", "dd"] &&
      (!hasKids d container || ((kidsOf d container).size == 1 && isHtmlO d (firstChild d container) ["br"])) then
    splitParent #[container]
    if !hasKids (← rd (·.dom)) container then
      let br ← createElement "br"
      appendChild container br
    let e ← get
    let d := e.dom
    let mut item := container
    if isHtml d item ["dd", "dt"] &&
        (ancestors d item).all (fun a => !inSameEditingHost e item a || !isAllowedChild e (.node item) a) then
      item ← setTagName item e.sep
    fixDisallowedAncestorsO (some item)
    return
  -- the inline formatting elements around the caret and outside any link, innermost
  -- first: an empty line the split leaves gets copies of them, so typing keeps the format
  let wrappers := (((chain d node).toList.reverse.takeWhile (· != container)).reverse.takeWhile
    (fun a => !isHtml d a ["a"])).reverse.filter fun a =>
      isInlineNode e a && isHtml d a (removeFormatNames.filter (· != "span"))
  -- the new line range: from the active range's start to the end of the container
  let r := activeOf e
  let mut ls := r.start
  for _ in [0:d.size + 1] do
    if ls.offset == 0 && !isProhibitedParagraphChild d ls.node then
      match parentOf d ls.node with
      | some p => ls := ⟨p, indexOf d ls.node⟩
      | none => break
    else break
  for _ in [0:d.size + 1] do
    if ls.offset == nodeLength d ls.node && !isProhibitedParagraphChild d ls.node then
      match parentOf d ls.node with
      | some p => ls := ⟨p, 1 + indexOf d ls.node⟩
      | none => break
    else break
  let newLineRange : Rng := ⟨ls, ⟨container, nodeLength d container⟩⟩
  let containedInNew := containedNodes d newLineRange fun _ => true
  let endOfLine := containedInNew.isEmpty || (containedInNew.size == 1 && isHtml d containedInNew[0]! ["br"])
  let ctag := (d.get container).lname
  let newName :=
    if headingNames.contains ctag && endOfLine then e.sep
    else if ctag == "dt" && endOfLine then "dd"
    else if ctag == "dd" && endOfLine then "dt"
    else ctag
  let newContainer ← createElement newName
  for a in (d.get container).attrs do
    if a.qname != "id" then setAttr newContainer a.qname a.value
  match parentOf d container with
  | some p => insertBefore p newContainer (d.nextSibling container)
  | none => return
  let d ← rd (·.dom)
  let containedAll := allContainedNodes d newLineRange fun _ => true
  let frag ← extractRange (d.size + 1) newLineRange
  let d ← rd (·.dom)
  for n in d.treeOrder frag false do
    if isEl d n && !containedAll.contains n && hasAttr d n "id" then removeAttr n "id"
  appendChild newContainer frag
  let mut c1 := container
  let mut c2 := newContainer
  let d ← rd (·.dom)
  for _ in [0:d.size + 1] do
    match lastChild d c1 with
    | some c => if isProhibitedParagraphChild d c then c1 := c else break
    | none => break
  for _ in [0:d.size + 1] do
    match lastChild d c2 with
    | some c => if isProhibitedParagraphChild d c then c2 := c else break
    | none => break
  let e ← get
  if !(kidsOf e.dom c1).any (isVisible e) then
    let _ ← appendEmptyLine c1 (if c1 == container then wrappers else [])
  let e ← get
  let mut caret := c2
  if !(kidsOf e.dom c2).any (isVisible e) then
    caret ← appendEmptyLine c2 (if c2 == newContainer then wrappers else [])
  setActive ⟨⟨caret, 0⟩, ⟨caret, 0⟩⟩

/-- A caret at the very start or end of the content of a link (`a` with `href`): the
point just outside the link, on that side. Text typed at the edge of a link does not
join the link (browsers; `editing/other/typing-around-link-element-*`). -/
def leaveLinkEdge (e : Ed) (bp : BP) : Option BP := Id.run do
  let d := e.dom
  let isLink := fun (n : NodeId) => isHtml d n ["a"] && hasAttr d n "href"
  if !(chain d bp.node).any isLink then return none
  let atEnd := bp.offset == nodeLength d bp.node
  let atStart := bp.offset == 0
  -- inside the content, or in an emptied link (its content was just replaced): stay
  if atEnd == atStart then return none
  let mut cur := bp.node
  for _ in [0:d.size + 1] do
    let some p := parentOf d cur | return none
    if !isEditable e cur then return none
    let i := indexOf d cur
    if isLink cur then return some ⟨p, if atEnd then i + 1 else i⟩
    if atEnd && i + 1 != (kidsOf d p).size then return none
    if !atEnd && i != 0 then return none
    cur := p
  return none

/-- Inside a link. Says: a caret that is neither at the start nor at the end of its node
is never moved out of a link, so text typed inside a link's text joins the link. Does not
say: what happens at the edges (the caret leaves the link when its node is the first or
last content of the link; tested). -/
theorem leaveLinkEdge_inside (e : Ed) (bp : BP) (h0 : bp.offset ≠ 0)
    (h1 : bp.offset ≠ nodeLength e.dom bp.node) : leaveLinkEdge e bp = none := by
  have a : (bp.offset == nodeLength e.dom bp.node) = false := by simpa using h1
  have b : (bp.offset == 0) = false := by simpa using h0
  unfold leaveLinkEdge
  simp only [a, b]
  split <;> rfl

/-- Insert one character (not a newline) at the active range. -/
def insertChar (c : Char) : M Unit := do
  let e ← get
  let d := e.dom
  let r := activeOf e
  let mut node := r.start.node
  let mut offset := r.start.offset
  if offset ≥ 1 then
    if let some k := (kidsOf d node)[offset - 1]? then
      if isText d k then
        node := k
        offset := nodeLength d k
  if let some k := (kidsOf d node)[offset]? then
    if isText d k then
      node := k
      offset := 0
  let overrides ← recordCurrentOverrides
  setActive ⟨⟨node, offset⟩, ⟨node, offset⟩⟩
  canonicalizeWhitespace node offset
  let e ← get
  let r := activeOf e
  match leaveLinkEdge e r.start with
  | some out => setActive ⟨out, out⟩
  | none => pure ()
  let e ← get
  let d := e.dom
  let r := activeOf e
  node := r.start.node
  offset := r.start.offset
  let s := String.singleton c
  if isText d node then
    replaceData node offset 0 s
    setActive ⟨⟨node, offset⟩, ⟨node, offset + unitsOf c⟩⟩
  else
    if (kidsOf d node).size == 1 then
      if let some fc := firstChild d node then
        if isCollapsedLineBreak e fc then removeNode fc
    let text ← createText s
    rangeInsertNode text
    setActive ⟨⟨text, 0⟩, ⟨text, unitsOf c⟩⟩
  restoreStatesAndValues overrides
  let r ← getActive
  canonicalizeWhitespace r.start.node r.start.offset false
  let r ← getActive
  canonicalizeWhitespace r.stop.node r.stop.offset false
  -- The draft autolinks here (a URL or address before a typed space becomes a link);
  -- browsers do not, and the WPT expectations are theirs. `autolink` is kept, unused.
  collapseActive false

/-- Split the inline elements around the (collapsed) active range, up to its block: the
caret ends between the halves (or before, or after, an element it was at the edge of).
Markup that `insertHTML` inserts does not take the inline formatting of the insertion
point (browsers; `editing/other/inserthtml-do-not-preserve-inline-styles.html`). -/
def splitInlineAtCaret : M Unit := do
  let bound ← rd fun e => e.dom.size + 1
  for _ in [0:bound] do
    let e ← get
    let d := e.dom
    let bp := (activeOf e).start
    let node := bp.node
    let some p := parentOf d node | break
    let i := indexOf d node
    if isText d node then
      if bp.offset == 0 then setActive ⟨⟨p, i⟩, ⟨p, i⟩⟩
      else if bp.offset == nodeLength d node then setActive ⟨⟨p, i + 1⟩, ⟨p, i + 1⟩⟩
      else
        let _ ← splitText node bp.offset
        setActive ⟨⟨p, i + 1⟩, ⟨p, i + 1⟩⟩
    else if isEl d node && isInlineNode e node && isEditable e node then
      if bp.offset == 0 then setActive ⟨⟨p, i⟩, ⟨p, i⟩⟩
      else if bp.offset == (kidsOf d node).size then setActive ⟨⟨p, i + 1⟩, ⟨p, i + 1⟩⟩
      else
        let clone ← cloneNode node false
        removeAttr clone "id"
        insertBefore p clone (d.nextSibling node)
        for c in (kidsOf d node).extract bp.offset (kidsOf d node).size do appendChild clone c
        setActive ⟨⟨p, i + 1⟩, ⟨p, i + 1⟩⟩
    else break

/-- Runs of whitespace as one space, none at the ends (a line of collapsed text). -/
def collapseLine (s : String) : String :=
  " ".intercalate ((String.ofList (s.toList.map fun c => if isWs c then ' ' else c)).splitOn " " |>.filter (!·.isEmpty))

/-- The text of a fragment as lines, as it would show: no text of elements that are not
rendered (`script`, `style`, `noscript`, ...), whitespace collapsed outside `pre`, a new
line at each `br`, block boundary and (in `pre`) line feed. -/
def plainLines (e : Ed) (frag : NodeId) : List String := Id.run do
  let d := e.dom
  let hidden := fun (n : NodeId) => (chain d n).any fun a =>
    isHtml d a (hiddenTags ++ ["noscript", "noframes", "head"])
  let inPre := fun (n : NodeId) => (chain d n).any fun a => isHtml d a ["pre", "listing", "xmp", "plaintext", "textarea"]
  let blockOf := fun (n : NodeId) => (chain d n).toList.reverse.find? fun a => a != n && isEl d a && blockTags.contains (d.get a).lname
  let mut lines : Array String := #[]
  let mut cur : String := ""
  let mut started := false
  let mut curBlock : Option NodeId := none
  for n in d.treeOrder frag false do
    if hidden n then continue
    if isHtml d n ["br"] then
      lines := lines.push cur
      cur := ""
      started := true
      continue
    if isText d n then
      let b := blockOf n
      if started && b != curBlock && !cur.isEmpty then
        lines := lines.push cur
        cur := ""
      curBlock := b
      started := true
      if inPre n then
        match (d.get n).data.splitOn "\n" with
        | first :: rest =>
          cur := cur ++ first
          for piece in rest do
            lines := lines.push cur
            cur := piece
        | [] => pure ()
      else cur := cur ++ (String.ofList ((d.get n).data.toList.map fun c => if isWs c then ' ' else c))
  if !cur.isEmpty || !lines.isEmpty then lines := lines.push cur
  -- collapse each line that has no run of two spaces to keep (text outside `pre` was
  -- already mapped to spaces; a `pre` line is kept as it is)
  return lines.toList

/-- The `insertHTML` command. -/
def insertHTML (value : String) : M Unit := do
  deleteSelection
  let e ← get
  if !startIsEditable e then return
  if inPlaintextHost e then
    -- a `plaintext-only` editing host takes the text of the markup, line by line
    let frag ← parseFragment htmlNS "div" value
    let e ← get
    let d := e.dom
    let pre := (d.treeOrder frag false).any fun n => isHtml d n ["pre", "listing", "xmp", "plaintext", "textarea"]
    let lines := (plainLines e frag).map fun l => if pre then l else collapseLine l
    let mut first := true
    for line in lines do
      if !first then lineBreakAtCaret
      first := false
      for c in line.toList do insertChar c
    return
  let d := e.dom
  let r := activeOf e
  -- the context of the fragment parse: the start node, or its parent for a Text node
  let ctx := if isEl d r.start.node then some r.start.node else d.parentElement r.start.node
  let (ns, name) := match ctx with
    | some c =>
      let x := d.get c
      if x.lname == "html" && x.ns == some htmlNS then (htmlNS, "body") else (x.ns.getD "", x.lname)
    | none => (htmlNS, "body")
  let frag ← parseFragment ns name value
  -- inline markup (no block among it): it goes between the halves of the inline elements
  -- at the caret; a block is placed by "fix disallowed ancestors", which keeps the values
  if (← rd fun e => (kidsOf e.dom frag).any (isEl e.dom) &&
      !(kidsOf e.dom frag).any (isProhibitedParagraphChild e.dom)) then splitInlineAtCaret
  let e ← get
  let d := e.dom
  let some last := lastChild d frag | return
  let descendants := d.treeOrder frag false
  let r := activeOf e
  if isBlockNode e r.start.node then
    for n in (kidsOf d r.start.node).filter fun n =>
        isEditable e n && isCollapsedBlockProp e n && indexOf d n ≥ r.start.offset do
      removeNode n
  rangeInsertNode frag
  let e ← get
  let d := e.dom
  let sn := (activeOf e).start.node
  if isBlockNode e sn && !(kidsOf d sn).any (isVisible e) then
    let br ← createElement "br"
    appendChild sn br
  collapseAfter last
  for n in descendants do fixDisallowedAncestorsO (some n)

/-- The `insertText` command: each character in turn; a newline is `insertParagraph`. -/
def insertText (value : String) : M Unit := do
  deleteSelection (stripWrappers := false)
  if !(← rd startIsEditable) then return
  for c in value.toList do
    -- each character deletes the (now collapsed) selection first, as the draft's recursion does
    deleteSelection (stripWrappers := false)
    if !(← rd startIsEditable) then return
    if c == '\n' then insertParagraph else insertChar c

/-- The action of a deleting or inserting command; `none` when `command` is not one. -/
def deleteAction (command value : String) : M (Option Bool) := do
  match command with
  | "delete" => return some (← preservingOverrides (do deleteCommand; return true))
  | "forwarddelete" => return some (← preservingOverrides (do forwardDeleteCommand; return true))
  | "inserthorizontalrule" => return some (← preservingOverrides (do insertHorizontalRule; return true))
  | "inserthtml" => return some (← preservingOverrides (do insertHTML value; return true))
  | "insertimage" =>
    if value.isEmpty then return some false
    return some (← preservingOverrides (do insertImage value; return true))
  | "insertlinebreak" => return some (← preservingOverrides (do insertLineBreak; return true))
  | "insertparagraph" => return some (← preservingOverrides (do insertParagraph; return true))
  | "inserttext" => insertText value; return some true
  | _ => return none

def deleteCommands : List String :=
  ["delete", "forwarddelete", "inserthorizontalrule", "inserthtml", "insertimage", "insertlinebreak",
   "insertparagraph", "inserttext"]

end L4Factoidal.DOM.Editing
