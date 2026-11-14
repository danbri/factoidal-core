/-
L4Factoidal.DOM.Editing.Delete — deleting the selection, and the commands that insert.

Specification: W3C Editing APIs draft: "Canonical space sequences", "canonicalize
whitespace", "Deleting the selection", the equivalent points of a boundary point,
"Automatic linking", and the commands `delete`, `forwardDelete`, `insertHorizontalRule`,
`insertHTML`, `insertImage`, `insertLineBreak`, `insertParagraph`, `insertText`. The Range
algorithms "insert" and "extract" (DOM §5.5) are here as functions of the editing state.

Proved: `canonicalSpaceSequence_length` (the sequence for `n` spaces has `n` characters)
and `canonicalSpaceSequence_chars` (only U+0020 and U+00A0). That no two U+0020 are
adjacent is tested on the first lengths, not proved.
Tested only (the WPT cases): the tree algorithms.
-/
import L4Factoidal.DOM.Editing.Block

namespace L4Factoidal.DOM.Editing
open L4Factoidal.DOM L4Factoidal.DOM.Range

/-! ## Canonical space sequences -/

def nbsp : Char := Char.ofNat 0xa0

/-- The repeated pairs before the last two or three characters: `k` pairs. -/
def spacePairs (nbStart : Bool) : Nat → List Char
  | 0 => []
  | k + 1 => (if nbStart then [nbsp, ' '] else [' ', nbsp]) ++ spacePairs nbStart k

/-- The last characters of a sequence of length two or three. -/
def spaceTail (three nbStart nbEnd : Bool) : List Char :=
  if three then
    match nbStart, nbEnd with
    | false, false => [' ', nbsp, ' ']
    | true, false => [nbsp, nbsp, ' ']
    | false, true => [' ', nbsp, nbsp]
    | true, true => [nbsp, ' ', nbsp]
  else
    match nbStart, nbEnd with
    | false, false => [nbsp, ' ']
    | true, false => [nbsp, ' ']
    | false, true => [' ', nbsp]
    | true, true => [nbsp, nbsp]

/-- "Canonical space sequence" of length `n`: spaces and no-break spaces that render as
`n` spaces, with a no-break space where a space would collapse (at a line start when
`nbStart`, at a line end when `nbEnd`). -/
def canonicalSpaceSequence (n : Nat) (nbStart nbEnd : Bool) : List Char :=
  if n == 0 then []
  else if n == 1 then (if !nbStart && !nbEnd then [' '] else [nbsp])
  else
    -- n = 2 + 2k (tail of two) or 3 + 2k (tail of three)
    let three := n % 2 == 1
    let k := (n - (if three then 3 else 2)) / 2
    spacePairs nbStart k ++ spaceTail three nbStart nbEnd

theorem spacePairs_length (nbStart : Bool) (k : Nat) : (spacePairs nbStart k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => cases nbStart <;> simp [spacePairs, ih] <;> omega

theorem spaceTail_length (three nbStart nbEnd : Bool) :
    (spaceTail three nbStart nbEnd).length = if three then 3 else 2 := by
  cases three <;> cases nbStart <;> cases nbEnd <;> rfl

/-- Length. Says: the canonical space sequence for `n` has exactly `n` characters, so
replacing a run of `n` spaces by it keeps every offset after the run. Does not say: that
the sequence renders as `n` spaces in every font (it does by CSS white-space rules when no
two U+0020 are adjacent and none is at a collapsing edge). -/
theorem canonicalSpaceSequence_length (n : Nat) (nbStart nbEnd : Bool) :
    (canonicalSpaceSequence n nbStart nbEnd).length = n := by
  unfold canonicalSpaceSequence
  by_cases h0 : n = 0
  · simp [h0]
  · by_cases h1 : n = 1
    · subst h1; cases nbStart <;> cases nbEnd <;> rfl
    · have hb0 : (n == 0) = false := by simpa using h0
      have hb1 : (n == 1) = false := by simpa using h1
      simp only [hb0, hb1, Bool.false_eq_true, if_false, List.length_append, spacePairs_length, spaceTail_length]
      by_cases h3 : n % 2 = 1
      · have : (n % 2 == 1) = true := by simpa using h3
        simp only [this, if_true]
        omega
      · have : (n % 2 == 1) = false := by simpa using h3
        simp only [this, Bool.false_eq_true, if_false]
        omega

def isSpaceOrNbsp (c : Char) : Bool := c == ' ' || c == nbsp

theorem spacePairs_all (nbStart : Bool) (k : Nat) : (spacePairs nbStart k).all isSpaceOrNbsp = true := by
  induction k with
  | zero => rfl
  | succ k ih =>
    cases nbStart
    · have : spacePairs false (k + 1) = [' ', nbsp] ++ spacePairs false k := rfl
      rw [this, List.all_append, ih]; decide
    · have : spacePairs true (k + 1) = [nbsp, ' '] ++ spacePairs true k := rfl
      rw [this, List.all_append, ih]; decide

theorem spaceTail_all (three nbStart nbEnd : Bool) : (spaceTail three nbStart nbEnd).all isSpaceOrNbsp = true := by
  cases three <;> cases nbStart <;> cases nbEnd <;> decide

/-- Characters. Says: the canonical space sequence holds only U+0020 and U+00A0. Does
not say: where each one is (tested by `#guard`). -/
theorem canonicalSpaceSequence_chars (n : Nat) (nbStart nbEnd : Bool) :
    (canonicalSpaceSequence n nbStart nbEnd).all isSpaceOrNbsp = true := by
  unfold canonicalSpaceSequence
  split
  · rfl
  · split
    · cases nbStart <;> cases nbEnd <;> decide
    · rw [List.all_append, spacePairs_all, spaceTail_all]; rfl

#guard canonicalSpaceSequence 2 false false == [nbsp, ' ']
#guard canonicalSpaceSequence 3 false false == [' ', nbsp, ' ']
#guard canonicalSpaceSequence 4 false false == [' ', nbsp, nbsp, ' ']
#guard canonicalSpaceSequence 5 true true == [nbsp, ' ', nbsp, ' ', nbsp]
#guard canonicalSpaceSequence 6 false true == [' ', nbsp, ' ', nbsp, ' ', nbsp]
-- no two adjacent U+0020, and none at a non-breaking edge, for the first lengths
#guard (List.range 12).all fun n => [false, true].all fun a => [false, true].all fun b =>
  let s := canonicalSpaceSequence n a b
  (s.zip (s.drop 1)).all (fun (x, y) => !(x == ' ' && y == ' ')) &&
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
      replaceData c 0 (nodeLength d c) (substringUnits (d.get sn).data so (eo - so))
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
        replaceData c 0 (nodeLength d c) (substringUnits (d.get sn).data so (len - so))
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
        replaceData c 0 (nodeLength d c) (substringUnits (d.get en).data 0 eo)
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

/-- "Delete the selection". -/
def deleteSelection (blockMerging : Bool := true) (stripWrappers : Bool := true) (backward : Bool := false) : M Unit := do
  if !(← rd hasActive) then return
  let r ← getActive
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

/-- The `insertHTML` command. -/
def insertHTML (value : String) : M Unit := do
  deleteSelection
  let e ← get
  if !startIsEditable e then return
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

/-- The `insertLineBreak` command. -/
def insertLineBreak : M Unit := do
  deleteSelection (stripWrappers := false)
  let e ← get
  if !startIsEditable e then return
  let d := e.dom
  let sn := (activeOf e).start.node
  if isEl d sn && !isAllowedChild e (.name "br") sn then return
  if !isEl d sn then
    match parentOf d sn with
    | some p => if !isAllowedChild e (.name "br") p then return
    | none => return
  leaveTextEdge
  let br ← createElement "br"
  rangeInsertNode br
  collapseAfter br
  if (← rd fun e => isCollapsedLineBreak e br) then
    let br2 ← createElement "br"
    rangeInsertNode br2
    collapseAfter br

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
  let mut container := node
  for _ in [0:d.size + 1] do
    match parentOf d container with
    | some p =>
      if !isSingleLineContainer d container && isEditable e p && inSameEditingHost e node p then container := p else break
    | none => break
  if isEditable e container && isSingleLineContainer d container && sameHostO e node (parentOf d container) &&
      isHtml d container ["p", "div"] then
    let mut outer := container
    for _ in [0:d.size + 1] do
      match parentOf d outer with
      | some p => if !isHtml d outer ["dd", "dt", "li"] && isEditable e p then outer := p else break
      | none => break
    if isHtml d outer ["dd", "dt", "li"] then container := outer
  if !isEditable e container || !inSameEditingHost e container node || !isSingleLineContainer d container then
    let tag := e.sep
    let nr := blockExtend e (activeOf e)
    let mut nodeList := (containedNodes d nr fun n => isAllowedChildOfName e (.node n) "p").extract 0 1
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
      | some ns => if isAllowedChildOfName e (.node ns) "p" then nodeList := nodeList.push ns else break
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
  if isWs c then
    let r ← getActive
    autolink r.start.node r.start.offset
  collapseActive false

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
