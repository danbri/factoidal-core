/-
L4Factoidal.HTML.TreeBuilder — tree construction of the WHATWG HTML Living
Standard, §13.2.6 "Tree construction", over the tokens of
`HTML/Tokenizer.lean`.

The DOM is an arena (`TB.dom`, an array of `DNode`; index 0 is the Document).
The stack of open elements and the list of active formatting elements hold
indexes into it. Each insertion mode is a function `Token → P Act`, where
`Act` says what the dispatcher does next: the token is done, the token is
reprocessed in the (new) current mode, or it is processed "using the rules
for" another mode. The dispatcher is a loop bounded by fuel.

Implemented (section numbers of §13.2.6.4):
  insertion modes initial, before html, before head, in head, in head
  noscript (the scripting flag is OFF, so the content of `noscript` is
  parsed as elements), after head, in body, text, in table, in table text,
  in caption, in column group, in table body, in row, in cell, in select,
  in select in table, in template, after body, in frameset, after frameset,
  after after body, after after frameset;
  tree construction dispatcher (§13.2.6.1) with MathML and HTML integration
  points, and the rules for parsing tokens in foreign content (§13.2.6.5)
  with the SVG tag name and attribute adjustments and the MathML ones;
  implied `html`, `head`, `body`; void elements; "has an element in
  scope" for the default, list item, button, table and select scopes;
  implied end tags (also thorough); the list of active formatting elements
  with markers, the Noah's Ark clause, "reconstruct the active formatting
  elements" and the adoption agency algorithm (§13.2.6.4.7, including the
  outer loop of 8 and the inner loop with its counter); foster parenting;
  `template` (its children are the children of the `template` element in the
  arena; there is no separate template contents document fragment);
  the stack of template insertion modes and "reset the insertion mode
  appropriately"; the LF after `pre`, `listing`, `textarea`; self-closing
  flag acknowledgement; quirks mode from the DOCTYPE (a short list of public
  identifier prefixes); generic RCDATA and raw text parsing for `title`,
  `textarea`, `style`, `xmp`, `iframe`, `noembed`, `noframes`, `script`;
  `plaintext`; parse errors for every rule that has one in the places above.

Not implemented: the HTML fragment parsing algorithm (§13.2.6.4 "context
element"; the function always parses a whole document); `form` element
association other than the form element pointer; `isindex`; script
execution (`document.write`, the script nesting level, the parser pause,
`async`/`defer` handling); the `<meta charset>` change-the-encoding step
(`HTML/Html.lean`'s caller does a prescan instead); the `srcdoc` and
"iframe" document rules; the full quirks mode table (limited-quirks mode is
not distinguished from no-quirks mode); the customizable `select` content
model of the newest Living Standard (the older `in select` rules are used).
-/
import L4Factoidal.HTML.Tokenizer

namespace L4Factoidal.HTML

inductive NS where
  | html | svg | math
deriving BEq, Inhabited

inductive DKind where
  | doc | elem | text | comment
deriving BEq, Inhabited

structure DNode where
  kind : DKind := .elem
  ns : NS := .html
  name : String := ""
  attrs : Array (String × String) := #[]
  data : String := ""
  parent : Option Nat := none
  kids : Array Nat := #[]

instance : Inhabited DNode := ⟨{}⟩

inductive Mode where
  | initial | beforeHtml | beforeHead | inHead | inHeadNoscript | afterHead | inBody | text
  | inTable | inTableText | inCaption | inColumnGroup | inTableBody | inRow | inCell
  | inSelect | inSelectInTable | inTemplate | afterBody | inFrameset | afterFrameset
  | afterAfterBody | afterAfterFrameset
deriving BEq, Inhabited

structure TB where
  dom : Array DNode := #[{ kind := .doc }]
  stack : Array Nat := #[]
  afe : Array (Option Nat) := #[]
  mode : Mode := .initial
  orig : Mode := .initial
  tmodes : Array Mode := #[]
  headPtr : Option Nat := none
  formPtr : Option Nat := none
  framesetOk : Bool := true
  quirks : Bool := false
  foster : Bool := false
  ack : Bool := false
  pend : Array Char := #[]
  skipLF : Bool := false
  errs : Array String := #[]
  tk : Tok
  done : Bool := false

abbrev P := StateM TB

inductive Act where
  | done | reprocess | via (m : Mode)

/-! ## Arrays and nodes -/

def arrRemove {α : Type} (a : Array α) (i : Nat) : Array α := a.extract 0 i ++ a.extract (i + 1) a.size
def arrInsert {α : Type} (a : Array α) (i : Nat) (x : α) : Array α := (a.extract 0 i).push x ++ a.extract i a.size

def DNode.is (n : DNode) (nm : String) : Bool := n.kind == .elem && n.ns == .html && n.name == nm
def DNode.isAny (n : DNode) (nms : List String) : Bool := n.kind == .elem && n.ns == .html && nms.contains n.name

def specialHtml : List String :=
  ["address", "applet", "area", "article", "aside", "base", "basefont", "bgsound", "blockquote", "body", "br",
   "button", "caption", "center", "col", "colgroup", "dd", "details", "dir", "div", "dl", "dt", "embed",
   "fieldset", "figcaption", "figure", "footer", "form", "frame", "frameset", "h1", "h2", "h3", "h4", "h5",
   "h6", "head", "header", "hgroup", "hr", "html", "iframe", "img", "input", "keygen", "li", "link", "listing",
   "main", "marquee", "menu", "meta", "nav", "noembed", "noframes", "noscript", "object", "ol", "p", "param",
   "plaintext", "pre", "script", "search", "section", "select", "source", "style", "summary", "table", "tbody",
   "td", "template", "textarea", "tfoot", "th", "thead", "title", "tr", "track", "ul", "wbr", "xmp"]

def mathTextNames : List String := ["mi", "mo", "mn", "ms", "mtext"]
def svgHtmlIPNames : List String := ["foreignObject", "desc", "title"]

def isSpecial (n : DNode) : Bool :=
  n.kind == .elem && match n.ns with
    | .html => specialHtml.contains n.name
    | .math => mathTextNames.contains n.name || n.name == "annotation-xml"
    | .svg => svgHtmlIPNames.contains n.name

def mathTextIP (n : DNode) : Bool := n.kind == .elem && n.ns == .math && mathTextNames.contains n.name

def htmlIP (n : DNode) : Bool :=
  n.kind == .elem &&
  ((n.ns == .math && n.name == "annotation-xml" &&
      n.attrs.any (fun a => a.1 == "encoding" && (lowerStr a.2 == "text/html" || lowerStr a.2 == "application/xhtml+xml")))
    || (n.ns == .svg && svgHtmlIPNames.contains n.name))

inductive Scope where
  | default | listItem | button | table | select
deriving BEq

def defaultBoundary (n : DNode) : Bool :=
  match n.ns with
  | .html => n.isAny ["applet", "caption", "html", "table", "td", "th", "marquee", "object", "template"]
  | .math => mathTextNames.contains n.name || n.name == "annotation-xml"
  | .svg => svgHtmlIPNames.contains n.name

def boundary (n : DNode) (s : Scope) : Bool :=
  match s with
  | .default => defaultBoundary n
  | .listItem => defaultBoundary n || n.isAny ["ol", "ul"]
  | .button => defaultBoundary n || n.is "button"
  | .table => n.isAny ["html", "table", "template"]
  | .select => !(n.isAny ["optgroup", "option"])

def isTreeWs (c : Char) : Bool := c == '\t' || c == '\n' || c == '\x0C' || c == '\r' || c == ' '

/-! ## Monadic helpers -/

def getN (i : Nat) : P DNode := do return (← get).dom[i]!
def modN (i : Nat) (f : DNode → DNode) : P Unit := modify fun tb => { tb with dom := tb.dom.modify i f }
def perr (s : String) : P Unit := modify fun tb => { tb with errs := tb.errs.push s }
def curNode : P DNode := do
  let tb ← get
  match tb.stack.back? with
  | some i => return tb.dom[i]!
  | none => return default
def setMode (m : Mode) : P Unit := modify fun tb => { tb with mode := m }
def popCur : P Unit := modify fun tb => { tb with stack := tb.stack.pop }

def newNode (n : DNode) : P Nat := do
  let tb ← get
  set { tb with dom := tb.dom.push n }
  return tb.dom.size

def insertAt (parent : Nat) (before : Option Nat) (child : Nat) : P Unit := modify fun tb =>
  let p := tb.dom[parent]!
  let kids := match before with
    | none => p.kids.push child
    | some b => match p.kids.findIdx? (· == b) with
      | some k => arrInsert p.kids k child
      | none => p.kids.push child
  { tb with dom := (tb.dom.set! parent { p with kids }).modify child (fun c => { c with parent := some parent }) }

def detach (child : Nat) : P Unit := modify fun tb =>
  match tb.dom[child]!.parent with
  | none => tb
  | some p =>
    let pn := tb.dom[p]!
    let d1 := tb.dom.set! p { pn with kids := pn.kids.filter (· != child) }
    { tb with dom := d1.modify child (fun c => { c with parent := none }) }

def lastIdx (tb : TB) (pred : DNode → Bool) : Option Nat := Id.run do
  let mut r : Option Nat := none
  for i in [0:tb.stack.size] do
    if pred tb.dom[tb.stack[i]!]! then r := some i
  return r

def tablePlace (tb : TB) (b : Nat) : Nat × Option Nat :=
  let tid := tb.stack[b]!
  match tb.dom[tid]!.parent with
  | some p => (p, some tid)
  | none => (tb.stack[b - 1]!, none)

/-- "The appropriate place for inserting a node" (§13.2.6.1), with foster parenting. -/
def appropriatePlace (override : Option Nat := none) : P (Nat × Option Nat) := do
  let tb ← get
  let target := match override with
    | some o => o
    | none => tb.stack.back?.getD 0
  let tn := tb.dom[target]!
  if tb.foster && tn.isAny ["table", "tbody", "tfoot", "thead", "tr"] then
    let lt := lastIdx tb (·.is "template")
    let lb := lastIdx tb (·.is "table")
    match lt, lb with
    | some t, some b => return (if t > b then (tb.stack[t]!, none) else tablePlace tb b)
    | some t, none => return (tb.stack[t]!, none)
    | none, some b => return tablePlace tb b
    | none, none => return (tb.stack[0]!, none)
  else return (target, none)

def insertChar (c : Char) : P Unit := do
  let (par, before) ← appropriatePlace
  if par == 0 then return
  let tb ← get
  let pn := tb.dom[par]!
  let prev : Option Nat := match before with
    | none => pn.kids.back?
    | some b => match pn.kids.findIdx? (· == b) with
      | some k => if k == 0 then none else some pn.kids[k - 1]!
      | none => none
  match prev with
  | some pv =>
    if tb.dom[pv]!.kind == .text then
      modN pv (fun n => { n with data := n.data.push c })
    else
      let id ← newNode { kind := .text, data := c.toString }
      insertAt par before id
  | none =>
    let id ← newNode { kind := .text, data := c.toString }
    insertAt par before id

def insertComment (data : String) (target : Option Nat := none) : P Unit := do
  let (par, before) ← appropriatePlace target
  let id ← newNode { kind := .comment, data }
  insertAt par before id

def insertElement (ns : NS) (name : String) (attrs : Array (String × String)) : P Nat := do
  let id ← newNode { kind := .elem, ns, name, attrs }
  let (par, before) ← appropriatePlace
  insertAt par before id
  modify fun tb => { tb with stack := tb.stack.push id }
  return id

def insertHtml (name : String) (attrs : List (String × String) := []) : P Nat :=
  insertElement .html name attrs.toArray

def hasScope (pred : DNode → Bool) (s : Scope) : P Bool := do
  let tb ← get
  let mut i := tb.stack.size
  for _ in [0:tb.stack.size] do
    if i == 0 then break
    i := i - 1
    let n := tb.dom[tb.stack[i]!]!
    if pred n then return true
    if boundary n s then return false
  return false

def hasNamed (nm : String) (s : Scope) : P Bool := hasScope (·.is nm) s

def hasOnStack (pred : DNode → Bool) : P Bool := do
  let tb ← get
  return tb.stack.any (fun i => pred tb.dom[i]!)

def popUntil (pred : DNode → Bool) : P Unit := do
  for _ in [0:(← get).stack.size] do
    let tb ← get
    match tb.stack.back? with
    | none => return
    | some i =>
      set { tb with stack := tb.stack.pop }
      if pred tb.dom[i]! then return

def popUntilId (id : Nat) : P Unit := do
  for _ in [0:(← get).stack.size] do
    let tb ← get
    match tb.stack.back? with
    | none => return
    | some i =>
      set { tb with stack := tb.stack.pop }
      if i == id then return

def impliedNames : List String := ["dd", "dt", "li", "optgroup", "option", "p", "rb", "rp", "rt", "rtc"]
def impliedThoroughNames : List String :=
  impliedNames ++ ["caption", "colgroup", "tbody", "td", "tfoot", "th", "thead", "tr"]

/-- Generate implied end tags (§13.2.6.3); `except` is a name that is not popped. -/
def genImplied (thorough : Bool := false) (except : String := "") : P Unit := do
  for _ in [0:(← get).stack.size] do
    let n ← curNode
    if n.isAny (if thorough then impliedThoroughNames else impliedNames) && n.name != except then popCur
    else return

def closeP : P Unit := do
  if ← hasNamed "p" .button then
    genImplied false "p"
    if !(← curNode).is "p" then perr "end-tag-implied-p"
    popUntil (·.is "p")

def clearToContext (names : List String) : P Unit := do
  for _ in [0:(← get).stack.size] do
    let n ← curNode
    if n.isAny names || n.isAny ["template", "html"] then return
    popCur

/-! ## List of active formatting elements -/

def sameEl (a b : DNode) : Bool :=
  a.ns == b.ns && a.name == b.name && a.attrs.size == b.attrs.size && a.attrs.all (fun x => b.attrs.contains x)

def afePush (id : Nat) : P Unit := modify fun tb =>
  let n := tb.dom[id]!
  let ms : List Nat := Id.run do
    let mut r : List Nat := []
    let mut i := tb.afe.size
    for _ in [0:tb.afe.size] do
      if i == 0 then break
      i := i - 1
      match tb.afe[i]! with
      | none => break
      | some e => if sameEl tb.dom[e]! n then r := i :: r
    return r
  let afe := match ms with
    | k :: _ => if ms.length ≥ 3 then arrRemove tb.afe k else tb.afe
    | [] => tb.afe
  { tb with afe := afe.push (some id) }

def clearAfeToMarker : P Unit := do
  for _ in [0:(← get).afe.size] do
    let tb ← get
    match tb.afe.back? with
    | none => return
    | some e =>
      set { tb with afe := tb.afe.pop }
      if e.isNone then return

/-- The entry after the last marker that is an `a`-like element named `nm`. -/
def afeFind (tb : TB) (nm : String) : Option (Nat × Nat) := Id.run do
  let mut i := tb.afe.size
  for _ in [0:tb.afe.size] do
    if i == 0 then break
    i := i - 1
    match tb.afe[i]! with
    | none => return none
    | some e => if tb.dom[e]!.is nm then return some (i, e)
  return none

def reconstructAfe : P Unit := do
  let tb ← get
  let n := tb.afe.size
  if n == 0 then return
  match tb.afe[n - 1]! with
  | none => return
  | some e =>
    if tb.stack.contains e then return
    let mut i := n - 1
    for _ in [0:n] do
      if i == 0 then break
      match tb.afe[i - 1]! with
      | none => break
      | some e2 => if tb.stack.contains e2 then break else i := i - 1
    for k in [i:n] do
      match (← get).afe[k]! with
      | none => pure ()
      | some e3 =>
        let nd := (← get).dom[e3]!
        let id ← insertElement nd.ns nd.name nd.attrs
        modify fun tb => { tb with afe := tb.afe.set! k (some id) }

/-- "Any other end tag" of the in body mode. -/
def anyOtherEnd (name : String) : P Unit := do
  let tb ← get
  let mut i := tb.stack.size
  for _ in [0:tb.stack.size] do
    if i == 0 then break
    i := i - 1
    let id := tb.stack[i]!
    let n := tb.dom[id]!
    if n.is name then
      genImplied false name
      if (← get).stack.back? != some id then perr "end-tag-mismatch"
      popUntilId id
      return
    else if isSpecial n then
      perr "unexpected-end-tag"
      return

def cloneEl (id : Nat) : P Nat := do
  let n ← getN id
  newNode { kind := .elem, ns := n.ns, name := n.name, attrs := n.attrs }

/-- The adoption agency algorithm (§13.2.6.4.7). -/
def adoption (subject : String) : P Unit := do
  let tb0 ← get
  let cn := tb0.dom[tb0.stack.back?.getD 0]!
  if cn.is subject && !(tb0.afe.contains tb0.stack.back?) then
    popCur
    return
  for _ in [0:8] do
    let tb ← get
    match afeFind tb subject with
    | none => anyOtherEnd subject; return
    | some (feA, fe) =>
    match tb.stack.findIdx? (· == fe) with
    | none =>
      perr "adoption-formatting-element-not-open"
      modify fun tb => { tb with afe := arrRemove tb.afe feA }
      return
    | some feS =>
    -- in scope?
    let mut inScope := true
    for j in [feS + 1:tb.stack.size] do
      if defaultBoundary tb.dom[tb.stack[j]!]! then inScope := false
    if !inScope then perr "adoption-formatting-element-not-in-scope"; return
    if tb.stack.back? != some fe then perr "adoption-formatting-element-not-current"
    let mut fbS : Option Nat := none
    for j in [feS + 1:tb.stack.size] do
      if fbS.isNone && isSpecial tb.dom[tb.stack[j]!]! then fbS := some j
    match fbS with
    | none =>
      popUntilId fe
      modify fun tb => { tb with afe := tb.afe.filter (· != some fe) }
      return
    | some fbi =>
    let fb := tb.stack[fbi]!
    let common := tb.stack[feS - 1]!
    let mut bookmark := feA
    let mut nodeIdx := fbi
    let mut last := fb
    let mut counter := 0
    for _ in [0:tb.stack.size + 1] do
      counter := counter + 1
      if nodeIdx == 0 then break
      nodeIdx := nodeIdx - 1
      let st ← get
      let nodeId := st.stack[nodeIdx]!
      if nodeId == fe then break
      let afeIdx := st.afe.findIdx? (· == some nodeId)
      if counter > 3 then
        match afeIdx with
        | some k =>
          modify fun tb => { tb with afe := arrRemove tb.afe k }
          if k < bookmark then bookmark := bookmark - 1
        | none => pure ()
      let afeIdx := (← get).afe.findIdx? (· == some nodeId)
      match afeIdx with
      | none => modify fun tb => { tb with stack := arrRemove tb.stack nodeIdx }
      | some k =>
        let nw ← cloneEl nodeId
        modify fun tb => { tb with afe := tb.afe.set! k (some nw), stack := tb.stack.set! nodeIdx nw }
        if last == fb then bookmark := k + 1
        detach last
        insertAt nw none last
        last := nw
    detach last
    let (par, before) ← appropriatePlace (some common)
    insertAt par before last
    let nw ← cloneEl fe
    let fbn ← getN fb
    for k in fbn.kids do
      detach k
      insertAt nw none k
    insertAt fb none nw
    -- list of active formatting elements
    let st ← get
    match st.afe.findIdx? (· == some fe) with
    | some k =>
      let bm := if k < bookmark then bookmark - 1 else bookmark
      modify fun tb => { tb with afe := arrInsert (arrRemove tb.afe k) bm (some nw) }
    | none => modify fun tb => { tb with afe := arrInsert tb.afe (min bookmark tb.afe.size) (some nw) }
    -- stack of open elements
    let st ← get
    match st.stack.findIdx? (· == fe) with
    | some k => modify fun tb => { tb with stack := arrRemove tb.stack k }
    | none => pure ()
    let st ← get
    match st.stack.findIdx? (· == fb) with
    | some k => modify fun tb => { tb with stack := arrInsert tb.stack (k + 1) nw }
    | none => pure ()

/-! ## Reset the insertion mode -/

def resetMode : P Unit := do
  let tb ← get
  let n := tb.stack.size
  let mut m : Mode := .inBody
  for k in [0:n] do
    let i := n - 1 - k
    let last := (i == 0)
    let nd := tb.dom[tb.stack[i]!]!
    let r : Option Mode :=
      if nd.is "select" then
        some (Id.run do
          let mut res := Mode.inSelect
          let mut j := i
          for _ in [0:i] do
            if j == 0 then break
            j := j - 1
            let a := tb.dom[tb.stack[j]!]!
            if a.is "template" then break
            if a.is "table" then
              res := .inSelectInTable
              break
          return res)
      else if (nd.is "td" || nd.is "th") && !last then some .inCell
      else if nd.is "tr" then some .inRow
      else if nd.isAny ["tbody", "thead", "tfoot"] then some .inTableBody
      else if nd.is "caption" then some .inCaption
      else if nd.is "colgroup" then some .inColumnGroup
      else if nd.is "table" then some .inTable
      else if nd.is "template" then some (tb.tmodes.back?.getD .inTemplate)
      else if nd.is "head" && !last then some .inHead
      else if nd.is "body" then some .inBody
      else if nd.is "frameset" then some .inFrameset
      else if nd.is "html" then some (if tb.headPtr.isNone then .beforeHead else .afterHead)
      else none
    match r with
    | some mm =>
      m := mm
      break
    | none => pure ()
  setMode m

/-! ## Foreign content tables -/

def svgTagNames : List String :=
  ["altGlyph", "altGlyphDef", "altGlyphItem", "animateColor", "animateMotion", "animateTransform", "clipPath",
   "feBlend", "feColorMatrix", "feComponentTransfer", "feComposite", "feConvolveMatrix", "feDiffuseLighting",
   "feDisplacementMap", "feDistantLight", "feDropShadow", "feFlood", "feFuncA", "feFuncB", "feFuncG", "feFuncR",
   "feGaussianBlur", "feImage", "feMerge", "feMergeNode", "feMorphology", "feOffset", "fePointLight",
   "feSpecularLighting", "feSpotLight", "feTile", "feTurbulence", "foreignObject", "glyphRef", "linearGradient",
   "radialGradient", "textPath"]

def svgAttrNames : List String :=
  ["attributeName", "attributeType", "baseFrequency", "baseProfile", "calcMode", "clipPathUnits",
   "diffuseConstant", "edgeMode", "filterUnits", "glyphRef", "gradientTransform", "gradientUnits",
   "kernelMatrix", "kernelUnitLength", "keyPoints", "keySplines", "keyTimes", "lengthAdjust",
   "limitingConeAngle", "markerHeight", "markerUnits", "markerWidth", "maskContentUnits", "maskUnits",
   "numOctaves", "pathLength", "patternContentUnits", "patternTransform", "patternUnits", "pointsAtX",
   "pointsAtY", "pointsAtZ", "preserveAlpha", "preserveAspectRatio", "primitiveUnits", "refX", "refY",
   "repeatCount", "repeatDur", "requiredExtensions", "requiredFeatures", "specularConstant",
   "specularExponent", "spreadMethod", "startOffset", "stdDeviation", "stitchTiles", "surfaceScale",
   "systemLanguage", "tableValues", "targetX", "targetY", "textLength", "viewBox", "viewTarget",
   "xChannelSelector", "yChannelSelector", "zoomAndPan"]

def adjustName (tbl : List String) (n : String) : String := (tbl.find? (fun s => lowerStr s == n)).getD n

def fontBreakoutAttr (attrs : List (String × String)) : Bool :=
  attrs.any (fun a => a.1 == "color" || a.1 == "face" || a.1 == "size")

def breakoutTags : List String :=
  ["b", "big", "blockquote", "body", "br", "center", "code", "dd", "div", "dl", "dt", "em", "embed", "h1", "h2",
   "h3", "h4", "h5", "h6", "head", "hr", "i", "img", "li", "listing", "menu", "meta", "nobr", "ol", "p", "pre",
   "ruby", "s", "small", "span", "strong", "strike", "sub", "sup", "table", "tt", "u", "ul", "var"]

/-! ## Insertion modes -/

def mergeAttrs (id : Nat) (attrs : List (String × String)) : P Unit :=
  modN id fun n => { n with attrs := attrs.foldl (fun a x => if a.any (·.1 == x.1) then a else a.push x) n.attrs }

def genericRaw (name : String) (attrs : List (String × String)) (st : TS) : P Unit := do
  let _ ← insertHtml name attrs
  modify fun tb => { tb with tk := { tb.tk with st }, orig := tb.mode, mode := .text }

def setAck : P Unit := modify fun tb => { tb with ack := true }

def quirkyPublic (p : String) : Bool :=
  ["-//w3o//dtd w3 html strict 3.0//", "-//w3c//dtd html 3.2", "-//ietf//dtd html", "-//netscape comm. corp.//dtd html",
   "-//microsoft//dtd internet explorer", "-//sun microsystems corp.//dtd hotjava", "-//softquad", "-//spyglass//dtd html 2.0 extended//",
   "-//as//dtd html 3.0 aswedit + extensions//", "-//advasoft ltd//dtd html 3.0 aswedit + extensions//"].any (fun x => p.startsWith x)
  || p == "html" || p == "-//w3o//dtd w3 html strict 3.0//en//" || p == "-/w3c/dtd html 4.0 transitional/en"

def initialH (tok : Token) : P Act := do
  match tok with
  | .char c =>
    if isTreeWs c then return .done else
    modify fun tb => { tb with quirks := true }
    perr "expected-doctype-but-got-chars"
    setMode .beforeHtml
    return .reprocess
  | .comment d => insertComment d (some 0); return .done
  | .doctype name pub sys fq =>
    if name != some "html" || pub.isSome || (sys.isSome && sys != some "about:legacy-compat") then
      perr "unexpected-doctype"
    let q := fq || name != some "html" || (pub.any (fun p => quirkyPublic (lowerStr p)))
      || (pub.any (fun p => sys.isNone && (lowerStr p).startsWith "-//w3c//dtd html 4.01 transitional//"))
    modify fun tb => { tb with quirks := q }
    setMode .beforeHtml
    return .done
  | _ =>
    modify fun tb => { tb with quirks := true }
    perr "expected-doctype-but-got-other"
    setMode .beforeHtml
    return .reprocess

def beforeHtmlH (tok : Token) : P Act := do
  let anything : P Act := do
    let _ ← insertHtml "html"
    setMode .beforeHead
    return .reprocess
  match tok with
  | .doctype .. => perr "unexpected-doctype"; return .done
  | .comment d => insertComment d (some 0); return .done
  | .char c => if isTreeWs c then return .done else anything
  | .startTag "html" attrs _ =>
    let _ ← insertHtml "html" attrs
    setMode .beforeHead
    return .done
  | .endTag n =>
    if ["head", "body", "html", "br"].contains n then anything
    else perr "unexpected-end-tag"; return .done
  | _ => anything

def beforeHeadH (tok : Token) : P Act := do
  let anything : P Act := do
    let id ← insertHtml "head"
    modify fun tb => { tb with headPtr := some id }
    setMode .inHead
    return .reprocess
  match tok with
  | .char c => if isTreeWs c then return .done else anything
  | .comment d => insertComment d; return .done
  | .doctype .. => perr "unexpected-doctype"; return .done
  | .startTag "html" _ _ => return .via .inBody
  | .startTag "head" attrs _ =>
    let id ← insertHtml "head" attrs
    modify fun tb => { tb with headPtr := some id }
    setMode .inHead
    return .done
  | .endTag n =>
    if ["head", "body", "html", "br"].contains n then anything
    else perr "unexpected-end-tag"; return .done
  | _ => anything

def inHeadH (tok : Token) : P Act := do
  let anything : P Act := do
    popCur
    setMode .afterHead
    return .reprocess
  match tok with
  | .char c => if isTreeWs c then insertChar c; return .done else anything
  | .comment d => insertComment d; return .done
  | .doctype .. => perr "unexpected-doctype"; return .done
  | .startTag n attrs _ =>
    if n == "html" then return .via .inBody
    else if ["base", "basefont", "bgsound", "link", "meta"].contains n then
      let _ ← insertHtml n attrs
      popCur
      setAck
      return .done
    else if n == "title" then genericRaw n attrs .rcdata; return .done
    else if n == "noscript" then
      let _ ← insertHtml n attrs
      setMode .inHeadNoscript
      return .done
    else if n == "noframes" || n == "style" then genericRaw n attrs .rawtext; return .done
    else if n == "script" then genericRaw n attrs .scriptData; return .done
    else if n == "template" then
      let _ ← insertHtml n attrs
      modify fun tb => { tb with afe := tb.afe.push none, framesetOk := false, mode := .inTemplate,
                                  tmodes := tb.tmodes.push .inTemplate }
      return .done
    else if n == "head" then perr "unexpected-head"; return .done
    else anything
  | .endTag n =>
    if n == "head" then
      popCur
      setMode .afterHead
      return .done
    else if n == "template" then
      if !(← hasOnStack (·.is "template")) then perr "unexpected-end-tag"; return .done
      genImplied true
      if !(← curNode).is "template" then perr "unclosed-element-in-template"
      popUntil (·.is "template")
      clearAfeToMarker
      modify fun tb => { tb with tmodes := tb.tmodes.pop }
      resetMode
      return .done
    else if n == "body" || n == "html" || n == "br" then anything
    else perr "unexpected-end-tag"; return .done
  | _ => anything

def inHeadNoscriptH (tok : Token) : P Act := do
  let anything : P Act := do
    perr "unexpected-token-in-noscript"
    popCur
    setMode .inHead
    return .reprocess
  match tok with
  | .doctype .. => perr "unexpected-doctype"; return .done
  | .startTag "html" _ _ => return .via .inBody
  | .endTag "noscript" => popCur; setMode .inHead; return .done
  | .char c => if isTreeWs c then return .via .inHead else anything
  | .comment _ => return .via .inHead
  | .startTag n _ _ =>
    if ["basefont", "bgsound", "link", "meta", "noframes", "style"].contains n then return .via .inHead
    else if n == "head" || n == "noscript" then perr "unexpected-start-tag"; return .done
    else anything
  | .endTag n => if n == "br" then anything else perr "unexpected-end-tag"; return .done
  | _ => anything

def afterHeadH (tok : Token) : P Act := do
  let anything : P Act := do
    let _ ← insertHtml "body"
    setMode .inBody
    return .reprocess
  match tok with
  | .char c => if isTreeWs c then insertChar c; return .done else anything
  | .comment d => insertComment d; return .done
  | .doctype .. => perr "unexpected-doctype"; return .done
  | .startTag n attrs _ =>
    if n == "html" then return .via .inBody
    else if n == "body" then
      let _ ← insertHtml "body" attrs
      modify fun tb => { tb with framesetOk := false, mode := .inBody }
      return .done
    else if n == "frameset" then
      let _ ← insertHtml "frameset" attrs
      setMode .inFrameset
      return .done
    else if ["base", "basefont", "bgsound", "link", "meta", "noframes", "script", "style", "template", "title"].contains n then
      perr "unexpected-start-tag-in-head"
      let tb ← get
      match tb.headPtr with
      | none => return .done
      | some h =>
        modify fun tb => { tb with stack := tb.stack.push h }
        let act ← inHeadH tok
        -- act is .done for these tags except `genericRaw`, which already set the mode
        modify fun tb => { tb with stack := tb.stack.filter (· != h) }
        let _ := act
        return .done
    else if n == "head" then perr "unexpected-head"; return .done
    else anything
  | .endTag n =>
    if n == "template" then return .via .inHead
    else if n == "body" || n == "html" || n == "br" then anything
    else perr "unexpected-end-tag"; return .done
  | _ => anything

def textH (tok : Token) : P Act := do
  match tok with
  | .char c => insertChar c; return .done
  | .eof =>
    perr "eof-in-text"
    popCur
    modify fun tb => { tb with mode := tb.orig }
    return .reprocess
  | .endTag _ =>
    popCur
    modify fun tb => { tb with mode := tb.orig }
    return .done
  | _ => return .done

def allowedAtEnd : List String :=
  ["dd", "dt", "li", "optgroup", "option", "p", "rb", "rp", "rt", "rtc", "tbody", "td", "tfoot", "th", "thead", "tr",
   "body", "html"]

def checkUnclosed : P Unit := do
  if ← hasOnStack (fun n => !(n.isAny allowedAtEnd)) then perr "unclosed-elements"

def isVoidInBody (n : String) : Bool := ["area", "br", "embed", "img", "keygen", "wbr"].contains n

def inBodyH (tok : Token) : P Act := do
  match tok with
  | .char c =>
    if c == '\x00' then perr "unexpected-null-character"; return .done
    reconstructAfe
    insertChar c
    if !isTreeWs c then modify fun tb => { tb with framesetOk := false }
    return .done
  | .comment d => insertComment d; return .done
  | .doctype .. => perr "unexpected-doctype"; return .done
  | .eof =>
    let tb ← get
    if !tb.tmodes.isEmpty then return .via .inTemplate
    checkUnclosed
    modify fun tb => { tb with done := true }
    return .done
  | .startTag n0 attrs sc =>
    let n := if n0 == "image" then "img" else n0
    if n0 == "image" then perr "image-start-tag"
    if n == "html" then
      perr "unexpected-html-start-tag"
      if !(← hasOnStack (·.is "template")) then
        let tb ← get
        match tb.stack[0]? with
        | some h => mergeAttrs h attrs
        | none => pure ()
      return .done
    else if ["base", "basefont", "bgsound", "link", "meta", "noframes", "script", "style", "template", "title"].contains n then
      return .via .inHead
    else if n == "body" then
      perr "unexpected-body-start-tag"
      let tb ← get
      match tb.stack[1]? with
      | some b =>
        if tb.dom[b]!.is "body" && !(← hasOnStack (·.is "template")) then
          modify fun tb => { tb with framesetOk := false }
          mergeAttrs b attrs
      | none => pure ()
      return .done
    else if n == "frameset" then
      perr "unexpected-frameset-start-tag"
      let tb ← get
      match tb.stack[1]? with
      | some b =>
        if tb.dom[b]!.is "body" && tb.framesetOk then
          detach b
          modify fun tb => { tb with stack := tb.stack.extract 0 1 }
          let _ ← insertHtml "frameset" attrs
          setMode .inFrameset
      | none => pure ()
      return .done
    else if ["address", "article", "aside", "blockquote", "center", "details", "dialog", "dir", "div", "dl",
        "fieldset", "figcaption", "figure", "footer", "header", "hgroup", "main", "menu", "nav", "ol", "p",
        "search", "section", "summary", "ul"].contains n then
      closeP
      let _ ← insertHtml n attrs
      return .done
    else if ["h1", "h2", "h3", "h4", "h5", "h6"].contains n then
      closeP
      if (← curNode).isAny ["h1", "h2", "h3", "h4", "h5", "h6"] then
        perr "nested-heading"
        popCur
      let _ ← insertHtml n attrs
      return .done
    else if n == "pre" || n == "listing" then
      closeP
      let _ ← insertHtml n attrs
      modify fun tb => { tb with skipLF := true, framesetOk := false }
      return .done
    else if n == "form" then
      let tb ← get
      if tb.formPtr.isSome && !(← hasOnStack (·.is "template")) then
        perr "unexpected-form-start-tag"
        return .done
      closeP
      let id ← insertHtml n attrs
      if !(← hasOnStack (·.is "template")) then modify fun tb => { tb with formPtr := some id }
      return .done
    else if n == "li" || n == "dd" || n == "dt" then
      modify fun tb => { tb with framesetOk := false }
      let tb ← get
      let mut i := tb.stack.size
      for _ in [0:tb.stack.size] do
        if i == 0 then break
        i := i - 1
        let nd := tb.dom[tb.stack[i]!]!
        let hit := if n == "li" then nd.is "li" else nd.is "dd" || nd.is "dt"
        if hit then
          genImplied false nd.name
          if (← curNode).name != nd.name then perr "unclosed-element-before-list-item"
          popUntil (·.is nd.name)
          break
        else if isSpecial nd && !nd.isAny ["address", "div", "p"] then break
      closeP
      let _ ← insertHtml n attrs
      return .done
    else if n == "plaintext" then
      closeP
      let _ ← insertHtml n attrs
      modify fun tb => { tb with tk := { tb.tk with st := .plaintext } }
      return .done
    else if n == "button" then
      if ← hasNamed "button" .default then
        perr "nested-button"
        genImplied
        popUntil (·.is "button")
      reconstructAfe
      let _ ← insertHtml n attrs
      modify fun tb => { tb with framesetOk := false }
      return .done
    else if n == "a" then
      let tb ← get
      match afeFind tb "a" with
      | some (_, e) =>
        perr "nested-a"
        adoption "a"
        modify fun tb => { tb with afe := tb.afe.filter (· != some e), stack := tb.stack.filter (· != e) }
      | none => pure ()
      reconstructAfe
      let id ← insertHtml n attrs
      afePush id
      return .done
    else if ["b", "big", "code", "em", "font", "i", "s", "small", "strike", "strong", "tt", "u"].contains n then
      reconstructAfe
      let id ← insertHtml n attrs
      afePush id
      return .done
    else if n == "nobr" then
      reconstructAfe
      if ← hasNamed "nobr" .default then
        perr "nested-nobr"
        adoption "nobr"
        reconstructAfe
      let id ← insertHtml n attrs
      afePush id
      return .done
    else if n == "applet" || n == "marquee" || n == "object" then
      reconstructAfe
      let _ ← insertHtml n attrs
      modify fun tb => { tb with afe := tb.afe.push none, framesetOk := false }
      return .done
    else if n == "table" then
      if !(← get).quirks then closeP
      let _ ← insertHtml n attrs
      modify fun tb => { tb with framesetOk := false, mode := .inTable }
      return .done
    else if isVoidInBody n then
      reconstructAfe
      let _ ← insertHtml n attrs
      popCur
      setAck
      modify fun tb => { tb with framesetOk := false }
      return .done
    else if n == "input" then
      reconstructAfe
      let _ ← insertHtml n attrs
      popCur
      setAck
      if !(attrs.any (fun a => a.1 == "type" && lowerStr a.2 == "hidden")) then
        modify fun tb => { tb with framesetOk := false }
      return .done
    else if n == "param" || n == "source" || n == "track" then
      let _ ← insertHtml n attrs
      popCur
      setAck
      return .done
    else if n == "hr" then
      closeP
      let _ ← insertHtml n attrs
      popCur
      setAck
      modify fun tb => { tb with framesetOk := false }
      return .done
    else if n == "textarea" then
      let _ ← insertHtml n attrs
      modify fun tb => { tb with skipLF := true, framesetOk := false, tk := { tb.tk with st := .rcdata },
                                  orig := tb.mode, mode := .text }
      return .done
    else if n == "xmp" then
      closeP
      reconstructAfe
      modify fun tb => { tb with framesetOk := false }
      genericRaw n attrs .rawtext
      return .done
    else if n == "iframe" then
      modify fun tb => { tb with framesetOk := false }
      genericRaw n attrs .rawtext
      return .done
    else if n == "noembed" then genericRaw n attrs .rawtext; return .done
    else if n == "select" then
      reconstructAfe
      let _ ← insertHtml n attrs
      let tb ← get
      let m := if [Mode.inTable, .inCaption, .inTableBody, .inRow, .inCell].contains tb.mode then Mode.inSelectInTable else .inSelect
      modify fun tb => { tb with framesetOk := false, mode := m }
      return .done
    else if n == "optgroup" || n == "option" then
      if (← curNode).is "option" then popCur
      reconstructAfe
      let _ ← insertHtml n attrs
      return .done
    else if n == "rb" || n == "rtc" then
      if ← hasNamed "ruby" .default then
        genImplied
        if !(← curNode).is "ruby" then perr "unclosed-in-ruby"
      let _ ← insertHtml n attrs
      return .done
    else if n == "rp" || n == "rt" then
      if ← hasNamed "ruby" .default then
        genImplied false "rtc"
        if !(← curNode).isAny ["ruby", "rtc"] then perr "unclosed-in-ruby"
      let _ ← insertHtml n attrs
      return .done
    else if n == "math" || n == "svg" then
      reconstructAfe
      let ns := if n == "math" then NS.math else NS.svg
      let ats := if n == "math" then attrs.map (fun a => (if a.1 == "definitionurl" then "definitionURL" else a.1, a.2))
        else attrs.map (fun a => (adjustName svgAttrNames a.1, a.2))
      let _ ← insertElement ns n ats.toArray
      if sc then
        popCur
        setAck
      return .done
    else if ["caption", "col", "colgroup", "frame", "head", "tbody", "td", "tfoot", "th", "thead", "tr"].contains n then
      perr "unexpected-start-tag"
      return .done
    else
      reconstructAfe
      let _ ← insertHtml n attrs
      return .done
  | .endTag n =>
    if n == "body" then
      if !(← hasNamed "body" .default) then perr "unexpected-end-tag"; return .done
      checkUnclosed
      setMode .afterBody
      return .done
    else if n == "html" then
      if !(← hasNamed "body" .default) then perr "unexpected-end-tag"; return .done
      checkUnclosed
      setMode .afterBody
      return .reprocess
    else if n == "template" then return .via .inHead
    else if ["address", "article", "aside", "blockquote", "button", "center", "details", "dialog", "dir", "div",
        "dl", "fieldset", "figcaption", "figure", "footer", "header", "hgroup", "listing", "main", "menu", "nav",
        "ol", "pre", "search", "section", "summary", "ul"].contains n then
      if !(← hasNamed n .default) then perr "unexpected-end-tag"; return .done
      genImplied
      if !(← curNode).is n then perr "end-tag-mismatch"
      popUntil (·.is n)
      return .done
    else if n == "form" then
      if !(← hasOnStack (·.is "template")) then
        let tb ← get
        let node := tb.formPtr
        modify fun tb => { tb with formPtr := none }
        match node with
        | none => perr "unexpected-end-tag"; return .done
        | some f =>
          let inScope ← hasScope (fun _ => false) .default
          let _ := inScope
          -- the form element must be in scope
          let tb ← get
          let mut ok := false
          let mut i := tb.stack.size
          for _ in [0:tb.stack.size] do
            if i == 0 then break
            i := i - 1
            if tb.stack[i]! == f then
              ok := true
              break
            if defaultBoundary tb.dom[tb.stack[i]!]! then break
          if !ok then perr "unexpected-end-tag"; return .done
          genImplied
          if tb.stack.back? != some f then perr "end-tag-mismatch"
          modify fun tb => { tb with stack := tb.stack.filter (· != f) }
          return .done
      else
        if !(← hasNamed "form" .default) then perr "unexpected-end-tag"; return .done
        genImplied
        if !(← curNode).is "form" then perr "end-tag-mismatch"
        popUntil (·.is "form")
        return .done
    else if n == "p" then
      if !(← hasNamed "p" .button) then
        perr "unexpected-end-tag-p"
        let _ ← insertHtml "p"
        pure ()
      closeP
      return .done
    else if n == "li" then
      if !(← hasNamed "li" .listItem) then perr "unexpected-end-tag"; return .done
      genImplied false "li"
      if !(← curNode).is "li" then perr "end-tag-mismatch"
      popUntil (·.is "li")
      return .done
    else if n == "dd" || n == "dt" then
      if !(← hasNamed n .default) then perr "unexpected-end-tag"; return .done
      genImplied false n
      if !(← curNode).is n then perr "end-tag-mismatch"
      popUntil (·.is n)
      return .done
    else if ["h1", "h2", "h3", "h4", "h5", "h6"].contains n then
      if !(← hasScope (·.isAny ["h1", "h2", "h3", "h4", "h5", "h6"]) .default) then
        perr "unexpected-end-tag"
        return .done
      genImplied
      if !(← curNode).is n then perr "end-tag-mismatch"
      popUntil (·.isAny ["h1", "h2", "h3", "h4", "h5", "h6"])
      return .done
    else if ["a", "b", "big", "code", "em", "font", "i", "nobr", "s", "small", "strike", "strong", "tt", "u"].contains n then
      adoption n
      return .done
    else if n == "applet" || n == "marquee" || n == "object" then
      if !(← hasNamed n .default) then perr "unexpected-end-tag"; return .done
      genImplied
      if !(← curNode).is n then perr "end-tag-mismatch"
      popUntil (·.is n)
      clearAfeToMarker
      return .done
    else if n == "br" then
      perr "end-tag-br"
      reconstructAfe
      let _ ← insertHtml "br"
      popCur
      modify fun tb => { tb with framesetOk := false }
      return .done
    else
      anyOtherEnd n
      return .done

def foreignH (tok : Token) : P Act := do
  match tok with
  | .char c =>
    if c == '\x00' then
      perr "unexpected-null-character"
      insertChar '�'
    else
      insertChar c
      if !isTreeWs c then modify fun tb => { tb with framesetOk := false }
    return .done
  | .comment d => insertComment d; return .done
  | .doctype .. => perr "unexpected-doctype"; return .done
  | .startTag n attrs sc =>
    if breakoutTags.contains n || (n == "font" && fontBreakoutAttr attrs) then
      perr "unexpected-html-element-in-foreign-content"
      for _ in [0:(← get).stack.size] do
        let tb ← get
        match tb.stack.back? with
        | none => break
        | some i =>
          let nd := tb.dom[i]!
          if nd.ns == .html || mathTextIP nd || htmlIP nd then break
          popCur
      return .reprocess
    else
      let cn ← curNode
      let ns := cn.ns
      let name := if ns == .svg then adjustName svgTagNames n else n
      let ats := if ns == .svg then attrs.map (fun a => (adjustName svgAttrNames a.1, a.2))
        else attrs.map (fun a => (if a.1 == "definitionurl" then "definitionURL" else a.1, a.2))
      let _ ← insertElement ns name ats.toArray
      if sc then
        popCur
        setAck
      return .done
  | .endTag n =>
    let tb ← get
    let top := tb.dom[tb.stack.back?.getD 0]!
    if top.ns == .svg && top.name == "script" && n == "script" then
      popCur
      return .done
    if lowerStr top.name != n then perr "end-tag-mismatch"
    let mut i := tb.stack.size
    for _ in [0:tb.stack.size] do
      if i == 0 then break
      i := i - 1
      if i == 0 then return .done
      let nd := tb.dom[tb.stack[i]!]!
      if lowerStr nd.name == n then
        popUntilId tb.stack[i]!
        return .done
      let below := tb.dom[tb.stack[i - 1]!]!
      if below.ns == .html then return .via tb.mode
    return .done
  | .eof => return .done

def tableStartContext : List String := ["table", "template", "html"]

def inTableH (tok : Token) : P Act := do
  let anything : P Act := do
    perr "foster-parenting"
    modify fun tb => { tb with foster := true }
    let a ← inBodyH tok
    modify fun tb => { tb with foster := false }
    return a
  match tok with
  | .char _ =>
    if (← curNode).isAny ["table", "tbody", "template", "tfoot", "thead", "tr"] then
      modify fun tb => { tb with pend := #[], orig := tb.mode, mode := .inTableText }
      return .reprocess
    else anything
  | .comment d => insertComment d; return .done
  | .doctype .. => perr "unexpected-doctype"; return .done
  | .startTag n attrs _ =>
    if n == "caption" then
      clearToContext ["table"]
      modify fun tb => { tb with afe := tb.afe.push none }
      let _ ← insertHtml n attrs
      setMode .inCaption
      return .done
    else if n == "colgroup" then
      clearToContext ["table"]
      let _ ← insertHtml n attrs
      setMode .inColumnGroup
      return .done
    else if n == "col" then
      clearToContext ["table"]
      let _ ← insertHtml "colgroup"
      setMode .inColumnGroup
      return .reprocess
    else if n == "tbody" || n == "tfoot" || n == "thead" then
      clearToContext ["table"]
      let _ ← insertHtml n attrs
      setMode .inTableBody
      return .done
    else if n == "td" || n == "th" || n == "tr" then
      clearToContext ["table"]
      let _ ← insertHtml "tbody"
      setMode .inTableBody
      return .reprocess
    else if n == "table" then
      perr "unexpected-table-in-table"
      if !(← hasNamed "table" .table) then return .done
      popUntil (·.is "table")
      resetMode
      return .reprocess
    else if n == "style" || n == "script" || n == "template" then return .via .inHead
    else if n == "input" then
      if attrs.any (fun a => a.1 == "type" && lowerStr a.2 == "hidden") then
        perr "unexpected-hidden-input-in-table"
        let _ ← insertHtml n attrs
        popCur
        setAck
        return .done
      else anything
    else if n == "form" then
      perr "unexpected-form-in-table"
      if (← hasOnStack (·.is "template")) || (← get).formPtr.isSome then return .done
      let id ← insertHtml n attrs
      modify fun tb => { tb with formPtr := some id }
      popCur
      return .done
    else anything
  | .endTag n =>
    if n == "table" then
      if !(← hasNamed "table" .table) then perr "unexpected-end-tag"; return .done
      popUntil (·.is "table")
      resetMode
      return .done
    else if ["body", "caption", "col", "colgroup", "html", "tbody", "td", "tfoot", "th", "thead", "tr"].contains n then
      perr "unexpected-end-tag"
      return .done
    else if n == "template" then return .via .inHead
    else anything
  | .eof => return .via .inBody

def inTableTextH (tok : Token) : P Act := do
  match tok with
  | .char c =>
    if c == '\x00' then perr "unexpected-null-character"
    else modify fun tb => { tb with pend := tb.pend.push c }
    return .done
  | _ =>
    let tb ← get
    if tb.pend.any (fun c => !isTreeWs c) then
      perr "foster-parenting-text"
      modify fun tb => { tb with foster := true }
      for c in tb.pend do
        reconstructAfe
        insertChar c
        modify fun tb => { tb with framesetOk := false }
      modify fun tb => { tb with foster := false }
    else
      for c in tb.pend do insertChar c
    modify fun tb => { tb with pend := #[], mode := tb.orig }
    return .reprocess

def inCaptionH (tok : Token) : P Act := do
  let closeCaption : P Bool := do
    if !(← hasNamed "caption" .table) then perr "unexpected-end-tag"; return false
    genImplied
    if !(← curNode).is "caption" then perr "end-tag-mismatch"
    popUntil (·.is "caption")
    clearAfeToMarker
    setMode .inTable
    return true
  match tok with
  | .endTag "caption" => let _ ← closeCaption; return .done
  | .startTag n _ _ =>
    if ["caption", "col", "colgroup", "tbody", "td", "tfoot", "th", "thead", "tr"].contains n then
      return (if ← closeCaption then .reprocess else .done)
    else return .via .inBody
  | .endTag n =>
    if n == "table" then return (if ← closeCaption then .reprocess else .done)
    else if ["body", "col", "colgroup", "html", "tbody", "td", "tfoot", "th", "thead", "tr"].contains n then
      perr "unexpected-end-tag"
      return .done
    else return .via .inBody
  | _ => return .via .inBody

def inColumnGroupH (tok : Token) : P Act := do
  let anything : P Act := do
    if !(← curNode).is "colgroup" then perr "unexpected-token"; return .done
    popCur
    setMode .inTable
    return .reprocess
  match tok with
  | .char c => if isTreeWs c then insertChar c; return .done else anything
  | .comment d => insertComment d; return .done
  | .doctype .. => perr "unexpected-doctype"; return .done
  | .startTag n attrs _ =>
    if n == "html" then return .via .inBody
    else if n == "col" then
      let _ ← insertHtml n attrs
      popCur
      setAck
      return .done
    else if n == "template" then return .via .inHead
    else anything
  | .endTag n =>
    if n == "colgroup" then
      if !(← curNode).is "colgroup" then perr "unexpected-end-tag"; return .done
      popCur
      setMode .inTable
      return .done
    else if n == "col" then perr "unexpected-end-tag"; return .done
    else if n == "template" then return .via .inHead
    else anything
  | .eof => return .via .inBody

def inTableBodyH (tok : Token) : P Act := do
  match tok with
  | .startTag n attrs _ =>
    if n == "tr" then
      clearToContext ["tbody", "tfoot", "thead"]
      let _ ← insertHtml n attrs
      setMode .inRow
      return .done
    else if n == "th" || n == "td" then
      perr "unexpected-cell-in-table-body"
      clearToContext ["tbody", "tfoot", "thead"]
      let _ ← insertHtml "tr"
      setMode .inRow
      return .reprocess
    else if ["caption", "col", "colgroup", "tbody", "tfoot", "thead"].contains n then
      if !(← hasScope (·.isAny ["tbody", "thead", "tfoot"]) .table) then perr "unexpected-start-tag"; return .done
      clearToContext ["tbody", "tfoot", "thead"]
      popCur
      setMode .inTable
      return .reprocess
    else return .via .inTable
  | .endTag n =>
    if n == "tbody" || n == "tfoot" || n == "thead" then
      if !(← hasNamed n .table) then perr "unexpected-end-tag"; return .done
      clearToContext ["tbody", "tfoot", "thead"]
      popCur
      setMode .inTable
      return .done
    else if n == "table" then
      if !(← hasScope (·.isAny ["tbody", "thead", "tfoot"]) .table) then perr "unexpected-end-tag"; return .done
      clearToContext ["tbody", "tfoot", "thead"]
      popCur
      setMode .inTable
      return .reprocess
    else if ["body", "caption", "col", "colgroup", "html", "td", "th", "tr"].contains n then
      perr "unexpected-end-tag"
      return .done
    else return .via .inTable
  | _ => return .via .inTable

def inRowH (tok : Token) : P Act := do
  let closeRow : P Bool := do
    if !(← hasNamed "tr" .table) then perr "unexpected-end-tag"; return false
    clearToContext ["tr"]
    popCur
    setMode .inTableBody
    return true
  match tok with
  | .startTag n attrs _ =>
    if n == "th" || n == "td" then
      clearToContext ["tr"]
      let _ ← insertHtml n attrs
      setMode .inCell
      modify fun tb => { tb with afe := tb.afe.push none }
      return .done
    else if ["caption", "col", "colgroup", "tbody", "tfoot", "thead", "tr"].contains n then
      return (if ← closeRow then .reprocess else .done)
    else return .via .inTable
  | .endTag n =>
    if n == "tr" then let _ ← closeRow; return .done
    else if n == "table" then return (if ← closeRow then .reprocess else .done)
    else if n == "tbody" || n == "tfoot" || n == "thead" then
      if !(← hasNamed n .table) then perr "unexpected-end-tag"; return .done
      return (if ← closeRow then .reprocess else .done)
    else if ["body", "caption", "col", "colgroup", "html", "td", "th"].contains n then
      perr "unexpected-end-tag"
      return .done
    else return .via .inTable
  | _ => return .via .inTable

def closeCell : P Unit := do
  genImplied
  if !(← curNode).isAny ["td", "th"] then perr "end-tag-mismatch"
  popUntil (·.isAny ["td", "th"])
  clearAfeToMarker
  setMode .inRow

def inCellH (tok : Token) : P Act := do
  match tok with
  | .endTag n =>
    if n == "td" || n == "th" then
      if !(← hasNamed n .table) then perr "unexpected-end-tag"; return .done
      genImplied
      if !(← curNode).is n then perr "end-tag-mismatch"
      popUntil (·.is n)
      clearAfeToMarker
      setMode .inRow
      return .done
    else if ["body", "caption", "col", "colgroup", "html"].contains n then
      perr "unexpected-end-tag"
      return .done
    else if ["table", "tbody", "tfoot", "thead", "tr"].contains n then
      if !(← hasNamed n .table) then perr "unexpected-end-tag"; return .done
      closeCell
      return .reprocess
    else return .via .inBody
  | .startTag n _ _ =>
    if ["caption", "col", "colgroup", "tbody", "td", "tfoot", "th", "thead", "tr"].contains n then
      if !(← hasScope (·.isAny ["td", "th"]) .table) then perr "unexpected-start-tag"; return .done
      closeCell
      return .reprocess
    else return .via .inBody
  | _ => return .via .inBody

def inSelectH (tok : Token) : P Act := do
  match tok with
  | .char c =>
    if c == '\x00' then perr "unexpected-null-character" else insertChar c
    return .done
  | .comment d => insertComment d; return .done
  | .doctype .. => perr "unexpected-doctype"; return .done
  | .startTag n attrs _ =>
    if n == "html" then return .via .inBody
    else if n == "option" then
      if (← curNode).is "option" then popCur
      let _ ← insertHtml n attrs
      return .done
    else if n == "optgroup" then
      if (← curNode).is "option" then popCur
      if (← curNode).is "optgroup" then popCur
      let _ ← insertHtml n attrs
      return .done
    else if n == "hr" then
      if (← curNode).is "option" then popCur
      if (← curNode).is "optgroup" then popCur
      let _ ← insertHtml n attrs
      popCur
      setAck
      return .done
    else if n == "select" then
      perr "unexpected-select-in-select"
      if !(← hasNamed "select" .select) then return .done
      popUntil (·.is "select")
      resetMode
      return .done
    else if n == "input" || n == "keygen" || n == "textarea" then
      perr "unexpected-input-in-select"
      if !(← hasNamed "select" .select) then return .done
      popUntil (·.is "select")
      resetMode
      return .reprocess
    else if n == "script" || n == "template" then return .via .inHead
    else perr "unexpected-start-tag-in-select"; return .done
  | .endTag n =>
    if n == "optgroup" then
      let tb ← get
      let cur := tb.dom[tb.stack.back?.getD 0]!
      let below := tb.dom[(tb.stack[tb.stack.size - 2]?).getD 0]!
      if cur.is "option" && below.is "optgroup" then popCur
      if (← curNode).is "optgroup" then popCur else perr "unexpected-end-tag"
      return .done
    else if n == "option" then
      if (← curNode).is "option" then popCur else perr "unexpected-end-tag"
      return .done
    else if n == "select" then
      if !(← hasNamed "select" .select) then perr "unexpected-end-tag"; return .done
      popUntil (·.is "select")
      resetMode
      return .done
    else if n == "template" then return .via .inHead
    else perr "unexpected-end-tag-in-select"; return .done
  | .eof => return .via .inBody

def inSelectInTableH (tok : Token) : P Act := do
  let tbl := ["caption", "table", "tbody", "tfoot", "thead", "tr", "td", "th"]
  match tok with
  | .startTag n _ _ =>
    if tbl.contains n then
      perr "unexpected-table-element-in-select"
      popUntil (·.is "select")
      resetMode
      return .reprocess
    else return .via .inSelect
  | .endTag n =>
    if tbl.contains n then
      perr "unexpected-end-tag"
      if !(← hasNamed n .table) then return .done
      popUntil (·.is "select")
      resetMode
      return .reprocess
    else return .via .inSelect
  | _ => return .via .inSelect

def inTemplateH (tok : Token) : P Act := do
  let switch (m : Mode) : P Act := do
    modify fun tb => { tb with tmodes := (tb.tmodes.pop).push m, mode := m }
    return .reprocess
  match tok with
  | .char _ | .comment _ | .doctype .. => return .via .inBody
  | .startTag n _ _ =>
    if ["base", "basefont", "bgsound", "link", "meta", "noframes", "script", "style", "template", "title"].contains n then
      return .via .inHead
    else if ["caption", "colgroup", "tbody", "tfoot", "thead"].contains n then switch .inTable
    else if n == "col" then switch .inColumnGroup
    else if n == "tr" then switch .inTableBody
    else if n == "td" || n == "th" then switch .inRow
    else switch .inBody
  | .endTag n =>
    if n == "template" then return .via .inHead
    else perr "unexpected-end-tag"; return .done
  | .eof =>
    if !(← hasOnStack (·.is "template")) then
      modify fun tb => { tb with done := true }
      return .done
    perr "eof-in-template"
    popUntil (·.is "template")
    clearAfeToMarker
    modify fun tb => { tb with tmodes := tb.tmodes.pop }
    resetMode
    return .reprocess

def afterBodyH (tok : Token) : P Act := do
  match tok with
  | .char c => if isTreeWs c then return .via .inBody else
    perr "unexpected-char-after-body"
    setMode .inBody
    return .reprocess
  | .comment d =>
    let tb ← get
    insertComment d (tb.stack[0]?)
    return .done
  | .doctype .. => perr "unexpected-doctype"; return .done
  | .startTag "html" _ _ => return .via .inBody
  | .endTag "html" => setMode .afterAfterBody; return .done
  | .eof => modify fun tb => { tb with done := true }; return .done
  | _ =>
    perr "unexpected-token-after-body"
    setMode .inBody
    return .reprocess

def afterAfterBodyH (tok : Token) : P Act := do
  match tok with
  | .comment d => insertComment d (some 0); return .done
  | .doctype .. => return .via .inBody
  | .char c => if isTreeWs c then return .via .inBody else
    perr "unexpected-char-after-body"
    setMode .inBody
    return .reprocess
  | .startTag "html" _ _ => return .via .inBody
  | .eof => modify fun tb => { tb with done := true }; return .done
  | _ =>
    perr "unexpected-token-after-body"
    setMode .inBody
    return .reprocess

def inFramesetH (tok : Token) : P Act := do
  match tok with
  | .char c =>
    if isTreeWs c then insertChar c else perr "unexpected-char-in-frameset"
    return .done
  | .comment d => insertComment d; return .done
  | .doctype .. => perr "unexpected-doctype"; return .done
  | .startTag n attrs _ =>
    if n == "html" then return .via .inBody
    else if n == "frameset" then let _ ← insertHtml n attrs; return .done
    else if n == "frame" then
      let _ ← insertHtml n attrs
      popCur
      setAck
      return .done
    else if n == "noframes" then return .via .inHead
    else perr "unexpected-start-tag-in-frameset"; return .done
  | .endTag n =>
    if n == "frameset" then
      if (← get).stack.size ≤ 1 then perr "unexpected-end-tag"; return .done
      popCur
      if !(← curNode).is "frameset" then setMode .afterFrameset
      return .done
    else perr "unexpected-end-tag"; return .done
  | .eof =>
    if (← get).stack.size > 1 then perr "eof-in-frameset"
    modify fun tb => { tb with done := true }
    return .done

def afterFramesetH (tok : Token) : P Act := do
  match tok with
  | .char c =>
    if isTreeWs c then insertChar c else perr "unexpected-char-after-frameset"
    return .done
  | .comment d => insertComment d; return .done
  | .doctype .. => perr "unexpected-doctype"; return .done
  | .startTag n _ _ =>
    if n == "html" then return .via .inBody
    else if n == "noframes" then return .via .inHead
    else perr "unexpected-start-tag"; return .done
  | .endTag n =>
    if n == "html" then setMode .afterAfterFrameset; return .done
    else perr "unexpected-end-tag"; return .done
  | .eof => modify fun tb => { tb with done := true }; return .done

def afterAfterFramesetH (tok : Token) : P Act := do
  match tok with
  | .comment d => insertComment d (some 0); return .done
  | .doctype .. => return .via .inBody
  | .char c => if isTreeWs c then return .via .inBody else perr "unexpected-char"; return .done
  | .startTag n _ _ =>
    if n == "html" then return .via .inBody
    else if n == "noframes" then return .via .inHead
    else perr "unexpected-start-tag"; return .done
  | .eof => modify fun tb => { tb with done := true }; return .done
  | _ => perr "unexpected-token"; return .done

def handler (m : Mode) (tok : Token) : P Act :=
  match m with
  | .initial => initialH tok
  | .beforeHtml => beforeHtmlH tok
  | .beforeHead => beforeHeadH tok
  | .inHead => inHeadH tok
  | .inHeadNoscript => inHeadNoscriptH tok
  | .afterHead => afterHeadH tok
  | .inBody => inBodyH tok
  | .text => textH tok
  | .inTable => inTableH tok
  | .inTableText => inTableTextH tok
  | .inCaption => inCaptionH tok
  | .inColumnGroup => inColumnGroupH tok
  | .inTableBody => inTableBodyH tok
  | .inRow => inRowH tok
  | .inCell => inCellH tok
  | .inSelect => inSelectH tok
  | .inSelectInTable => inSelectInTableH tok
  | .inTemplate => inTemplateH tok
  | .afterBody => afterBodyH tok
  | .inFrameset => inFramesetH tok
  | .afterFrameset => afterFramesetH tok
  | .afterAfterBody => afterAfterBodyH tok
  | .afterAfterFrameset => afterAfterFramesetH tok

/-- The tree construction dispatcher (§13.2.6.1). -/
def useHtmlRules (tb : TB) (tok : Token) : Bool :=
  match tb.stack.back? with
  | none => true
  | some i =>
    let n := tb.dom[i]!
    if n.ns == .html then true
    else match tok with
      | .eof => true
      | .startTag nm _ _ =>
        if mathTextIP n && nm != "mglyph" && nm != "malignmark" then true
        else if n.ns == .math && n.name == "annotation-xml" && nm == "svg" then true
        else htmlIP n
      | .char _ => mathTextIP n || htmlIP n
      | _ => false

def dispatch : Nat → Option Mode → Token → P Unit
  | 0, _, _ => pure ()
  | f + 1, force, tok => do
    let tb ← get
    let act ← match force with
      | some m => handler m tok
      | none => if useHtmlRules tb tok then handler tb.mode tok else foreignH tok
    match act with
    | .done => pure ()
    | .reprocess => dispatch f none tok
    | .via m => dispatch f (some m) tok

/-- Process one token: the LF after `pre`, the self-closing flag. -/
def process (tok : Token) : P Unit := do
  let tb ← get
  if tb.skipLF then
    modify fun tb => { tb with skipLF := false }
    match tok with
    | .char '\n' => return
    | _ => pure ()
  modify fun tb => { tb with ack := false }
  dispatch 32 none tok
  match tok with
  | .startTag _ _ true =>
    if !(← get).ack then perr "non-void-html-element-start-tag-with-trailing-solidus"
  | _ => pure ()

/-! ## Driver and output -/

inductive HNode where
  | element (ns : NS) (name : String) (attrs : List (String × String)) (kids : List HNode)
  | text (s : String)
  | comment (s : String)

structure Parsed where
  children : List HNode
  errors : Array String

def buildTree (dom : Array DNode) : Nat → Nat → List HNode
  | 0, _ => []
  | f + 1, id =>
    let n := dom[id]!
    n.kids.toList.filterMap fun k =>
      let c := dom[k]!
      match c.kind with
      | .text => some (HNode.text c.data)
      | .comment => some (HNode.comment c.data)
      | .elem => some (HNode.element c.ns c.name c.attrs.toList (buildTree dom f k))
      | .doc => none

def runAll : P Unit := do
  let n := (← get).tk.inp.size
  for _ in [0:3 * n + 100] do
    if (← get).done then break
    let tb ← get
    let foreign := match tb.stack.back? with
      | some i => tb.dom[i]!.ns != .html
      | none => false
    let (tok, tk) := ({ tb.tk with foreign }).pull
    set { tb with tk }
    process tok

/-- Parse a whole document (§13.2). -/
def parseHtml (src : String) : Parsed :=
  let inp := normalizeNewlines src
  let tb0 : TB := { tk := { inp }, errs := inputErrors inp }
  let ((), tb) := runAll.run tb0
  { children := buildTree tb.dom (tb.dom.size + 1) 0, errors := tb.errs ++ tb.tk.errs }

end L4Factoidal.HTML
