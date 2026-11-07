import SVG
import Std.Data.HashMap

/- Forgiving front door for the strict SVG reader.

   The strict reader in SVG.lean refuses any document it can not fully draw.
   A browser must instead draw what it can. This pass removes what the strict
   reader refuses, and it records each removal. The reader itself is unchanged,
   so each thing it learns to draw leaves this log with no change here.

   `dropped` is the to-do list. A scene made here is a partial rendering. It
   makes no claim of SVG conformance. -/
namespace NativeSVGForgiving

open L4Factoidal.XML

private def svgURI := "http://www.w3.org/2000/svg"
private def xmlURI := "http://www.w3.org/XML/1998/namespace"
/-- XML nesting limit of this pass; the strict reader stops at 32 groups. -/
private def maxDepth : Nat := 64
/-- Strict parses allowed for one document. Each one is a full reader run. -/
private def maxParses : Nat := 4000

/-- Elements the strict reader reads. Any other element is removed and logged. -/
private def readable := ["svg","g","use","symbol","defs","style","metadata","title","desc",
  "rect","circle","ellipse","line","polygon","polyline","path",
  "linearGradient","radialGradient","stop","solidColor"]
/-- Elements that paint nothing: their content needs no reader support. -/
private def silent := ["title","desc","metadata"]

private def isSpace (s : String) : Bool :=
  s.toList.all (fun c => c == ' ' || c == '\t' || c == '\n' || c == '\r')

/-- `xml:id` is an ID (XML ID 1.0); the strict reader reads only `id`. -/
private def renameId (attrs : List NamespaceAttribute) : List NamespaceAttribute :=
  attrs.map fun a =>
    if a.name.namespace_ == some xmlURI && a.name.localPart == "id"
    then {a with name:={namespace_:=none,localPart:="id"}} else a

private def plainAttr (attrs : List NamespaceAttribute) (key : String) : Option String :=
  (attrs.find? (fun a => a.name.namespace_.isNone && a.name.localPart == key)).map (·.value)
private def mkAttr (key value : String) : NamespaceAttribute :=
  {name:={namespace_:=none,localPart:=key},value}
private def svgElement (tag : String) (attrs : List NamespaceAttribute) (children : List NamespaceNode) : NamespaceNode :=
  .element {namespace_:=some svgURI,localPart:=tag} attrs children

/-! ### SVG fonts and text

   SVG Tiny 1.2 §11: a glyph is path data. Text therefore lowers to `path`
   elements, which the strict reader can already draw. -/

private structure Glyph where
  name : String
  advance : Float
  data : String

structure SVGFont where
  family : String := ""
  unitsPerEm : Float := 1000
  defaultAdvance : Float := 500
  /-- `font-face` ascent and descent, in font units, both as positive depths. -/
  ascent : Float := 800
  descent : Float := 200
  glyphs : Std.HashMap Char Glyph := {}
  kerning : Std.HashMap (String × String) Float := {}
  missing : Glyph := ⟨"",500,""⟩
instance : Inhabited SVGFont := ⟨{}⟩

private def float (source : Option String) (fallback : Float) : Float :=
  match source with
  | none => fallback
  | some s =>
    let s := s.trimAscii.toString
    let s := if s.endsWith "px" then (s.dropEnd 2).toString else s
    match (NativeSVG.number s) with | .ok value => value | .error _ => fallback

private def fontElements : Nat → NamespaceNode → List NamespaceNode
  | 0,_ => []
  | _,.other _ => []
  | fuel+1,node@(.element name _ children) =>
    if name.localPart == "font" then [node] else children.flatMap (fontElements fuel)

private def SVGFont.ofElement (attrs : List NamespaceAttribute) (children : List NamespaceNode) : SVGFont := Id.run do
  let fallback := float (plainAttr attrs "horiz-adv-x") 500
  let mut font : SVGFont := {defaultAdvance:=fallback,missing:=⟨"",fallback,""⟩}
  for child in children do
    let .element name a _ := child | continue
    let advance := float (plainAttr a "horiz-adv-x") fallback
    let data := (plainAttr a "d").getD ""
    match name.localPart with
    | "font-face" => 
      let units := float (plainAttr a "units-per-em") 1000
      font := {font with unitsPerEm:=units,family:=(plainAttr a "font-family").getD "",ascent:=(float (plainAttr a "ascent") (units*0.8)).abs,descent:=(float (plainAttr a "descent") (units*0.2)).abs}
    | "missing-glyph" => font := {font with missing:=⟨"",advance,data⟩}
    | "glyph" =>
      if let some text := plainAttr a "unicode" then
        if let [c] := text.toList then
          font := {font with glyphs:=font.glyphs.insert c ⟨(plainAttr a "glyph-name").getD text,advance,data⟩}
    | "hkern" =>
      let left := (plainAttr a "g1").getD ""
      let right := (plainAttr a "g2").getD ""
      let k := float (plainAttr a "k") 0
      for l in left.splitOn "," do
        for r in right.splitOn "," do
          font := {font with kerning:=font.kerning.insert (l.trimAscii.toString,r.trimAscii.toString) k}
    | _ => pure ()
  return font

/-- Every `font` element of a parsed SVG tree. -/
private def fontsIn (root : NamespaceNode) : List SVGFont :=
  (fontElements maxDepth root).filterMap fun
    | .element _ attrs children => some (SVGFont.ofElement attrs children)
    | _ => none

/-- Read the first `font` element of an SVG document. -/
def SVGFont.parse (xml : String) : Except String SVGFont := do
  match fontsIn (← parseNamespaceView xml) with
  | font::_ => pure font
  | [] => throw "no font element"

private def SVGFont.glyph (font : SVGFont) (c : Char) : Glyph :=
  font.glyphs.getD c font.missing

/-- Attributes of a text element that the strict reader paints with. -/
private def paintKeys := ["fill","stroke","fill-opacity","stroke-opacity","color","display","visibility","opacity"]

private structure TextState where
  size : Float := 16
  anchor : String := "start"
  family : String := ""
  strokeWidth : Float := 1

private def TextState.read (s : TextState) (attrs : List NamespaceAttribute) : TextState :=
  { size := float (plainAttr attrs "font-size") s.size,
    anchor := (plainAttr attrs "text-anchor").getD s.anchor,
    family := (plainAttr attrs "font-family").getD s.family,
    strokeWidth := float (plainAttr attrs "stroke-width") s.strokeWidth }

/-- CSS Fonts: the first named family that is known, else the default font. -/
private def chooseFont (fonts : List SVGFont) (family : String) : Option SVGFont :=
  let names := (family.splitOn ",").map (fun n => (n.trimAscii.toString.replace "'" "").replace "\"" "")
  (names.findSome? (fun name => fonts.find? (·.family == name))).orElse (fun _ => fonts.getLast?)

private structure Run where
  text : String
  size : Float
  strokeWidth : Float
  paint : List NamespaceAttribute
  xs : List Float := []
  ys : List Float := []
  dx : Float := 0
  dy : Float := 0

private def paintOf (attrs : List NamespaceAttribute) : List NamespaceAttribute :=
  attrs.filter fun a => a.name.namespace_.isNone && paintKeys.contains a.name.localPart

private def numberList (attrs : List NamespaceAttribute) (key : String) : List Float :=
  match plainAttr attrs key with
  | none => []
  | some s => ((s.splitOn " ").flatMap (·.splitOn ",") |>.filter (· != "")).map (fun n => float (some n) 0)

/-- Text runs in order. A later unsupported child is logged and skipped. -/
private def textRuns : Nat → TextState → List NamespaceAttribute → NamespaceNode → List Run × List String
  | 0,_,_,_ => ([],[])
  | _,state,paint,.other raw => match raw with
    | .text t | .cdata t => ([{text := t, size := state.size, strokeWidth := state.strokeWidth, paint := paint}],[])
    | _ => ([],[])
  | fuel+1,state,paint,.element name attrs children =>
    if name.localPart != "tspan" then ([],["element in text: " ++ name.localPart]) else
    let inner := state.read attrs
    let results := children.map (textRuns fuel inner (paint ++ paintOf attrs))
    let runs := results.flatMap (·.1)
    let runs := match runs with
      | run::rest =>
        let placed : Run := { run with
          xs := numberList attrs "x"
          ys := numberList attrs "y"
          dx := (numberList attrs "dx").headD 0
          dy := (numberList attrs "dy").headD 0 }
        placed::rest
      | [] => []
    (runs,results.flatMap (·.2))

private def collapse (s : String) : String :=
  let spaced := s.toList.map (fun c => if c == '\n' || c == '\t' || c == '\r' then ' ' else c)
  String.ofList (spaced.foldr (fun c acc => match acc with
    | ' '::_ => if c == ' ' then acc else c::acc
    | _ => c::acc) [])

private def runAdvance (font : SVGFont) (run : Run) : Float :=
  let scale := run.size/font.unitsPerEm
  let (total,_) := run.text.toList.foldl (fun (total,previous) c =>
    let g := font.glyph c
    let kern := (previous.bind (fun (p : Glyph) => font.kerning.get? (p.name,g.name))).getD 0
    (total+(g.advance-kern)*scale,some g)) ((0 : Float),(none : Option Glyph))
  total

/-- Tell each glyph path of a run the bounding box of the whole text, x0 y0 x1 y1. -/
private def markGlyphs (box : Float × Float × Float × Float) : NamespaceNode → NamespaceNode
  | .element name attrs paths =>
    let (x0,y0,x1,y1) := box
    let mark : NamespaceAttribute := {name:={namespace_:=some NativeSVG.internalURI,localPart:=NativeSVG.textBoxAttribute},value:=s!"{x0} {y0} {x1-x0} {y1-y0}"}
    .element name attrs (paths.map fun
      | .element n a c => .element n (a ++ [mark]) c
      | node => node)
  | node => node

/-- Lower one `text` element to a group of glyph paths. -/
private def lowerText (font : SVGFont) (state : TextState) (attrs : List NamespaceAttribute)
    (children : List NamespaceNode) : NamespaceNode × List String := Id.run do
  let state := state.read attrs
  let results := children.map (textRuns maxDepth state [])
  let raw := (results.flatMap (·.1)).map (fun r => {r with text:=collapse r.text})
  -- Default xml:space: no leading or trailing space on the whole text.
  let lastIndex := raw.length-1
  let runs := raw.zipIdx.map fun (r,i) =>
    let text := if i == 0 then r.text.trimAsciiStart.toString else r.text
    {r with text:=if i == lastIndex then text.trimAsciiEnd.toString else text}
  let width := (runs.map (runAdvance font)).foldl (·+·) 0
  let shift := match state.anchor with | "middle" => -width/2 | "end" => -width | _ => 0
  let xs := numberList attrs "x"
  let ys := numberList attrs "y"
  let mut x := xs.headD 0 + (numberList attrs "dx").headD 0 + shift
  let mut y := ys.headD 0 + (numberList attrs "dy").headD 0
  let mut index := 0
  let mut groups : Array NamespaceNode := #[]
  -- SVG Tiny 1.2 §7.11: the bounding box of a text is that of its character cells.
  let mut box : Option (Float × Float × Float × Float) := none
  for run in runs do
    x := x+run.dx
    y := y+run.dy
    if run.size <= 0 then continue
    let scale := run.size/font.unitsPerEm
    let mut paths : Array NamespaceNode := #[]
    let mut previous : Option Glyph := none
    for (c,position) in run.text.toList.zipIdx do
      -- A coordinate list places the characters it covers (SVG Tiny 1.2 §10.5).
      if let some value := run.xs[position]? then x := value
      if let some value := run.ys[position]? then y := value
      if position > 0 || index > 0 then
        if let some value := xs[index]? then x := value
        if let some value := ys[index]? then y := value
      index := index+1
      let g := font.glyph c
      let kern := (previous.bind (fun p => font.kerning.get? (p.name,g.name))).getD 0
      x := x-kern*scale
      if !g.data.isEmpty then
        paths := paths.push (svgElement "path" [mkAttr "d" g.data,mkAttr "stroke-width" (toString (run.strokeWidth/scale)),
          mkAttr "transform" s!"translate({x},{y}) scale({scale},{-scale})"] [])
      let cellTop := y-font.ascent*scale
      let cellBottom := y+font.descent*scale
      let cellRight := x+g.advance*scale
      box := some (match box with
        | none => (x,cellTop,cellRight,cellBottom)
        | some (x0,y0,x1,y1) => (min x0 x,min y0 cellTop,max x1 cellRight,max y1 cellBottom))
      x := x+g.advance*scale
      previous := some g
    groups := groups.push (svgElement "g" run.paint paths.toList)
  let outer := paintOf attrs ++ (attrs.filter (fun a => a.name.namespace_.isNone && a.name.localPart == "transform"))
  let ids := renameId attrs |>.filter (fun a => a.name.namespace_.isNone && a.name.localPart == "id")
  let marked := match box with
    | none => groups.toList
    | some box => groups.toList.map (markGlyphs box)
  return (svgElement "g" (ids ++ outer) marked,results.flatMap (·.2))

/-- SVG Tiny 1.2 §5.8.2: this agent's language is en, and it has no extensions. -/
private def conditionsPass (attrs : List NamespaceAttribute) : Bool :=
  let language := match plainAttr attrs "systemLanguage" with
    | none => true
    | some value => (value.splitOn ",").any fun tag =>
      let tag := tag.trimAscii.toString.toLower
      tag == "en" || tag.startsWith "en-"
  let extensions := match plainAttr attrs "requiredExtensions" with | none => true | some _ => false
  language && extensions

/-- Elements of the tree that have an id, by id; the first one with an id wins. -/
private def idTargets : Nat → NamespaceNode → List (String × NamespaceNode)
  | 0,_ => []
  | _,.other _ => []
  | fuel+1,node@(.element _ attrs children) =>
    ((plainAttr (renameId attrs) "id").toList.map (·,node)) ++ children.flatMap (idTargets fuel)

private def hasElement (tag : String) : Nat → NamespaceNode → Bool
  | 0,_ => false
  | _,.other _ => false
  | fuel+1,.element name _ children => name.localPart == tag || children.any (hasElement tag fuel)

/-- SVG Tiny 1.2 §5.6: an instance inherits from its `use` element. Text lowers
    here, with the font values in force, so a `use` of text must lower its own
    copy. A target with a `use` inside stays with the strict reader, which has
    the cycle check. -/
private def textInstance (targets : Std.HashMap String NamespaceNode) (attrs : List NamespaceAttribute) : Option NamespaceNode := do
  let source ← NativeSVGReferences.href attrs
  if !source.startsWith "#" then none
  let target ← targets.get? (source.drop 1).toString
  let .element name _ _ := target | none
  if !["g","text"].contains name.localPart || !hasElement "text" maxDepth target || hasElement "use" maxDepth target then none
  pure target

/-- Remove foreign and unread elements, stray text and the content of silent
    elements, and lower `text` when a font is known. Returns the new tree and
    one log line for each removal. -/
private def normalise (fonts : List SVGFont) (targets : Std.HashMap String NamespaceNode) : Nat → TextState → Bool → NamespaceNode → Option NamespaceNode × List String
  | 0,_,_,_ => (none,["element: nesting exceeds 64"])
  | _,_,_,.other (.comment c) => (some (.other (.comment c)),[])
  | _,_,keepText,.other raw => match raw with
    | .text t | .cdata t =>
      if keepText || isSpace t then (some (.other raw),[]) else (none,["text outside a text element"])
    | _ => (none,["processing instruction"])
  | fuel+1,state,_,.element name attrs children =>
    if name.namespace_ != some svgURI then (none,["foreign element: " ++ name.localPart])
    else if !conditionsPass attrs then (none,[])
    else if name.localPart == "text" && !fonts.isEmpty then
      let inner := state.read attrs
      match chooseFont fonts inner.family with
      | some font => let (node,log) := lowerText font state attrs children; (some node,log)
      | none => (none,["element: text"])
    else if name.localPart == "switch" then
      -- SVG Tiny 1.2 §5.8: draw only the first child whose conditions pass.
      let selected : NamespaceNode → Bool := fun
        | .element n a _ => n.namespace_ == some svgURI && conditionsPass a | _ => false
      let chosen := children.find? selected
      let inner := state.read attrs
      let result := (chosen.toList).map (normalise fonts targets fuel inner false)
      -- A child that is not drawn can still be referenced, so it stays as a definition.
      let unused := children.eraseIdx (children.findIdx selected)
      let kept := unused.map (normalise fonts targets fuel inner false)
      (some (svgElement "g" (renameId attrs) (result.filterMap (·.1) ++ [svgElement "defs" [] (kept.filterMap (·.1))])),
        result.flatMap (·.2) ++ kept.flatMap (·.2))
    else if name.localPart == "a" then
      -- A link draws its content. Link regions are not part of this pass.
      let inner := state.read attrs
      let results := children.map (normalise fonts targets fuel inner false)
      (some (svgElement "g" (renameId attrs) (results.filterMap (·.1))),results.flatMap (·.2))
    else if name.localPart == "use" && !fonts.isEmpty && (textInstance targets attrs).isSome then
      let inner := state.read attrs
      let target := (textInstance targets attrs).getD (.other (.comment ""))
      let (node,log) := normalise fonts targets fuel inner false target
      let x := float (plainAttr attrs "x") 0
      let y := float (plainAttr attrs "y") 0
      let frame := ((plainAttr attrs "transform").getD "") ++ s!" translate({x},{y})"
      let kept := (renameId attrs).filter fun a => a.name.namespace_.isNone &&
        !["x","y","width","height","transform","href","font-size","font-family","text-anchor"].contains a.name.localPart
      (some (svgElement "g" (kept ++ [mkAttr "transform" frame]) node.toList),log)
    else if !readable.contains name.localPart then (none,["element: " ++ name.localPart])
    else if silent.contains name.localPart then (some (.element name (renameId attrs) []),[])
    else
      let keepText := name.localPart == "style"
      let inner := state.read attrs
      let results := children.map (normalise fonts targets fuel inner keepText)
      (some (.element name (renameId attrs) (results.filterMap (·.1))),results.flatMap (·.2))

private def stripAttr (tag : String) (key : String) : Nat → NamespaceNode → NamespaceNode × Nat
  | 0,node => (node,0)
  | _,.other raw => (.other raw,0)
  | fuel+1,.element name attrs children =>
    let kept := if tag.isEmpty || name.localPart == tag then attrs.filter (fun a => a.name.localPart != key) else attrs
    let results := children.map (stripAttr tag key fuel)
    (.element name kept (results.map (·.1)),
      attrs.length-kept.length + (results.map (·.2)).foldl (·+·) 0)

/-- Element paths, deepest first, so a removal takes the least possible. -/
private def elementPaths : Nat → List Nat → NamespaceNode → List (List Nat)
  | 0,_,_ => []
  | _,_,.other _ => []
  | fuel+1,path,.element _ _ children =>
    (children.zipIdx.flatMap fun (child,index) => elementPaths fuel (path++[index]) child) ++ [path]

private def removeAt : Nat → List Nat → NamespaceNode → NamespaceNode
  | 0,_,node => node
  | _,[],node => node
  | _,_,.other raw => .other raw
  | fuel+1,[index],.element name attrs children =>
    let _ := fuel
    .element name attrs (children.eraseIdx index)
  | fuel+1,index::rest,.element name attrs children =>
    .element name attrs (children.zipIdx.map fun (child,i) =>
      if i == index then removeAt fuel rest child else child)

private def nodeAt : Nat → List Nat → NamespaceNode → Option NamespaceNode
  | _,[],node => some node
  | 0,_,_ => none
  | _,_,.other _ => none
  | fuel+1,index::rest,.element _ _ children => do
    nodeAt fuel rest (← children[index]?)

private def tagName : NamespaceNode → String
  | .element name _ _ => name.localPart
  | _ => "node"

/-- A stroke style the reader refuses: draw with the default style, and log it. -/
private def styleError (message : String) : Option String :=
  ["stroke-linejoin","stroke-miterlimit","stroke-linecap"].find? fun key =>
    message.startsWith ("unsupported " ++ key ++ ":")

/-- `unsupported attribute on TAG: KEY`, with or without "qualified". -/
private def attributeError (message : String) : Option (String × String) :=
  let tail := if message.startsWith "unsupported attribute on "
    then some (message.drop 25).toString
    else if message.startsWith "qualified attribute unsupported on "
    then some (message.drop 35).toString else none
  tail.bind fun tail => match tail.splitOn ": " with
    | [tag,key] => some (tag,key)
    | _ => none

private structure Attempt where
  root : NamespaceNode
  dropped : List String
  parses : Nat

/-- Remove the deepest element whose removal changes the reader's first error.
    The reader stops at its first error, so an element that does not cause it
    can not change it, except by a reference to the element that does. -/
private def removeOffender (width height : Nat) (message : String) (a : Attempt) :
    Option Attempt := Id.run do
  let mut parses := a.parses
  for path in elementPaths maxDepth [] a.root do
    if path.isEmpty then continue
    if parses >= maxParses then return none
    parses := parses + 1
    let next := removeAt maxDepth path a.root
    let changed := match NativeSVG.parseRoot next width height with
      | .ok _ => true
      | .error other => other != message
    if changed then
      let tag := ((nodeAt maxDepth path a.root).map tagName).getD "node"
      return some {root:=next,parses,dropped:=a.dropped ++ [s!"removed {tag}: {message}"]}
  return none

private def repair (width height : Nat) : Nat → Attempt → Except String (NativeSVG.Scene × List String)
  | 0,_ => throw "forgiving pass exceeded its repair limit"
  | fuel+1,a =>
    match NativeSVG.parseRoot a.root width height with
    | .ok scene => pure (scene,a.dropped)
    | .error message =>
      let stripped := (attributeError message).bind fun (tag,key) =>
        let (root,count) := stripAttr tag key maxDepth a.root
        if count == 0 then none
        else some {a with root,parses:=a.parses+1,dropped:=a.dropped ++ List.replicate count s!"attribute: {tag} {key}"}
      let restyled := (styleError message).bind fun key =>
        let (root,count) := stripAttr "" key maxDepth a.root
        if count == 0 then none
        else some {a with root,parses:=a.parses+1,dropped:=a.dropped ++ [s!"approximated: {key}"]}
      match (stripped.orElse fun _ => restyled).orElse (fun _ => removeOffender width height message a) with
      | some next => repair width height fuel next
      | none => throw message

/-- The `version` label names a language edition; it does not change drawing. -/
private def rootAttrs (root : NamespaceNode) : NamespaceNode × List String :=
  match root with
  | .element name attrs children =>
    let dropped := ["version","baseProfile","viewport-fill","viewport-fill-opacity"]
    let kept := attrs.filter fun a => !(a.name.namespace_.isNone && dropped.contains a.name.localPart)
    -- SVG Tiny 1.2 §11.11: viewport-fill paints the whole viewport first.
    let background := match plainAttr attrs "viewport-fill" with
      | none => []
      | some fill => if fill.trimAscii.toString == "none" then [] else
        [svgElement "rect" ([mkAttr "x" "-100000",mkAttr "y" "-100000",mkAttr "width" "200000",mkAttr "height" "200000",mkAttr "fill" fill] ++
          ((plainAttr attrs "viewport-fill-opacity").toList.map (mkAttr "fill-opacity"))) []]
    (.element name kept (background ++ children),(attrs.filter (fun a => !kept.any (fun k => k.name == a.name))).map
      (fun a => "attribute: svg " ++ a.name.localPart))
  | node => (node,[])

/-- Parse as a browser would: draw what the strict reader can draw. A document
    that is not well-formed XML stays an error. -/
def parse (xml : String) (width height : Nat) (font : Option SVGFont := none) :
    Except String (NativeSVG.Scene × List String) := do
  if xml.length > NativeSVG.maxInputChars then throw "SVG input exceeds 1048576 characters"
  let root ← parseNamespaceView xml
  let (root,rootLog) := rootAttrs root
  -- Fonts in the document come first; the host's font is the default.
  let targets := (idTargets maxDepth root).foldl (fun map (id,node) =>
    if map.contains id then map else map.insert id node) ({} : Std.HashMap String NamespaceNode)
  let (some root,log) := normalise (fontsIn root ++ font.toList) targets maxDepth {} false root | throw "root element is not read"
  repair width height 1024 {root,dropped:=rootLog ++ log,parses:=0}

end NativeSVGForgiving
