import L4Factoidal.Rendering.Style

/-! Checks of the cascade's rule buckets and element-key table (realperf, record
docs/designissues/2026-11-09-real-site-layout-speed.md).

* `RuleIndex.matched` gives, for every node of each test page, the matches of the plain
  loop `matchedRules` (the premise of `CSS.computeAll_eq_linear`), and `computeAll`
  gives the styles of `computeAllLinear`.
* Cost: the candidates an element tries are those of its buckets. With N one-class rules
  and M elements of two classes each, the buckets give 2·M candidates in all, where the
  plain loop tries N·M rules. -/
namespace L4Factoidal.Rendering.CascadeTests
open DOM CSS

private def fingerprint (ms : List Match) : String :=
  reprStr (ms.map fun (o,r,sel) => (o,reprStr r,reprStr sel))

/-- Every node of the page: the buckets' matches are the plain loop's. -/
def agrees (html css : String) (state : ElementState := {}) : Bool :=
  match CSS.parse css with
  | .error _ => false
  | .ok rules =>
    let dom := DOM.parseHtmlDocument html
    let ix := RuleIndex.build rules
    let ks := ElemKeys.of dom
    (List.range dom.size).all fun id =>
      fingerprint (ix.matched (ks.get dom) dom id state) == fingerprint (matchedRules dom id rules state)

/-- And the styles agree, compared by their `Repr`. -/
def stylesAgree (html css : String) (state : ElementState := {}) : Bool :=
  match CSS.parse css with
  | .error _ => false
  | .ok rules =>
    let dom := DOM.parseHtmlDocument html
    match computeAll dom rules 1 state, computeAllLinear dom rules 1 state with
    | .ok a, .ok b => reprStr a == reprStr b
    | .error a, .error b => a == b
    | _, _ => false

private def page :=
  "<html><body id='top' class='skin'><div id='x' class='a b'><p class='b'>one <a href='/u'>link</a></p>" ++
  "<ul class='list a'><li class='item'>i</li><li class='item b a'>j <span>k</span></li></ul></div>" ++
  "<section><div class='a'><span class='c' id='y'>s</span></div><a href='#v' class='b'>v</a><a>no</a></section>" ++
  "<button>go</button><svg width='10' height='10'><rect class='a'/></svg></body></html>"
private def sheet :=
  "div{color:#010101}*{margin:0}.a{color:#020202}#x{color:#030303}div.a{padding:1px}" ++
  ".a .b{color:#040404}p:hover{color:#050505}a:link{color:#060606}.a.b{color:#070707}" ++
  "ul li{color:#080808}#x .a span{color:#090909}:visited{color:#0a0a0a}.b,.c,#y{margin:2px}" ++
  "section a.b{color:#0b0b0b}.item:hover span{color:#0c0c0c}body .skin{color:#0d0d0d}" ++
  "li.item.b.a{color:#0e0e0e}span#y.c{color:#0f0f0f}:any-link{color:#101010}button:active{color:#111111}"

#guard agrees page sheet
#guard agrees page sheet {hover := some 9, active := some 20}
#guard agrees page sheet {visited := [7, 19]}
#guard stylesAgree page sheet
#guard stylesAgree page sheet {hover := some 9, visited := [7]}
#guard agrees page ""
#guard agrees "<p class=' a\tb\n a '>x</p>" ".a{color:red}.b.a{color:blue}"

#guard RuleIndex.mergeRuns #[] == #[]
#guard RuleIndex.mergeRuns #[#[1,3]] == #[1,3]
#guard RuleIndex.mergeRuns #[#[1,3,9],#[2,3],#[],#[0,9,10],#[3]] == #[0,1,2,3,9,10]
#guard RuleIndex.mergeRuns ((List.range 33).toArray.map fun i => #[i,40+i%3]) ==
  ((List.range 33) ++ [40,41,42]).toArray

/-- The candidates all elements try. -/
def candidateTotal (html css : String) : Nat :=
  match CSS.parse css with
  | .error _ => 0
  | .ok rules =>
    let dom := DOM.parseHtmlDocument html
    let ix := RuleIndex.build rules
    let ks := ElemKeys.of dom
    let author := userAgentRules.length
    (List.range dom.size).foldl (fun n id =>
      if (dom.get id).type == .element then
        n + ((ix.candidates (ks.get dom id) (dom.get id).lname).filter (· ≥ author)).size
      else n) 0

private def manyRules (n : Nat) : String :=
  String.join ((List.range n).map fun i => s!".c{i}\{color:#000001}")
private def manyElements (m : Nat) : String :=
  "<div>" ++ String.join ((List.range m).map fun i => s!"<i class='c{i % 97} c{100 + i % 89}'></i>") ++ "</div>"

-- N = 400 one-class rules, M = 300 elements: 600 author candidates (2·M), not 120,000 (N·M).
#guard candidateTotal (manyElements 300) (manyRules 400) == 600
-- The author candidates grow with M, not with N.
#guard candidateTotal (manyElements 300) (manyRules 2000) == 600
#guard agrees (manyElements 60) (manyRules 200)

/-! `parseIn` (the sheet read once, `parseRaw`, then filtered by the media queries)
gives the rules of `parseInBlocks` (the conditions tested first, for one environment):
`CSS.parseInBlocks_eq` proves it; these run it. -/
private def mediaSheet :=
  "p{color:red}@media (min-width: 600px){p{color:blue}.a{margin:1px}}@media print{p{color:green}}" ++
  "@media screen and (max-width: 400px){div{padding:2px}}@media (prefers-color-scheme: dark){a{color:#fff}}" ++
  "@media screen or print{b{color:red}}@font-face{font-family:x}@media all{@media screen{i{color:red}}em{color:red}}" ++
  "@media only screen{q{color:red}}@media not print{s{color:red}}"
private def sameRules (env : MediaQuery.Env) (source : String) : Bool :=
  match parseIn env source, parseInBlocks env source with
  | .ok a, .ok b => reprStr a == reprStr b
  | .error a, .error b => a == b
  | _, _ => false
#guard sameRules {} mediaSheet
#guard sameRules {width := some 800, height := some 600, dark := some false} mediaSheet
#guard sameRules {width := some 300, height := some 600, dark := some true} mediaSheet
#guard sameRules {medium := "print"} mediaSheet
#guard sameRules {width := some 800} sheet
-- with the rule of the `@media screen` block inside `@media all` (read since 2026-11-14)
#guard ((parseIn {width := some 800} mediaSheet).toOption.map List.length) == some 7

/-! The sheet reader in the cascade (`SheetReader`): `@supports`, `@layer`, nesting, and
custom properties with `var()` (`CssVars`), on the computed style of the element `t`. -/
private def styleAt (html css : String) : Option Computed :=
  let dom := DOM.parseHtmlDocument html
  match CSS.parse css, dom.getElementById 0 "t" with
  | .ok rules, some id => ((computeAll dom rules).toOption.bind (·[id]?))
  | _, _ => none
private def redOf (html css : String) : Option Float := (styleAt html css).map (·.color.r)
/-- The width in px; -1 for `auto`, -2 for another unit. -/
private def widthOf (html css : String) : Option Float := (styleAt html css).map fun s =>
  match s.width with
  | .px v => v
  | .auto => -1
  | _ => -2
private def marginOf (html css : String) : Option (List Float) :=
  (styleAt html css).map fun s => [s.margin.top, s.margin.right, s.margin.bottom, s.margin.left]
private def pageT := "<div class=a><p id=t class=b>x</p></div>"
-- @supports: read when the condition holds; nested in @media
#guard widthOf pageT "@supports (display: grid) { p { width: 10px } }" == some 10
#guard widthOf pageT "@supports (display: no-such) { p { width: 10px } }" == some (-1)
#guard widthOf pageT "@media screen { @supports (width: 1px) { p { width: 10px } } }" == some 10
#guard widthOf pageT "@media print { @supports (width: 1px) { p { width: 10px } } }" == some (-1)
-- nesting
#guard widthOf pageT ".a { .b { width: 10px } }" == some 10
#guard widthOf pageT ".a { & > p { width: 10px } }" == some 10
#guard widthOf pageT "p { &.b { width: 10px } &.c { width: 20px } }" == some 10
#guard widthOf pageT ".a { width: 5px; p { width: 10px } }" == some 10
#guard widthOf pageT ".a { @media screen { p { width: 10px } } }" == some 10
-- layers (CSS Cascade 5 §6.4): a later layer wins over an earlier one whatever the
-- specificity; unlayered rules win over layers; important declarations in the reverse
#guard widthOf pageT "@layer one { #t { width: 10px } } @layer two { p { width: 20px } }" == some 20
#guard widthOf pageT "@layer two, one; @layer one { #t { width: 10px } } @layer two { p { width: 20px } }" == some 10
#guard widthOf pageT "p { width: 30px } @layer one { #t { width: 10px } }" == some 30
#guard widthOf pageT "@layer one { p { width: 10px !important } } @layer two { #t { width: 20px !important } }" == some 10
#guard widthOf pageT "#t { width: 30px !important } @layer one { p { width: 10px !important } }" == some 10
#guard widthOf "<p id=t style='width: 40px'>x</p>" "@layer one { p { width: 10px } } #t { width: 30px }" == some 40
#guard widthOf "<p id=t style='width: 40px !important'>x</p>" "@layer one { p { width: 10px !important } }" == some 40
#guard widthOf pageT "@layer a { @layer b { #t { width: 10px } } p { width: 20px } }" == some 20
-- custom properties: inherited, own over inherited, fallbacks, invalid at computed-value time
#guard widthOf pageT ":root { --w: 10px } p { width: var(--w) }" == some 10
#guard widthOf pageT ".a { --w: 10px } p { width: var(--w) }" == some 10
#guard widthOf pageT ":root { --w: 10px } p { --w: 20px; width: var(--w) }" == some 20
#guard widthOf pageT "p { width: var(--none, 30px) }" == some 30
#guard widthOf pageT "p { width: 5px } #t { width: var(--none) }" == some (-1)
#guard widthOf pageT ":root { --a: var(--b); --b: 10px } p { width: var(--a) }" == some 10
#guard widthOf pageT ":root { --a: var(--b); --b: var(--a) } p { width: var(--a, 7px) }" == some 7
#guard widthOf pageT ":root { --w: 10px } p { width: calc(var(--w) * 2) }" == some 20
#guard widthOf "<p id=t style='--w: 12px; width: var(--w)'>x</p>" "" == some 12
#guard widthOf "<div style='--w: 12px'><p id=t style='width: var(--w)'>x</p></div>" "" == some 12
#guard redOf pageT ":root { --c: #ff0000 } p { color: var(--c) }" == some 1
#guard redOf pageT ":root { --c: 255, 0, 0 } p { color: rgb(var(--c)) }" == some 1
-- margin with var(): the sides after substitution; a later longhand still wins
#guard marginOf pageT ":root { --m: 1px 2px } p { margin: var(--m) }" == some [1, 2, 1, 2]
#guard marginOf pageT ":root { --m: 1px } p { margin: var(--m) 4px; margin-top: 9px }" == some [9, 4, 1, 4]
#guard marginOf pageT ":root { --m: 1px } p { margin-top: 9px; margin: var(--m) }" == some [1, 1, 1, 1]
-- invalid at computed-value time: as if not declared (this profile starts a `p` with the
-- user agent's margins, which are not declarations, so they stand where CSS says 0)
#guard marginOf pageT "p { margin: 3px } #t { margin: var(--none) }" == some [8, 0, 8, 0]
#guard marginOf pageT "p { margin: calc(1px + 2px) 0 }" == some [3, 0, 3, 0]
-- flow-relative properties (CSS Logical 1): one cascade with the physical ones, by direction
private def paddingOf (html css : String) : Option (List Float) :=
  (styleAt html css).map fun s => [s.padding.top, s.padding.right, s.padding.bottom, s.padding.left]
#guard marginOf pageT "p { margin: 0; margin-inline-start: 5px; margin-block-end: 7px }" == some [0, 0, 7, 5]
#guard marginOf "<div dir=rtl><p id=t>x</p></div>" "p { margin: 0; margin-inline-start: 5px }" == some [0, 5, 0, 0]
#guard marginOf pageT "p { margin: 0; direction: rtl; margin-inline-start: 5px }" == some [0, 5, 0, 0]
#guard marginOf pageT "p { margin: 0; margin-inline: 5px 6px; margin-block: 1px }" == some [1, 6, 1, 5]
#guard marginOf pageT "p { margin-inline-start: 5px; margin-left: 9px; margin-top: 0; margin-bottom: 0 }" == some [0, 0, 0, 9]
#guard marginOf pageT "p { margin-left: 9px; margin-inline-start: 5px; margin-top: 0; margin-bottom: 0 }" == some [0, 0, 0, 5]
#guard marginOf pageT "#t { margin-left: 9px } p { margin: 0; margin-inline-start: 5px }" == some [0, 0, 0, 9]
#guard marginOf pageT ":root { --m: 5px 6px } p { margin: 0; margin-inline: var(--m) }" == some [0, 6, 0, 5]
#guard paddingOf pageT "p { padding-inline: 3px; padding-block-start: 2px }" == some [2, 3, 0, 3]
#guard paddingOf "<p id=t style='padding-inline-end: 4px'>x</p>" "" == some [0, 4, 0, 0]
#guard widthOf pageT "p { inline-size: 10px }" == some 10
#guard widthOf pageT "p { inline-size: 10px; width: 20px }" == some 20
#guard widthOf pageT "p { width: 20px; inline-size: 10px }" == some 10
#guard (styleAt pageT "p { block-size: 10px; max-inline-size: 30px }").map (fun s => (reprStr s.height, reprStr s.maxWidth)) ==
  (styleAt pageT "p { height: 10px; max-width: 30px }").map (fun s => (reprStr s.height, reprStr s.maxWidth))
-- CSS-wide keywords (CSS Cascade 4 §7.3)
#guard redOf pageT ".a { color: #ff0000 } p { color: #00ff00 } #t { color: inherit }" == some 1
#guard redOf "<div style='color:#ff0000'><a id=t href=x>l</a></div>" "a { color: inherit }" == some 1
#guard redOf pageT "body { color: #ff0000 } p { color: initial }" == some 0
#guard redOf pageT "body { color: #ff0000 } p { color: #00ff00 } #t { color: unset }" == some 1
#guard widthOf pageT ".a { width: 50px } p { width: 20px } #t { width: inherit }" == some 50
#guard widthOf pageT ".a { width: 50px } p { width: 20px } #t { width: unset }" == some (-1)
#guard widthOf pageT ".a { width: 50px } p { width: 20px } #t { width: initial }" == some (-1)
#guard marginOf pageT "p { margin: 3px } #t { margin: initial }" == some [0, 0, 0, 0]
#guard marginOf pageT "p { margin: 3px } #t { margin: revert }" == some [8, 0, 8, 0]
#guard marginOf pageT ".a { margin: 3px } p { margin: inherit }" == some [3, 3, 3, 3]
#guard (styleAt pageT ".a { font-size: 30px; font-family: Foo } p { font-size: 10px; font-family: Bar } #t { font: inherit }").map
  (fun s => (s.fontSize, s.fontFamily)) == some (30, "Foo")
#guard (styleAt "<div><h1 id=t>x</h1></div>" "h1 { font-size: inherit }").map (·.fontSize) == some 16
-- the `font` shorthand sets the size, the family and the line height
#guard (styleAt pageT "#t { font: xx-small serif }").map (fun s => (s.fontSize, s.fontFamily)) == some (9, "serif")
#guard (styleAt pageT "#t { font: italic bold 12px/30px Georgia, serif }").map (fun s => (s.fontSize, s.lineHeight)) ==
  some (12, 30)
#guard (styleAt pageT ".a { font: 20px/2 Foo } #t { font-size: 10px }").map (fun s => (s.fontSize, s.lineHeight)) == some (10, 20)
#guard (styleAt "<div><h1 id=t>x</h1></div>" "h1 { display: inherit }").map (fun s => reprStr s.display) ==
  (styleAt "<div><p id=t>x</p></div>" "").map (fun s => reprStr s.display)
-- a page with no custom property has no map
#guard (styleAt pageT "p { width: 10px }").map (·.vars.isEmpty) == some true
#guard (styleAt pageT ":root { --a: 1 } p { width: 10px }").map (·.vars.toList) == some [("--a", "1")]
-- declarations with strings and URLs
#guard widthOf pageT "p { background-image: url(data:image/png;base64,AA==); width: 10px }" == some 10
#guard widthOf "<p id=t style='background-image: url(data:image/png;base64,AA==); width: 10px'>x</p>" "" == some 10

/-! Pages with shadow trees: the scoped buckets (`ScopedIndex`) against the plain loop
(`matchedRulesIn`, the premise of `CSS.computeAllIn_eq_linear`), on every node, and the
styles of `computeAllIn` against `computeAllInLinear`. -/
private def scopedRules (dom : DOM.Dom) (docCss shadowCss : String) : Except String (List Rule) := do
  let doc ← CSS.parse docCss
  let sr := ((List.range dom.size).filter (dom.isShadowRoot ·))
  let inner ← CSS.parse shadowCss
  return doc ++ sr.foldr (fun r acc => inner.map (fun x => {x with scope := some r}) ++ acc) []

def agreesIn (html docCss shadowCss : String) (state : ElementState := {}) : Bool :=
  let dom := DOM.parseHtmlDocument html
  match scopedRules dom docCss shadowCss with
  | .error _ => false
  | .ok rules =>
    let ts := TreeScope.of dom
    let ix := ScopedIndex.build rules
    let ks := ElemKeys.of dom
    (List.range dom.size).all fun id =>
      fingerprint (ix.matched (ks.get dom) ts id state) == fingerprint (matchedRulesIn ts id rules state)

def stylesAgreeIn (html docCss shadowCss : String) (state : ElementState := {}) : Bool :=
  let dom := DOM.parseHtmlDocument html
  match scopedRules dom docCss shadowCss with
  | .error _ => false
  | .ok rules =>
    let ts := TreeScope.of dom
    match computeAllIn ts dom.flat rules 1 state, computeAllInLinear ts dom.flat rules 1 state with
    | .ok a, .ok b => reprStr a == reprStr b
    | .error a, .error b => a == b
    | _, _ => false

private def shadowPage :=
  "<html><body><div id='h' class='a'><template shadowrootmode='open'><style></style><p id='in' class='b'>s <span class='c'>t</span></p>" ++
  "<slot></slot><slot name='n'></slot><div id='h2'><template shadowrootmode='open'><p class='b'>u</p><slot></slot></template><i class='b' slot='q'>v</i></div></template>" ++
  "<b id='lt' class='a'>x</b><em slot='n'>y</em></div><p id='out' class='b'>o</p></body></html>"
private def shadowDocCss :=
  "p{color:#010101}.b{color:#020202}#h{color:#030303}.a{margin:0}*{padding:0}#out .b{color:#040404}" ++
  ":host{color:#050505}::slotted(b){color:#060606}"
private def shadowInnerCss :=
  ".b{color:#070707}p span{color:#080808}:host{color:#090909}:host(.a){color:#0a0a0a}:host #in{color:#0b0b0b}" ++
  "::slotted(b){color:#0c0c0c}::slotted(*){margin:1px}slot::slotted(.a){color:#0d0d0d}.c:hover{color:#0e0e0e}"

#guard agreesIn shadowPage shadowDocCss shadowInnerCss
#guard agreesIn shadowPage shadowDocCss shadowInnerCss {hover := some 8, active := some 12}
#guard agreesIn shadowPage shadowDocCss ""
#guard agreesIn shadowPage "" shadowInnerCss
#guard stylesAgreeIn shadowPage shadowDocCss shadowInnerCss
#guard stylesAgreeIn shadowPage shadowDocCss shadowInnerCss {hover := some 8}

-- A page with no shadow tree never takes the scoped path: `:host` and `::slotted()` rules
-- go in no bucket, and match nothing.
#guard ((CSS.parse ":host{color:red}::slotted(b){color:red}").toOption.map fun rs =>
  let ix := RuleIndex.build rs
  (ix.universal.size, ix.byTag.size, ix.byClass.size, ix.byId.size)) == some ((RuleIndex.build []).universal.size, (RuleIndex.build []).byTag.size, 0, (RuleIndex.build []).byId.size)

-- font-weight and font-style (2026-11-14; before, neither had a field and no text was bold or
-- italic). The user agent's defaults: headings and th bold, b and strong bolder than their
-- parent, i, em, cite, var, dfn and address italic; inherited; author rules win.
#guard (styleAt "<p><b id=t>x</b></p>" "").map (·.fontWeight) == some 700
#guard (styleAt "<h1 id=t>x</h1>" "").map (·.fontWeight) == some 700
#guard (styleAt "<h1><b id=t>x</b></h1>" "").map (·.fontWeight) == some 900
#guard (styleAt "<h1><span id=t>x</span></h1>" "").map (·.fontWeight) == some 700
#guard (styleAt "<p id=t>x</p>" "").map (fun s => (s.fontWeight, s.oblique)) == some (400, false)
#guard (styleAt "<h1 id=t>x</h1>" "h1 { font-weight: normal }").map (·.fontWeight) == some 400
#guard (styleAt "<p id=t>x</p>" "p { font-weight: 600 }").map (·.fontWeight) == some 600
#guard (styleAt "<p id=t>x</p>" "p { font-weight: heavy }").map (·.fontWeight) == some 400
-- bolder and lighter are relative to the parent's weight, not to the element's default
#guard (styleAt "<h1><b id=t>x</b></h1>" "b { font-weight: lighter }").map (·.fontWeight) == some 400
#guard (styleAt "<h1><span id=t>x</span></h1>" "span { font-weight: bolder }").map (·.fontWeight) == some 900
#guard (styleAt "<div style='font-weight:normal'><b id=t>x</b></div>" "b { font-weight: inherit }").map (·.fontWeight) == some 400
#guard (styleAt "<h1 id=t>x</h1>" "h1 { font-weight: initial }").map (·.fontWeight) == some 400
#guard (styleAt "<p><em id=t>x</em></p>" "").map (·.oblique) == some true
#guard (styleAt "<em><span id=t>x</span></em>" "").map (·.oblique) == some true
#guard (styleAt "<em id=t>x</em>" "em { font-style: normal }").map (·.oblique) == some false
#guard (styleAt "<p id=t>x</p>" "p { font-style: oblique 10deg }").map (·.oblique) == some true
#guard (styleAt "<p id=t>x</p>" "p { font-style: italic }").map (·.oblique) == some true
/-! Presentational hints (HTML §15; html/rendering/dimension-attributes.html and
pixel-length-attributes.html): the computed style of the first element named `tag`. -/
private def hinted (html css tag : String) (f : Computed → Bool) : Bool :=
  match CSS.parse css with
  | .error _ => false
  | .ok rules =>
    let dom := DOM.parseHtmlDocument html
    match computeAll dom rules 1 {} with
    | .ok styles => match (List.range dom.size).find? (fun i => (dom.get i).lname == tag) with
      | some i => (styles[i]?.map f).getD false
      | none => false
    | .error _ => false

private def isPx (v : Float) : CSS.Length → Bool
  | .px x => x == v
  | _ => false

#guard hinted "<img width='200.25' height='20.25e2'>" "" "img" fun s => isPx 200.25 s.width && isPx 20.25 s.height
#guard hinted "<hr width='50%'>" "" "hr" fun s => match s.width with | .percent p => p == 0.5 | _ => false
#guard hinted "<iframe width=300 height=100></iframe>" "" "iframe" fun s => isPx 300 s.width && isPx 100 s.height
#guard hinted "<embed hspace=7 vspace='3.5'>" "" "embed" fun s => s.margin.left == 7 && s.margin.right == 7 && s.margin.top == 3.5
#guard hinted "<img border=4>" "" "img" fun s => s.borderStyle == .solid && s.borderWidth.top == 4
#guard hinted "<img border=4 width=+5>" "img{border-width:1px;width:9px}" "img" fun s => s.borderWidth.left == 1 && isPx 9 s.width
#guard hinted "<table><tr><td width=0 height='0%'>x</table>" "" "td" fun s => match s.width, s.height with | .auto, .auto => true | _, _ => false
#guard hinted "<table width=0 height=0><tr><td>x</table>" "" "table" fun s => (match s.width with | .auto => true | _ => false) && isPx 0 s.height
#guard hinted "<body marginwidth=3 topmargin=4 marginheight=5>" "" "body" fun s => s.margin.left == 3 && s.margin.right == 3 && s.margin.top == 5 && s.margin.bottom == 5
#guard hinted "<body leftmargin=-1 topmargin=2>" "" "body" fun s => s.margin.left == 8 && s.margin.top == 2
#guard hinted "<input type=image width=40 hspace=2>" "" "input" fun s => isPx 40 s.width && s.margin.left == 2
#guard hinted "<input width=40>" "" "input" fun s => match s.width with | .auto => true | _ => false
#guard hinted "<picture><source srcset=a.png width=200 height=50><img src=b.png width=9></picture>" "" "img" fun s => isPx 200 s.width && isPx 50 s.height

/-! Heading levels, `:heading` and `:indeterminate` of radio groups
(html/semantics/sections/headingoffset-and-headingreset.html, selectors/pseudo-classes). -/
private def levels (html : String) : List (Option Nat) :=
  let d := DOM.parseHtmlDocument html
  ((List.range d.size).filter fun i => L4Factoidal.DOM.Selectors.headingRank (d.get i) != 0).map (L4Factoidal.DOM.Selectors.headingLevel d)

private def matching (html sel : String) (tags : List String) : List Bool :=
  let d := DOM.parseHtmlDocument html
  match L4Factoidal.DOM.Selectors.parse sel with
  | some l => ((List.range d.size).filter fun i => tags.contains (d.get i).lname).map
      fun i => L4Factoidal.DOM.Selectors.matchList d none L4Factoidal.DOM.Selectors.matchFuel i l
  | none => []

#guard levels "<div headingoffset=1><h1></h1><h3></h3><div headingoffset=2><h1></h1><div headingreset><h1></h1></div></div></div>" ==
  [some 2, some 4, some 4, some 1]
#guard levels "<div headingoffset=8><h1></h1><h6></h6></div><div headingoffset=-3><h2></h2></div><h1 headingoffset=3></h1>" ==
  [some 9, some 9, some 2, some 4]
#guard matching "<h1></h1><div headingoffset=1><h1></h1></div>" ":heading(2)" ["h1"] == [false, true]
#guard matching "<h1></h1><h2></h2>" ":heading(1, 3)" ["h1", "h2"] == [true, false]
#guard matching "<input type=radio name=a><input type=radio name=a><input type=radio name=b checked><input type=radio name=b><progress></progress><progress value=1></progress>"
  ":indeterminate" ["input", "progress"] == [true, true, false, false, true, false]

end L4Factoidal.Rendering.CascadeTests
