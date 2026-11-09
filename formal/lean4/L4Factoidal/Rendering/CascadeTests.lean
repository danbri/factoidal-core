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

/-! `parseIn` (the sheet read once, `parseRawKept`, then filtered by the media queries)
gives the rules of `parseInBlocks` (the blocks read in place for one environment). -/
private def mediaSheet :=
  "p{color:red}@media (min-width: 600px){p{color:blue}.a{margin:1px}}@media print{p{color:green}}" ++
  "@media screen and (max-width: 400px){div{padding:2px}}@media (prefers-color-scheme: dark){a{color:#fff}}" ++
  "@media (hover: hover){b{color:red}}@font-face{font-family:x}@media all{@media screen{i{color:red}}em{color:red}}" ++
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
#guard ((parseIn {width := some 800} mediaSheet).toOption.map List.length) == some 6

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

end L4Factoidal.Rendering.CascadeTests
