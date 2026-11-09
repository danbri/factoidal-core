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

end L4Factoidal.Rendering.CascadeTests
