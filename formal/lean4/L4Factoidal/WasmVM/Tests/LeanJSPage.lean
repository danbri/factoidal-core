import L4Factoidal.WasmVM.Hosts.LeanJS
import L4Factoidal.DOM.OfHtml

/-!
# A page on BubblePopJS

`Hosts.LeanJS`: the prelude runs once in the JavaScript engine written in Lean, a page
starts from it, and its scripts change the arena through the typed commands of
`Hosts.Dom`. These checks run at build time: the page's script reads and writes the DOM,
logs, arms a timer and a listener; a click runs the listener and a microtask after it; the
clock moves and the timer runs.
-/
namespace L4Factoidal.WasmVM.Tests.LeanJSPage
open L4Factoidal.WasmVM.Hosts

def page : String := "<!doctype html><title>t</title><p id=out>before</p><button id=go>Go</button><script>" ++
  "const out = document.getElementById('out'); out.textContent = 'ran ' + document.title;" ++
  "document.getElementById('go').addEventListener('click', e => { out.textContent = 'clicked ' + e.target.id;" ++
  "  Promise.resolve().then(() => console.log('microtask')); });" ++
  "setTimeout(() => console.log('timer at ' + Date.now()), 50); console.log('loaded', [1, 2].map(x => x * 2).join());" ++
  "</script>"

def started : Except String LeanJS.Session := do
  let base ← LeanJS.prepareSource
  let dom := DOM.parseHtmlDocument page
  let scripts := ((dom.treeOrder 0).toList.filter fun k => DOM.Dom.isHtmlElement (dom.get k) "script").toArray.map
    fun k => (k, (dom.textContent k).getD "")
  return LeanJS.start base dom "file:///t.html" scripts {} {} { instructionsPerMs := 1000000000000 }

def logsOf (s : LeanJS.Session) : List String := s.logs.toList

#guard match started with
  | .ok s => logsOf s == ["loaded 2,4"] && s.errors.isEmpty && s.changes > 0 && (LeanJS.engine.loop s).timers.length == 1
  | .error _ => false

/-- The button's node, then a click and 60 ms of the clock. -/
def afterClick : Except String LeanJS.Session := do
  let s ← started
  let some go := s.host.dom.dom.getElementById 0 "go" | throw "no button"
  let s := LeanJS.engine.click s go
  return (LeanJS.engine.advance s 60).1

#guard match afterClick with
  | .ok s => logsOf s == ["loaded 2,4", "microtask", "timer at 50"] && s.errors.isEmpty
  | .error _ => false

end L4Factoidal.WasmVM.Tests.LeanJSPage

namespace L4Factoidal.WasmVM.Tests.LeanJSPage
/-- Original page regression: detached anchors/areas and reflected src/href are read
again after script changes the base; a second document has its own base. -/
private def baseURLPage : Except String (List String) := do
  let base ← Hosts.LeanJS.prepareSource
  let dom := DOM.parseHtmlDocument "<base href='/first/'><body></body>"
  let script := "const b=document.querySelector('base'); const a=document.createElement('a'); a.href='item';" ++
    "const area=document.createElement('area'); area.href='map'; const img=document.createElement('img'); img.src='pic';" ++
    "const link=document.createElement('link'); link.href='sheet';" ++
    "b.href='https://cdn.test/next/'; console.log([a.href,area.href,img.src,link.href].join('|'));" ++
    "b.remove(); console.log(a.href);" ++
    "const d=document.implementation.createHTMLDocument('other'); const db=d.createElement('base');" ++
    "db.href='https://owner.test/'; d.head.appendChild(db); const da=d.createElement('a'); da.href='own'; console.log(da.href);"
  let s := Hosts.LeanJS.start base dom "https://example.test/dir/page" #[(0, script)]
  if !s.errors.isEmpty then throw (";".intercalate s.errors.toList)
  let child := Hosts.LeanJS.start base (DOM.parseHtmlDocument "<base href='sub/'>") "about:srcdoc"
    #[(0, "const a=document.createElement('a'); a.href='x'; console.log(a.href);")]
    (aboutBase := some "https://creator.test/path/")
  if !child.errors.isEmpty then throw (";".intercalate child.errors.toList)
  return s.logs.toList ++ child.logs.toList

#guard baseURLPage == .ok [
  "https://cdn.test/next/item|https://cdn.test/next/map|https://cdn.test/next/pic|https://cdn.test/next/sheet",
  "https://example.test/dir/item", "https://owner.test/own", "https://creator.test/path/sub/x"]
end L4Factoidal.WasmVM.Tests.LeanJSPage
