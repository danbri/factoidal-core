import L4Factoidal.WasmVM.Hosts.LeanJSRealm
import L4Factoidal.WasmVM.Tests.LeanJSPage

/-!
# BubblePopJS's realm made at build time

`LeanJSRealm.prepare` decodes the heap that the prelude left (`LeanJSRealmData`). Checked
at build time:

- the data is not stale: it is accepted (same prelude, same fresh realm);
- the codec gives the data back: the decoded heap, written again, is the same data;
- a page on the decoded realm does what it does on the prelude's run (`LeanJSPage`).
-/
namespace L4Factoidal.WasmVM.Tests.LeanJSRealm
open L4Factoidal.WasmVM.Hosts

def decoded : Except String LeanJS.Session := LeanJS.prepareWith LeanJS.realmData

#guard decoded.isOk

#guard match decoded with
  | .ok s => match L4Factoidal.JS.Snapshot.encode (LeanJS.freshRealm {}) s.heap #[s.api, .str LeanJS.preludeMark] with
    | .ok again => again == LeanJS.realmData
    | .error _ => false
  | .error _ => false

def started : Except String LeanJS.Session := do
  let base ← decoded
  let dom := DOM.parseHtmlDocument LeanJSPage.page
  let scripts := ((dom.treeOrder 0).toList.filter fun k => DOM.Dom.isHtmlElement (dom.get k) "script").toArray.map
    fun k => (k, (dom.textContent k).getD "")
  let s := LeanJS.start base dom "file:///t.html" scripts {} {} { instructionsPerMs := 1000000000000 }
  let some go := s.host.dom.dom.getElementById 0 "go" | throw "no button"
  return (LeanJS.engine.advance (LeanJS.engine.click s go) 60).1

#guard match started with
  | .ok s => s.logs.toList == ["loaded 2,4", "microtask", "timer at 50"] && s.errors.isEmpty
  | .error _ => false

end L4Factoidal.WasmVM.Tests.LeanJSRealm
