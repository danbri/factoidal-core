import L4Factoidal.WasmVM.Hosts.LeanJSWorkers
import L4Factoidal.DOM.OfHtml

/-!
# Dedicated workers on BubblePopJS

`Hosts.LeanJSWorkers`, checked at build time: a page makes a worker; its script is asked of
the embedder (one fetch, with the script it imports); messages go both ways through the
structured clone; the worker's scope has no DOM; a timer in the worker runs at its time on
the page's clock; an error not handled in the worker reaches the Worker object; terminate
stops it; and a page with no worker has no worker state.
-/
namespace L4Factoidal.WasmVM.Tests.LeanJSWorkers
open L4Factoidal L4Factoidal.WasmVM.Hosts

def page : String := "<!doctype html><script>" ++
  "const w = new Worker('w.js', {name: 'n'});" ++
  "w.onmessage = e => { console.log('got', JSON.stringify(e.data.v), e.data.m instanceof Map, e.data.m.get(1), Date.now());" ++
  "  if (e.data.v === 'bye') { w.terminate(); w.postMessage('after'); } };" ++
  "w.onerror = e => { console.log('error', e.message); e.preventDefault(); };" ++
  "w.postMessage({n: 2});</script>"

def worker : String :=
  "importScripts('lib.js');" ++
  "console.log('scope', typeof document, typeof window, self.constructor.name, name, location.pathname, lib);" ++
  "onmessage = e => {" ++
  "  if (e.data === 'after') { console.log('ran after terminate'); return; }" ++
  "  postMessage({v: e.data.n * 21, m: new Map([[1, 'one']])});" ++
  "  setTimeout(() => { postMessage({v: 'late', m: new Map()}); throw new Error('boom'); }, 40);" ++
  "  setTimeout(() => postMessage({v: 'bye', m: new Map()}), 60); };"

def scriptsOf (dom : DOM.Dom) : Array (Nat × String) :=
  ((dom.treeOrder 0).toList.filter fun k => DOM.Dom.isHtmlElement (dom.get k) "script").toArray.map
    fun k => (k, (dom.textContent k).getD "")

/-- The page started, its worker's scripts given as the embedder would, and the loop run
until it is quiet: the page's console lines, the fetch rounds, and the workers left. -/
def run : Except String (List String × List (List String) × Nat) := do
  let base ← LeanJS.prepareSource
  let dom := DOM.parseHtmlDocument page
  let s := LeanJS.start base dom "http://t.test/p.html" (scriptsOf dom) {} {} { instructionsPerMs := 1000000000000 }
  let e := LeanJSWorkers.engine
  let mut a : LeanJSWorkers.Agents := LeanJSWorkers.pump { page := s, base := some base }
  let mut rounds := []
  for _ in [0:4] do
    if a.w.loads.isEmpty then break
    rounds := rounds ++ [a.w.loads.toList]
    let got := a.w.loads.map fun u =>
      (u, if u.endsWith "/w.js" then some worker else if u.endsWith "/lib.js" then some "var lib = 'lib';" else none)
    a := LeanJSWorkers.give a got
    a := (e.settle a 1000 100000 LeanJSWorkers.Agents.waits).1
  return (a.page.logs.toList, rounds, a.w.list.size)

#guard match run with
  | .ok (logs, rounds, left) =>
    rounds == [["http://t.test/w.js"], ["http://t.test/lib.js"]] && left == 0 &&
    logs == ["[worker 1] scope undefined undefined DedicatedWorkerGlobalScope n /w.js lib",
      "got 42 true one 0", "got \"late\" true undefined 40", "error Error: boom", "got \"bye\" true undefined 60"]
  | .error _ => false

-- Math.random in workers (each seeded from its own entropy by `WebApi.mathRandomSeed`) is
-- tested in labs/demos/foafnaut/workers_test.ts on the native library: the seed is a
-- SHA-256 by HACL*, which Lean's interpreter of `#guard` cannot call.

-- a page that makes no worker: no worker state, no fetch
#guard match (do
    let base ← LeanJS.prepareSource
    let dom := DOM.parseHtmlDocument "<script>console.log(typeof Worker)</script>"
    let s := LeanJS.start base dom "http://t.test/q.html" (scriptsOf dom) {} {} {}
    let a := LeanJSWorkers.pump { page := s, base := some base }
    return (a.page.logs.toList, a.page.wkIdle, a.w.list.size, a.w.loads.size) : Except String _) with
  | .ok (logs, idle, n, loads) => logs == ["function"] && idle && n == 0 && loads == 0
  | .error _ => false

end L4Factoidal.WasmVM.Tests.LeanJSWorkers
