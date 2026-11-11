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

-- Math.random in workers: each worker's seed comes from its own entropy
-- (`WebApi.mathRandomSeed`), so two workers of one page draw different sequences, and
-- neither draws the realm snapshot's (cryptosec finding F2). The embedder's entropy is
-- given here as 32 bytes per worker number.
def randomPage : String := "<!doctype html><script>" ++
  "for (const n of [1, 2]) new Worker('r.js').onmessage = e => console.log('r', e.data);" ++
  "</script>"

def randomRun : Except String (List String) := do
  let base ← LeanJS.prepareSource
  let dom := DOM.parseHtmlDocument randomPage
  let s := LeanJS.start base dom "http://t.test/r.html" (scriptsOf dom) {} {} { instructionsPerMs := 1000000000000 }
  let e := LeanJSWorkers.engine
  let mut a : LeanJSWorkers.Agents := LeanJSWorkers.pump
    { page := s, base := some base, entropy := fun w => ByteArray.mk (Array.replicate 32 (UInt8.ofNat (w + 7))) }
  for _ in [0:4] do
    if a.w.loads.isEmpty then break
    a := LeanJSWorkers.give a (a.w.loads.map fun u => (u, some "postMessage([Math.random(), Math.random(), Math.random()].join())"))
    a := (e.settle a 1000 100000 LeanJSWorkers.Agents.waits).1
  -- the snapshot's own sequence, as a worker drew it before the fix (a page on the realm)
  let dom := DOM.parseHtmlDocument "<script>console.log('r', [Math.random(), Math.random(), Math.random()].join())</script>"
  let p := LeanJS.start base dom "http://t.test/q.html" (scriptsOf dom) {} {} {}
  return a.page.logs.toList ++ p.logs.toList

#guard match randomRun with
  | .ok [a, b, snap] => a.startsWith "r 0." && b.startsWith "r 0." && a != b && a != snap && b != snap
  | _ => false

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
