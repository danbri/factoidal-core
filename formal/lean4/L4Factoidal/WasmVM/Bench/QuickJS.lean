/-
L4Factoidal.WasmVM.Bench.QuickJS: QuickJS-NG, compiled to WebAssembly, running page
scripts inside the WasmVM engine, with the DOM in Lean
(https://github.com/danbri/factoidal/issues/1244; record:
docs/designissues/2026-11-07-wasmvm-engine.md, "QuickJS in WasmVM").

`lake exe wasmvm-bench qjs WASM [REACTOR]`, from `formal/lean4`. WASM is the output of
`tools/wasmvm/build-quickjs.sh` (not in the repository); the entry point is
`tools/wasmvm/quickjs/qjs_wasmvm_entry.c`. REACTOR, when given, is the pinned
QuickJS-NG v0.18.0 `qjs-wasi-reactor.wasm` that the Foafnaut script engine runs today
(`labs/demos/foafnaut/web-render/script-engine/fetch-reactor.mjs`).

1. Load the module. WASI capabilities: a virtual clock that the timer loop sets (QuickJS
   aborts without a clock); no randomness, no output, no environment, no files. `foafnaut_dom` is served by `Hosts.Dom` on a Lean DOM
   arena; `env.emscripten_notify_memory_growth` does nothing.
2. Plain JavaScript: each case is evaluated and its completion value compared.
3. Scripted pages: each page is parsed with the Lean HTML parser (`DOM.parseHtmlDocument`),
   its classic scripts run in tree order, then clicks are dispatched. Lean dispatches:
   it finds the `click` listeners of the target in the host's requests and runs each
   with `qjs_call`. The typed commands of each turn are compared with what the current
   host-run QuickJS path gives for the same element snapshot and sources
   (`tools/wasmvm/quickjs/host-reference.mjs`, run with `node`, when REACTOR is given).
4. Pages that the host-run path does not support (timers, `createElement`, promises)
   run with a small timer loop here (virtual time, due time then order of
   `setTimeout`) and are compared with the expected text.
5. Speed: wall time of each evaluation and the Wasm instructions it ran.
-/
import L4Factoidal.WasmVM.WasiIO
import L4Factoidal.WasmVM.Hosts.Dom
import L4Factoidal.WasmVM.Bench.Sample
import L4Factoidal.WasmVM.Hosts.Page
import L4Factoidal.DOM.OfHtml
import Lean.Data.Json

namespace L4Factoidal.WasmVM.Bench.QuickJS
open L4Factoidal.WasmVM L4Factoidal.WasmVM.Wasi L4Factoidal.DOM
open Lean (Json)

def jn (n : Nat) : Json := .num (Lean.JsonNumber.fromNat n)

/-- Since 2026-11-08 the module runs as a page session (`Hosts.Page`): the WASI clock is
the event loop's, `foafnaut_dom` is served on a Lean DOM arena, and Lean runs the
microtask checkpoint (`runJobs`). -/
abbrev Vm := Hosts.Page.Session

structure Timed where
  status : Nat
  text : String
  steps : Nat
  ns : Nat

/-- Evaluate `src`, then the microtask checkpoint; the instructions and the wall time. -/
def evalTimed (v : Vm) (src : String) : IO (Vm × Timed) := do
  let t0 ← IO.monoNanosNow
  let n0 := v.steps
  let (v, status, text) := v.eval src
  let v := v.runJobs
  let t1 ← IO.monoNanosNow
  return (v, ⟨status, text, v.steps - n0, t1 - t0⟩)

/-- Load the module on the arena of `html`, run `_initialize`, `qjs_new` and page mode. -/
def start (bytes : ByteArray) (html : String) : IO (Hosts.Page.Module' × Vm) := do
  let m ← match Hosts.Page.prepare bytes with
    | .ok m => pure m
    | .error e => throw (IO.userError e)
  match Hosts.Page.instantiatePage m (parseHtmlDocument html) with
  | .ok v => return (m, v)
  | .error e => throw (IO.userError e)

/-! ## Plain JavaScript -/

def plainCases : List (String × String × String) := [
  ("arithmetic", "1 + 2 * 3 - 4 / 2", "5"),
  ("numbers", "[0.1 + 0.2, 2 ** 53 + 1, (255).toString(16), Number('1e3'), Math.max(3, 9, 4)].join(' ')",
    "0.30000000000000004 9007199254740992 ff 1000 9"),
  ("strings", "'abc'.toUpperCase() + '-' + 'x'.repeat(3) + '-' + '  trim '.trim() + '-' + 'é€😀'.length",
    "ABC-xxx-trim-4"),
  ("closures", "(() => { let c = 0; const inc = () => ++c; inc(); inc(); return inc(); })()", "3"),
  ("arrays", "[5, 3, 9, 1].sort((a, b) => a - b).map(x => x * 2).filter(x => x > 2).join(',')", "6,10,18"),
  ("JSON", "JSON.stringify(JSON.parse('{\"a\":[1,2,{\"b\":null}],\"c\":\"\\\\u00e9\"}'))",
    "{\"a\":[1,2,{\"b\":null}],\"c\":\"é\"}"),
  ("try/catch", "(() => { try { null.x } catch (e) { return e instanceof TypeError && e.message.length > 0 } })()",
    "true"),
  ("class", "class P { #x; constructor(x) { this.#x = x } get double() { return this.#x * 2 } static of(x) { return new P(x) } }; P.of(21).double",
    "42"),
  ("inheritance", "class A { hi() { return 'A' } }; class B extends A { hi() { return super.hi() + 'B' } }; new B().hi()",
    "AB"),
  ("destructuring", "const { a, b: [c, ...d] } = { a: 1, b: [2, 3, 4] }; `${a}${c}${d}`", "123,4"),
  ("Map and Set", "const m = new Map([[1, 'one']]); m.set(2, 'two'); [...m.values(), new Set([1, 1, 2]).size].join()",
    "one,two,2"),
  ("generators", "function* g() { yield 1; yield 2; yield 3 }; [...g()].reduce((a, b) => a + b)", "6"),
  ("regular expressions", "'2026-11-08'.replace(/(\\d+)-(\\d+)-(\\d+)/, '$3/$2/$1') + ' ' + /\\p{L}+/u.exec('42 Grüße')[0]",
    "08/11/2026 Grüße"),
  ("BigInt", "(2n ** 64n).toString()", "18446744073709551616"),
  ("Date.now is the virtual clock", "Date.now() + ' ' + new Date(0).toISOString()", "0 1970-01-01T00:00:00.000Z"),
  ("Intl-free toLocaleString", "(1234.5).toFixed(2)", "1234.50"),
  ("promises and microtasks", "var order = []; Promise.resolve(1).then(v => order.push('then ' + v)); queueMicrotask(() => order.push('micro')); order.push('sync'); order.join()",
    "sync"),
  ("after the microtask checkpoint", "order.join()", "sync,then 1,micro"),
  ("async function", "var got; (async () => { got = await Promise.resolve(7) * 6 })(); 'started'", "started"),
  ("awaited value", "got", "42"),
  ("no host objects", "[typeof process, typeof require, typeof fetch, typeof XMLHttpRequest, typeof WebAssembly].join()",
    "undefined,undefined,undefined,undefined,undefined"),
  ("thrown error", "throw new RangeError('boom')", "RangeError: boom"),
  ("syntax error", "let = ;", "SyntaxError"),
  ("recursion", "function fib(n) { return n < 2 ? n : fib(n - 1) + fib(n - 2) }; fib(20)", "6765"),
  ("deep recursion is caught", "(() => { function f(n) { return f(n + 1) + 1 } try { f(0) } catch (e) { return e instanceof RangeError } })()",
    "true")]

/-! ## Scripted pages -/

def attrVal (n : Node) (name : String) : String :=
  ((n.attrs.find? (fun a => a.ns.isNone && a.lname == name)).map (·.value)).getD ""

/-- Element snapshot, as `WebRenderScript.snapshot` gives it to the host-run path. -/
def snapshot (d : Dom) : Json := Id.run do
  let mut nodes : Array Json := #[]
  for id in d.treeOrder 0 do
    let n := d.get id
    if n.type == .element then
      let attrs := n.attrs.toList.filter (·.ns.isNone)
      nodes := nodes.push (Json.mkObj [("id", jn id), ("tagName", Json.str n.lname),
        ("attributes", Json.mkObj (attrs.map fun a => (a.qname, Json.str a.value))),
        ("textContent", Json.str ((d.textContent id).getD ""))])
  return Json.arr nodes

/-- The classic scripts in tree order. -/
def scripts (d : Dom) : Array String := Id.run do
  let mut out := #[]
  for id in d.treeOrder 0 do
    let n := d.get id
    if n.type == .element && Dom.isHtmlElement n "script" then
      let ty := (attrVal n "type").trimAscii.toString.toLower
      if ["", "text/javascript", "application/javascript", "module"].contains ty && ty != "module" then
        out := out.push ((d.textContent id).getD "")
  return out

def commandJson : Hosts.Dom.Command → Json
  | .setTextContent n v => Json.mkObj [("op", Json.str "setTextContent"), ("nodeId", jn n), ("value", Json.str v)]
  | .setAttribute n k v => Json.mkObj [("op", Json.str "setAttribute"), ("nodeId", jn n), ("name", Json.str k), ("value", Json.str v)]
  | .createElement k n => Json.mkObj [("op", Json.str "createElement"), ("name", Json.str k), ("nodeId", jn n)]
  | .appendChild p c => Json.mkObj [("op", Json.str "appendChild"), ("parent", jn p), ("nodeId", jn c)]
  | .removeAttribute n k => Json.mkObj [("op", Json.str "removeAttribute"), ("nodeId", jn n), ("name", Json.str k)]
  | .createNode k d n => Json.mkObj [("op", Json.str "createNode"), ("kind", jn k), ("data", Json.str d), ("nodeId", jn n)]
  | .createElementNS ns q n => Json.mkObj [("op", Json.str "createElementNS"), ("namespace", Json.str ns), ("name", Json.str q), ("nodeId", jn n)]
  | .insertBefore p c b => Json.mkObj [("op", Json.str "insertBefore"), ("parent", jn p), ("nodeId", jn c), ("before", match b with | some k => jn k | none => Json.null)]
  | .removeChild p c => Json.mkObj [("op", Json.str "removeChild"), ("parent", jn p), ("nodeId", jn c)]
  | .replaceChild p n c => Json.mkObj [("op", Json.str "replaceChild"), ("parent", jn p), ("nodeId", jn n), ("child", jn c)]
  | .cloneNode n d r => Json.mkObj [("op", Json.str "cloneNode"), ("source", jn n), ("deep", Json.bool d), ("nodeId", jn r)]
  | .normalize n => Json.mkObj [("op", Json.str "normalize"), ("nodeId", jn n)]
  | .setAttributeNS n ns q v => Json.mkObj [("op", Json.str "setAttributeNS"), ("nodeId", jn n), ("namespace", Json.str ns), ("name", Json.str q), ("value", Json.str v)]
  | .removeAttributeNS n ns l => Json.mkObj [("op", Json.str "removeAttributeNS"), ("nodeId", jn n), ("namespace", Json.str ns), ("name", Json.str l)]
  | .adoptNode n doc => Json.mkObj [("op", Json.str "adoptNode"), ("nodeId", jn n), ("document", jn doc)]
  | .importNode n doc deep r => Json.mkObj [("op", Json.str "importNode"), ("source", jn n), ("document", jn doc), ("deep", Json.bool deep), ("nodeId", jn r)]
  | .setChecked n v => Json.mkObj [("op", Json.str "setChecked"), ("nodeId", jn n), ("value", Json.bool v)]
  | .resetForm n => Json.mkObj [("op", Json.str "resetForm"), ("nodeId", jn n)]
  | .replaceData n o k v => Json.mkObj [("op", Json.str "replaceData"), ("nodeId", jn n), ("offset", jn o), ("count", jn k), ("value", Json.str v)]
  | .splitText n o r => Json.mkObj [("op", Json.str "splitText"), ("source", jn n), ("offset", jn o), ("nodeId", jn r)]
  | .frameDocument el src xml r => Json.mkObj [("op", Json.str "frameDocument"), ("frame", jn el), ("source", Json.str src), ("xml", Json.bool xml), ("nodeId", jn r)]
  | .attachShadow h f r => Json.mkObj [("op", Json.str "attachShadow"), ("host", jn h), ("flags", jn f), ("nodeId", jn r)]
  | .assignSlot sl ns => Json.mkObj [("op", Json.str "assignSlot"), ("nodeId", jn sl), ("nodes", Json.arr (ns.map jn))]

/-- One turn: its commands, logs and whether the default was prevented. -/
structure Batch where
  commands : Array Json
  logs : Array String
  prevented : Bool
  errors : Array String
  steps : Nat
  ns : Nat

def Batch.json (b : Batch) : Json :=
  Json.mkObj [("commands", Json.arr b.commands), ("logs", Json.arr (b.logs.map Json.str)),
    ("defaultPrevented", Json.bool b.prevented)]

/-- The host's commands, logs and errors since the marks. -/
def take (v : Vm) (mc ml me : Nat) : Array Json × Array String × Array String :=
  ((v.commands.extract mc v.commands.size).map commandJson, v.logs.extract ml v.logs.size,
    v.errors.extract me v.errors.size)

/-- A page and the `id`s of the elements to click, in order. -/
structure Page where
  name : String
  html : String
  clicks : List String
  /-- Expected text of the body after the clicks and timers, when there is no reference. -/
  expect : Option String := none

def runPage (m : Hosts.Page.Module') (p : Page) : IO (Array Batch × Dom × Array Nat × Json × Array String) := do
  let dom := parseHtmlDocument p.html
  let snap := snapshot dom
  let srcs := scripts dom
  let scriptNodes := (dom.treeOrder 0).filter fun k => Dom.isHtmlElement (dom.get k) "script"
  let t0 ← IO.monoNanosNow
  let v ← match Hosts.Page.start m dom "about:blank" (scriptNodes.zip srcs) with
    | .ok v => pure v
    | .error e => throw (IO.userError e)
  let t1 ← IO.monoNanosNow
  let (cs, ls, es) := take v 0 0 0
  let mut v := v
  let mut batches := #[({ commands := cs, logs := ls, prevented := false, errors := es, steps := v.steps, ns := t1 - t0 } : Batch)]
  let mut clickIds := #[]
  for target in p.clicks do
    let node := (dom.getElementById 0 target).getD 0
    clickIds := clickIds.push node
    let (mc, ml, me, n0) := (v.commands.size, v.logs.size, v.errors.size, v.steps)
    let a ← IO.monoNanosNow
    -- A click is a task of the user interaction source; the bench dispatches it at once
    -- to read `defaultPrevented`, as `Session.click` does when its task runs.
    let (v', prevented) := v.dispatch node "click"
    v := v'
    let b ← IO.monoNanosNow
    let (cs, ls, es) := take v mc ml me
    batches := batches.push ({ commands := cs, logs := ls, prevented, errors := es, steps := v.steps - n0, ns := b - a } : Batch)
  let (mc, ml, me, n0) := (v.commands.size, v.logs.size, v.errors.size, v.steps)
  let (v2, _) := v.settle 60000
  v := v2
  if v.tasks > 0 && (v.commands.size > mc || v.logs.size > ml) then
    let (cs, ls, es) := take v mc ml me
    batches := batches.push ({ commands := cs, logs := ls, prevented := false, errors := es, steps := v.steps - n0, ns := 0 } : Batch)
  return (batches, v.host.dom.dom, clickIds, Json.mkObj [("nodes", snap), ("sources", Json.arr (srcs.map Json.str)),
    ("clicks", Json.arr (clickIds.map fun n => jn n))], srcs)

def fixtureDir : System.FilePath := "../../labs/demos/foafnaut/web-render/fixtures"

def pages : IO (List Page) := do
  let scripted ← IO.FS.readFile (fixtureDir / "scripted.html")
  let mvp ← IO.FS.readFile (fixtureDir / "mvp.html")
  return [
    { name := "fixtures/scripted.html", html := scripted, clicks := ["change", "change"] },
    { name := "fixtures/mvp.html", html := mvp, clicks := ["change", "change", "change"] },
    { name := "two scripts share bindings; this and event.type", clicks := ["change", "change"],
      html := "<p id=message>before</p><a id=change href=#change>Change</a>" ++
        "<script>let count = 1; document.getElementById(\"message\").textContent = \"loaded\";</script>" ++
        "<script>document.querySelector(\"#change\").addEventListener(\"click\", function(event) { " ++
        "document.getElementById(\"message\").textContent = \"click \" + count++; this.setAttribute(\"data-clicked\", event.type); });</script>" },
    { name := "preventDefault is seen by the next listener", clicks := ["change"],
      html := "<p id=message>before</p><a id=change href=#change>Change</a><script>" ++
        "const a = document.getElementById('change');" ++
        "a.addEventListener('click', e => { console.log('first', e.defaultPrevented); e.preventDefault(); });" ++
        "a.addEventListener('click', e => { console.log('second', e.defaultPrevented); });</script>" },
    -- Not compared with host-run QuickJS: host-reference.mjs runs guest.mjs without the
    -- Lean DOM binding, which is where the host-run path checks attribute names.
    { name := "getAttribute, a refused attribute name, and a caught error", clicks := [],
      expect := some "1  InvalidCharacterError",
      html := "<p id=message data-x=1>before</p><script>" ++
        "const m = document.getElementById('message');" ++
        "let r; try { m.setAttribute('bad name', 'v'); r = 'no error' } catch (e) { r = e.name }" ++
        "m.textContent = [m.getAttribute('data-x'), m.getAttribute('missing'), r].join(' ');</script>" },
    { name := "timers: setTimeout order, setInterval, clearInterval (Lean runs the timers)", clicks := [],
      expect := some "a b c tick1 tick2 tick3 done",
      html := "<p id=out></p><script>" ++
        "const out = document.getElementById('out'); const log = [];" ++
        "const show = () => out.textContent = log.join(' ');" ++
        "setTimeout(() => { log.push('c'); show() }, 20);" ++
        "setTimeout(() => { log.push('a'); show() }, 0);" ++
        "setTimeout(() => { log.push('b'); show() }, 10);" ++
        "let n = 0; const iv = setInterval(() => { log.push('tick' + (++n)); if (n === 3) { clearInterval(iv); setTimeout(() => { log.push('done'); show() }, 5) } show() }, 25);" ++
        "const never = setTimeout(() => log.push('never'), 1); clearTimeout(never);</script>" },
    { name := "createElement and appendChild", clicks := ["add", "add"],
      expect := some "Item 1Item 2Item 3add",
      html := "<ul id=list></ul><button id=add>add</button><script>" ++
        "let k = 0; const list = document.getElementById('list');" ++
        "const add = () => { const li = document.createElement('LI'); li.textContent = 'Item ' + (++k); li.setAttribute('class', 'item'); list.appendChild(li); };" ++
        "add(); document.getElementById('add').onclick = add;</script>" },
    { name := "promise jobs run after each script and each callback", clicks := ["b"],
      expect := some "sync micro click click-micro",
      html := "<p id=out></p><button id=b></button><script>" ++
        "const out = document.getElementById('out'); const log = []; const show = () => out.textContent = log.join(' ');" ++
        "Promise.resolve().then(() => { log.push('micro'); show() }); log.push('sync'); show();" ++
        "document.getElementById('b').addEventListener('click', () => { log.push('click'); queueMicrotask(() => { log.push('click-micro'); show() }) });</script>" }]

/-- Body text of the arena (the `body` element's descendant text, minus scripts). -/
def bodyText (d : Dom) : String := Id.run do
  let some b := (d.treeOrder 0 false).find? (fun k => Dom.isHtmlElement (d.get k) "body") | return ""
  let mut out := ""
  for k in d.treeOrder b false do
    let n := d.get k
    if n.type == .text then
      let inScript := match n.parent with
        | some p => Dom.isHtmlElement (d.get p) "script"
        | none => false
      if !inScript then out := out ++ n.data
  return out.trimAscii.toString

/-- The host-run QuickJS result for the same snapshot, sources and clicks. -/
def reference (reactor : String) (req : Json) : IO (Except String (Array Json)) := do
  let cfg : IO.Process.SpawnArgs := { cmd := "node", args := #["../../tools/wasmvm/quickjs/host-reference.mjs", reactor] }
  let child ← IO.Process.spawn { cfg with stdin := IO.Process.Stdio.piped, stdout := IO.Process.Stdio.piped, stderr := IO.Process.Stdio.piped }
  let (stdin, child) ← child.takeStdin
  stdin.putStr req.compress
  stdin.flush
  let out ← child.stdout.readToEnd
  let err ← child.stderr.readToEnd
  let code ← child.wait
  if code != 0 then return .error s!"node exit {code}: {err}"
  match Json.parse out.trimAscii.toString with
  | .error e => return .error s!"reference output: {e}"
  | .ok j =>
    match j.getObjValAs? (Array Json) "batches", j.getObjValAs? String "error" with
    | .ok bs, .error _ => return .ok bs
    | .ok _, .ok e => return .error s!"reference: {e}"
    | .error e, _ => return .error s!"reference output: {e}"

def run (path : String) (reactor : Option String) : IO UInt32 := do
  let bytes ← IO.FS.readBinFile path
  let t0 ← IO.monoNanosNow
  let (m, v) ← start bytes "<!doctype html><title>plain</title>"
  let t1 ← IO.monoNanosNow
  IO.println s!"module: {bytes.size} bytes; decode, validate, instantiate, _initialize and qjs_new: {(t1 - t0) / 1000000} ms"
  IO.println s!"imports: {v.bindings.toList.map fun b => match b with | .wasi f => f.name | .extra m x => s!"{m}.{x}"}"
  let mut v := v
  let mut fails := 0
  let mut passes := 0
  let mut totalSteps := 0
  let mut totalNs := 0
  IO.println "\n# Plain JavaScript"
  for (what, src, want) in plainCases do
    let (v', t) ← evalTimed v src
    v := v'
    totalSteps := totalSteps + t.steps; totalNs := totalNs + t.ns
    let got := (t.text.splitOn "\n").head!
    let ok := if t.status == 1 then got.startsWith want else got == want
    if ok then passes := passes + 1 else fails := fails + 1
    let mips := if t.ns == 0 then 0 else t.steps * 1000 / t.ns
    IO.println s!"{if ok then "ok  " else "FAIL"} {what}: {got}{if ok then "" else s!" (expected {want})"} [{t.steps} instr, {t.ns / 1000} us, {mips} M instr/s]"
  IO.println s!"plain JavaScript: {passes} pass, {fails} fail; {totalSteps} instructions in {totalNs / 1000000} ms ({if totalNs == 0 then 0 else totalSteps * 1000 / totalNs} M instr/s)"
  Sample.report "QuickJS plain cases"
  -- A longer run for the speed figure.
  let (v', t) ← evalTimed v "(() => { let s = 0; for (let i = 0; i < 200000; i++) s = (s + i * i) % 1000003; const o = []; for (let i = 0; i < 2000; i++) o.push({ k: 'k' + i, v: i }); return s + ' ' + JSON.stringify(o).length })()"
  v := v'
  IO.println s!"speed: loop and JSON: {t.text}: {t.steps} instructions in {t.ns / 1000000} ms = {if t.ns == 0 then 0 else t.steps * 1000 / t.ns} M instr/s"
  Sample.report "QuickJS loop and JSON"
  let (_, t) ← evalTimed v "function fib(n) { return n < 2 ? n : fib(n - 1) + fib(n - 2) }; fib(24)"
  IO.println s!"speed: fib(24) = {t.text}: {t.steps} instructions in {t.ns / 1000000} ms = {if t.ns == 0 then 0 else t.steps * 1000 / t.ns} M instr/s"
  Sample.report "QuickJS fib(24)"
  IO.println "\n# Scripted pages (Lean DOM, Lean dispatch)"
  let mut same := 0
  let mut differ := 0
  let mut notCompared := 0
  for p in ← pages do
    let (batches, dom, _, req, _) ← runPage m p
    IO.println s!"{p.name}:"
    for b in batches do
      IO.println s!"  turn: {(Json.arr b.commands).compress} logs {b.logs.toList} prevented {b.prevented}{if b.errors.isEmpty then "" else s!" errors {b.errors.toList}"} [{b.steps} instr, {b.ns / 1000} us]"
    let text := bodyText dom
    IO.println s!"  body text after: {repr text}"
    match p.expect with
    | some want =>
      if text == want then same := same + 1; IO.println "  same as expected"
      else differ := differ + 1; IO.println s!"  DIFFERS from expected {repr want}"
    | none =>
      match reactor with
      | none => notCompared := notCompared + 1; IO.println "  not compared (no reactor given)"
      | some r =>
        match ← reference r req with
        | .error e => differ := differ + 1; IO.println s!"  reference failed: {e}"
        | .ok refs =>
          let mine := batches.map (·.json.compress)
          let theirs := refs.map (·.compress)
          if mine == theirs then same := same + 1; IO.println "  same commands, logs and defaultPrevented as host-run QuickJS"
          else
            differ := differ + 1
            IO.println s!"  DIFFERS from host-run QuickJS: {theirs.toList}"
  IO.println s!"scripted pages: {same} same, {differ} differ, {notCompared} not compared"
  return if fails == 0 && differ == 0 then 0 else 1

end L4Factoidal.WasmVM.Bench.QuickJS
