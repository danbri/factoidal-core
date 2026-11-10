import L4Factoidal.WasmVM.Hosts.LeanJS
import L4Factoidal.DOM.OfHtml

/-!
# XMLHttpRequest on BubblePopJS

`Net.Xhr` and the glue of `prelude.js`, checked at build time: a page's request is asked of the
embedder, the answer arrives as a task, and the events, state and text are the standard's.
A cross-origin answer without CORS is not visible; a local target from a public page never reaches
the embedder; `abort` and `timeout` give their events; and a host that did not turn the
network on has no `XMLHttpRequest` at all.
-/
namespace L4Factoidal.WasmVM.Tests.LeanJSNet
open L4Factoidal L4Factoidal.WasmVM.Hosts L4Factoidal.Net.PageFetch

def scriptsOf (dom : DOM.Dom) : Array (Nat × String) :=
  ((dom.treeOrder 0).toList.filter fun k => DOM.Dom.isHtmlElement (dom.get k) "script").toArray.map
    fun k => (k, (dom.textContent k).getD "")

def startPage (src : String) (network : Bool := true) (url : String := "http://a.test/p.html") : Except String LeanJS.Session := do
  let base ← LeanJS.prepareSource
  let dom := DOM.parseHtmlDocument ("<!doctype html><script>" ++ src ++ "</script>")
  return LeanJS.start base dom url (scriptsOf dom) { network } {} { instructionsPerMs := 1000000000000 }

/-- Give every waiting request of the page's outbox its answer, then run the loop. -/
def answerAll (s : LeanJS.Session) (a : Wire → Answer) : LeanJS.Session := Id.run do
  let e := LeanJS.engine
  let mut net := s.host.web.net
  let wires := net.outbox
  net := { net with outbox := #[] }
  let mut loop := s.host.loop
  for w in wires do
    let (n', cb) := Net.Xhr.give net w.id (a w)
    net := n'
    if let some c := cb then loop := loop.queueTask .networking c
  let s := s.setHost { s.host with web := { s.host.web with net }, loop }
  return (e.settle s 1000).1

def logOf (s : LeanJS.Session) : List String := s.host.dom.logs.toList

/-- A page script that logs each event of one XHR by name and readyState. -/
def track : String :=
  "const x = new XMLHttpRequest(); const log = (m) => console.log(m);" ++
  "x.onreadystatechange = () => log('rs ' + x.readyState);" ++
  "for (const t of ['loadstart','progress','load','loadend','error','abort','timeout'])" ++
  "  x.addEventListener(t, e => log(t + ' ' + e.loaded + ' ' + x.readyState + ' ' + x.status));"

def sameOriginText : Except String (List String) := do
  let s ← startPage (track ++ "x.open('GET','/d.txt');x.send();x.onload=()=>log(x.responseText+'|'+x.getResponseHeader('X-Y')+'|'+x.getAllResponseHeaders()+'|'+x.responseURL);")
  let s := answerAll s fun w =>
    { status := 200, statusText := "OK", headers := [("Content-Type", "text/plain; charset=utf-8"), ("X-Y", "z")], body := "héllo".toUTF8, url := w.url }
  return logOf s

#guard sameOriginText == .ok ["rs 1", "loadstart 0 1 0", "rs 2", "rs 3", "progress 6 3 200", "rs 4",
  "load 6 4 200", "héllo|z|content-type: text/plain; charset=utf-8\r\nx-y: z\r\n|http://a.test/d.txt", "loadend 6 4 200"]

-- A cross-origin answer with no CORS header: error, and the page reads nothing.
def crossNoCors : Except String (List String) := do
  let s ← startPage (track ++ "x.open('GET','http://b.test/secret');x.send();x.onloadend=()=>log('['+x.responseText+x.status+']');")
  let s := answerAll s fun _ => { status := 200, body := "secret".toUTF8 }
  return logOf s

#guard crossNoCors == .ok ["rs 1", "loadstart 0 1 0", "rs 4", "error 0 4 0", "loadend 0 4 0", "[0]"]

-- With `Access-Control-Allow-Origin` it is read, and only safelisted fields.
def crossCors : Except String (List String) := do
  let s ← startPage ("const x = new XMLHttpRequest();x.open('GET','http://b.test/d');x.send();x.onload=()=>console.log(x.responseText,x.getResponseHeader('X-Y'));")
  let s := answerAll s fun _ => { status := 200, headers := [("access-control-allow-origin", "http://a.test"), ("x-y", "1")], body := "ok".toUTF8 }
  return logOf s

#guard crossCors == .ok ["ok null"]

-- A public page cannot name a local target: nothing reaches the embedder.
def localRefused : Except String (Nat × List String) := do
  let s ← startPage ("const x = new XMLHttpRequest();x.open('GET','http://127.0.0.1:8000/x');x.send();console.log('sent');x.onerror=()=>console.log('err',x.status);x.onload=()=>console.log('LOADED');")
  let wires := s.host.web.net.outbox.size
  let s := (LeanJS.engine.settle s 1000).1
  return (wires, logOf s)

#guard localRefused == .ok (0, ["sent", "err 0"])

-- abort() during send, and a `timeout` that fires before any answer.
def abortFlow : Except String (List String) := do
  let s ← startPage (track ++ "x.open('GET','/x');x.send();x.abort();log('after '+x.readyState);")
  return logOf s

#guard abortFlow == .ok ["rs 1", "loadstart 0 1 0", "rs 4", "abort 0 4 0", "loadend 0 4 0", "after 0"]

def timeoutFlow : Except String (List String) := do
  let s ← startPage (track ++ "x.open('GET','/x');x.timeout=500;x.send();")
  let e := LeanJS.engine
  let s := (e.advance s ((e.loop s).clock + 600)).1
  return logOf s

#guard timeoutFlow == .ok ["rs 1", "loadstart 0 1 0", "rs 4", "timeout 0 4 0", "loadend 0 4 0"]

-- Errors: forbidden method, forbidden header silently dropped.
def errors : Except String (List String) := do
  let s ← startPage ("const x = new XMLHttpRequest();try{x.open('TRACE','/x')}catch(e){console.log(e.name)}" ++
    "x.open('GET','/x');x.setRequestHeader('Cookie','a=1');x.setRequestHeader('X-A','1');try{x.setRequestHeader('X-A','a\\nb')}catch(e){console.log(e.name)}x.send();")
  return logOf s

#guard errors == .ok ["SecurityError", "SyntaxError"]

-- Sync: the first run stops and asks; the run again with the answer goes through.
def syncFlow : Except String (Option String × List String) := do
  let base ← LeanJS.prepareSource
  let src := "const x = new XMLHttpRequest(); x.open('GET','/s', false); x.onload=()=>console.log('load',x.status,x.responseText); x.send(); console.log('after',x.readyState);"
  let dom := DOM.parseHtmlDocument ("<!doctype html><script>" ++ src ++ "</script>")
  let s0 := LeanJS.start base dom "http://a.test/p.html" (scriptsOf dom) { network := true, syncOk := true } {} { instructionsPerMs := 1000000000000 }
  let wanted := s0.host.web.net.syncWanted.map (·.url)
  let a : Answer := { status := 200, statusText := "OK", body := "sync".toUTF8 }
  let s1 := LeanJS.start base dom "http://a.test/p.html" (scriptsOf dom) { network := true, syncOk := true, syncAnswers := #[a] } {} { instructionsPerMs := 1000000000000 }
  return (wanted, logOf s1)

#guard syncFlow == .ok (some "http://a.test/s", ["load 200 sync", "after 4"])

-- fetch: same core, the promise resolves with the body.
def fetchFlow : Except String (List String) := do
  let s ← startPage ("fetch('/d').then(r=>r.text().then(t=>console.log(r.status,r.ok,r.headers.get('X-Y'),t)));")
  let s := answerAll s fun _ => { status := 200, statusText := "OK", headers := [("X-Y", "z")], body := "ok".toUTF8 }
  return logOf s

#guard fetchFlow == .ok ["200 true z ok"]

-- fetch: a cross-origin answer with no CORS rejects, and nothing reaches the page.
def fetchRefused : Except String (List String) := do
  let s ← startPage ("fetch('http://b.test/x').then(r=>console.log('resolved'),e=>console.log(e.name));")
  let s := answerAll s fun _ => { status := 200, body := "secret".toUTF8 }
  return logOf s

#guard fetchRefused == .ok ["TypeError"]

-- Off when the embedder does not turn it on: no such global.
def off : Except String (List String) := do
  let s ← startPage "console.log(typeof XMLHttpRequest);" false
  return logOf s

#guard off == .ok ["undefined"]

end L4Factoidal.WasmVM.Tests.LeanJSNet
