/-
L4Factoidal.WasmVM.Bench.Page: run a page with `Hosts.Page` from the command line
(record: docs/designissues/2026-11-08-page-scripts.md).

`lake exe wasmvm-bench page WASM ROOT FILE... [--settle MS] [--commands N]`

For each FILE (an HTML file, a path under ROOT or absolute), the page is parsed with the
Lean HTML parser, its classic scripts run in document order (a `src` script is read from
ROOT for a path that starts with `/`, else beside the file), and the event loop runs until
nothing waits or MS virtual milliseconds pass (default 30000). One JSON line per page:
the logs, the errors, the body text, the command count, the clock, the instructions and
the wall time. The engine op `scriptSession` (`labs/demos/foafnaut/WebScripts.lean`) runs
the same session.
-/
import L4Factoidal.WasmVM.Hosts.Page
import L4Factoidal.DOM.OfHtml
import L4Factoidal.DOM.OfXml
import Lean.Data.Json

namespace L4Factoidal.WasmVM.Bench.Page
open L4Factoidal.WasmVM L4Factoidal.WasmVM.Hosts.Page L4Factoidal.DOM
open Lean (Json)

def attrVal (n : Node) (name : String) : Option String :=
  (n.attrs.find? (fun a => a.ns.isNone && a.lname == name)).map (·.value)

/-- Classic scripts in tree order: (node, src attribute or none, inline text). -/
def scriptElements (d : Dom) : Array (Nat × Option String × String) := Id.run do
  let mut out := #[]
  for id in d.treeOrder 0 do
    let n := d.get id
    if n.type == .element && Dom.isHtmlElement n "script" then
      let ty := ((attrVal n "type").getD "").trimAscii.toString.toLower
      if ["", "text/javascript", "application/javascript", "text/ecmascript", "application/ecmascript"].contains ty then
        out := out.push (id, attrVal n "src", (d.textContent id).getD "")
  return out

def readScript (root dir : System.FilePath) (src : String) : IO String := do
  let path := (src.splitOn "?").head!
  let file : System.FilePath := if path.startsWith "/" then root / (path.drop 1).toString else dir / path
  try IO.FS.readFile file catch _ => return s!"throw new Error('script not found: {src}')"

/-- The `iframe` elements of the page in tree order, with their `src`. -/
def iframeElements (d : Dom) : Array (Nat × Option String) := Id.run do
  let mut out := #[]
  for id in d.treeOrder 0 do
    let n := d.get id
    if n.type == .element && Dom.isHtmlElement n "iframe" then out := out.push (id, attrVal n "src")
  return out

/-- The document of a frame: `about:blank` with no `src`; a file under ROOT (a path that
starts with `/`) or beside the page, as XML for `.xml`, `.xhtml` and `.svg`, else HTML.
A file that is missing or not well-formed gives no frame. -/
def frameDocument (root dir : System.FilePath) (src : Option String) : IO (Option Dom) := do
  match src with
  | none => return some Hosts.Dom.aboutBlank
  | some src =>
    let src := if src.startsWith "http://web-platform.test/" then (src.drop 24).toString else src
    let path := ((src.splitOn "#").head!.splitOn "?").head!
    if path.isEmpty || path == "about:blank" then return some Hosts.Dom.aboutBlank
    if path.startsWith "http:" || path.startsWith "https:" || path.startsWith "data:" then return none
    let file : System.FilePath := if path.startsWith "/" then root / (path.drop 1).toString else dir / path
    let text ← try IO.FS.readFile file catch _ => return none
    if path.endsWith ".xml" || path.endsWith ".xhtml" || path.endsWith ".svg" then
      let ct := if path.endsWith ".xhtml" then "application/xhtml+xml" else if path.endsWith ".svg" then "image/svg+xml" else "application/xml"
      return (parseXmlDocument text).toOption.map fun d => d.setNode 0 fun n => { n with contentType := ct }
    return some (parseHtmlDocument text)

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

def jn (n : Nat) : Json := .num (Lean.JsonNumber.fromNat n)

def run (args : List String) : IO UInt32 := do
  let (wasm, root, rest) ← match args with
    | w :: r :: rest => pure (w, r, rest)
    | _ => throw (IO.userError "usage: wasmvm-bench page WASM ROOT FILE... [--settle MS] [--commands N] [--instructions-per-ms N]")
  let mut files : Array String := #[]
  let mut settleMs := 30000
  let mut commands := 4096
  -- The rate of the script clock (`ScriptClock`): the engine's by default.
  let mut rate := 100000
  let xs := rest.toArray
  let mut i := 0
  while i < xs.size do
    match xs[i]! with
    | "--settle" => settleMs := (xs[i+1]?.bind String.toNat?).getD settleMs; i := i + 2
    | "--commands" => commands := (xs[i+1]?.bind String.toNat?).getD commands; i := i + 2
    | "--instructions-per-ms" => rate := max 1 ((xs[i+1]?.bind String.toNat?).getD rate); i := i + 2
    | f => files := files.push f; i := i + 1
  let t0 ← IO.monoNanosNow
  let bytes ← IO.FS.readBinFile wasm
  let m ← match prepare bytes with
    | .ok m => pure m
    | .error e => throw (IO.userError e)
  let t1 ← IO.monoNanosNow
  IO.eprintln s!"module: {bytes.size} bytes, decode and validate {(t1 - t0) / 1000000} ms"
  let mut bad := 0
  for f in files do
    let file : System.FilePath := if f.startsWith "/" then f else System.FilePath.mk root / f
    let html ← IO.FS.readFile file
    let dom := parseHtmlDocument html
    let dir := file.parent.getD "."
    let mut scripts := #[]
    for (node, src, text) in scriptElements dom do
      let source ← match src with
        | some s => readScript root dir s
        | none => pure text
      scripts := scripts.push (node, source)
    let mut frames := #[]
    for (node, src) in iframeElements dom do
      if let some fd ← frameDocument root dir src then frames := frames.push (node, fd)
    let a ← IO.monoNanosNow
    match start m dom ("http://web-platform.test/" ++ f) scripts { commands, logs := 100000, frames := true } frames {}
        { instructionsPerMs := rate } with
    | .error e =>
      bad := bad + 1
      IO.println (Json.mkObj [("file", .str f), ("error", .str e)]).compress
    | .ok s =>
      let b ← IO.monoNanosNow
      -- Settle; answer the navigations of iframes the page made; settle again.
      let (s0, quiet0) := s.settle settleMs
      let mut s := s0
      let mut quiet := quiet0
      for _ in [0:256] do
        let loads := s.frameLoads
        if loads.isEmpty || s.loop.clock ≥ settleMs then break
        for (el, url) in loads do
          s := s.attachFrame el (← frameDocument root dir (some url))
        let (s', q) := s.settle (settleMs - s.loop.clock)
        s := s'; quiet := q
      let c ← IO.monoNanosNow
      IO.println (Json.mkObj [("file", .str f), ("quiet", .bool quiet), ("clock", jn s.loop.clock),
        ("logs", .arr (s.logs.map .str)), ("errors", .arr (s.errors.map .str)),
        ("commands", jn s.commands.size), ("tasks", jn s.tasks), ("jobs", jn s.jobs),
        ("instructions", jn s.steps), ("startMs", jn ((b - a) / 1000000)), ("settleMs", jn ((c - b) / 1000000)),
        ("body", .str ((bodyText s.host.dom.dom).take 400).toString)]).compress
  return if bad == 0 then 0 else 1

end L4Factoidal.WasmVM.Bench.Page
