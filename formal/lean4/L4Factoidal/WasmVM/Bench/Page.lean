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
    | _ => throw (IO.userError "usage: wasmvm-bench page WASM ROOT FILE... [--settle MS] [--commands N]")
  let rec opts : List String → List String × Nat × Nat
    | "--settle" :: v :: xs => let (f, _, c) := opts xs; (f, v.toNat!, c)
    | "--commands" :: v :: xs => let (f, s, _) := opts xs; (f, s, v.toNat!)
    | x :: xs => let (f, s, c) := opts xs; (x :: f, s, c)
    | [] => ([], 30000, 4096)
  let (files, settleMs, commands) := opts rest
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
    let a ← IO.monoNanosNow
    match start m dom ("http://web-platform.test/" ++ f) scripts { commands, logs := 100000 } with
    | .error e =>
      bad := bad + 1
      IO.println (Json.mkObj [("file", .str f), ("error", .str e)]).compress
    | .ok s =>
      let b ← IO.monoNanosNow
      let (s, quiet) := s.settle settleMs
      let c ← IO.monoNanosNow
      IO.println (Json.mkObj [("file", .str f), ("quiet", .bool quiet), ("clock", jn s.loop.clock),
        ("logs", .arr (s.logs.map .str)), ("errors", .arr (s.errors.map .str)),
        ("commands", jn s.commands.size), ("tasks", jn s.tasks), ("jobs", jn s.jobs),
        ("instructions", jn s.steps), ("startMs", jn ((b - a) / 1000000)), ("settleMs", jn ((c - b) / 1000000)),
        ("body", .str ((bodyText s.host.dom.dom).take 400).toString)]).compress
  return if bad == 0 then 0 else 1

end L4Factoidal.WasmVM.Bench.Page
