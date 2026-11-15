import L4Factoidal.WasmVM.Hosts.LeanJS
import L4Factoidal.JS.Test262

/-!
# `lake exe bubblepop-test262` — Test262 on the realm the browser runs page scripts in

`bubblepop-test262 test262-files ROOT LIST`: as `leanjs test262-files` (`JS/Test262.lean`), on
the page realm of `LeanJS.prepareSource`: BubblePopJS with the page objects of
`tools/wasmvm/quickjs/prelude.js` (Temporal, Intl, the window's globals) on an empty
document, the realm each page of Foafnaut starts from. The full Test262 run of
danbri/factoidal-builds (`test262.yml`) uses it. Test262's `print` is the runner's (the
window's `print` prints nothing), read back as `$262.out`.
-/

namespace L4Factoidal.WasmVM.Hosts.Test262Page
open L4Factoidal.WasmVM.Hosts

def main (args : List String) : IO UInt32 := do
  match args with
  | ["test262-files", root, list] =>
    match LeanJS.prepareSource with
    | .error e => IO.eprintln s!"the page realm failed: {e}"; pure 1
    | .ok s =>
      JS.Test262.test262Files root list { s.heap with jobs := #[], jobHead := 0 } (page := true)
      pure 0
  | _ =>
    IO.eprintln "usage: bubblepop-test262 test262-files ROOT LIST"
    pure 64

end L4Factoidal.WasmVM.Hosts.Test262Page

def main (args : List String) : IO UInt32 := L4Factoidal.WasmVM.Hosts.Test262Page.main args
