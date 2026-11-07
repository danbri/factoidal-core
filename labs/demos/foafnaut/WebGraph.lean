import FoafNaut
import WebShell

/-! The interactive FOAF graph as a browser page. The model is a Lean value that the
host keeps as text; each input goes through the app's own transition, and each frame
is the app's own checked SVG inside a small HTML page. -/
namespace WebGraph
open L4Factoidal
open NativeFoafNaut

private def str (j : JSON.Json) (key : String) : String :=
  match j.field? key with | some (.string value) => value | _ => ""
private def int (j : JSON.Json) (key : String) : Int :=
  match j.field? key with | some (.number value) => value.toInt?.getD 0 | _ => 0

/-- The picture of a model as a page, with no margin so app pixels are page pixels. -/
def page (wire : String) : Except String String := do
  let some m := Model.decode wire | throw "invalid FOAF graph model"
  -- `keepApart` holds the layout policy on each step, so a frame draws what it is given.
  let svg ← NativeSceneSVG.serialize m.scene
  return "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>FOAF graph</title>" ++
    "<style>body{margin:0;background:white}svg{display:block}</style></head><body>" ++ svg ++ "</body></html>"

/-- A node may not cover another. The app's layout policy decides what covers: a step
that breaks it keeps the last legal positions, so a dragged node stops at its neighbour.
A layout that already breaks the policy, as after a reveal, may still move. -/
def keepApart (before after : Model) : Model :=
  let legal := fun (m : Model) => L4Factoidal.UI.LayoutPolicy.certify m.policy m.footprints
  if legal after || !legal before then after else {after with positions := before.positions}

private def chrome (request : JSON.Json) : Int :=
  let shell := WebShell.Shell.ofJson ((request.field? "shell").getD .null)
  Int.ofNat (WebShell.height shell (int request "width").toNat)

/-- Sizes and pointer positions arrive in window coordinates; the app starts below
the chrome. Kind 1 is a resize, 2 to 4 are pointer events. -/
private def appY (request : JSON.Json) (kind : Nat) (b : Int) : Int :=
  if kind >= 1 && kind <= 4 then b - chrome request else b

/-- `graphStart`, `graphEvent` and `graphPage`. A frame says what the host must do. -/
def op (name : String) (request : JSON.Json) : Except String (Option String) := do
  if name == "graphStart" then
    let width := (int request "width").toNat
    let height := (int request "height" - chrome request).toNat
    return some (initialResponse (str request "rdf") width.toUInt32 height.toUInt32)
  if name == "graphEvent" then
    let kind := (int request "kind").toNat
    let some m := Model.decode (str request "model") | throw "invalid FOAF graph model"
    let result := transitionModel m kind (int request "a") (appY request kind (int request "b"))
    let model := keepApart m result.model
    return some (response model result.commands false result.clipboardWrite result.clipboardRead)
  if name == "graphPage" then
    return some (JSON.Json.object [("source",.string (← page (str request "model")))]).toString
  return none

end WebGraph
