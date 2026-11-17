import L4Factoidal.Presenter.Spec
import L4Factoidal.JSON.Parser
import L4Factoidal.JSON.Serialize

/-! Pure JSON boundary for the presenter. The caller owns the state; no document, font,
script session or mutable engine state is read. Wire integers fit signed 32-bit values on
both native and Wasm. The text boundary refuses requests above 4096 bytes before parsing. -/
namespace L4Factoidal.Presenter.Wire
open JSON

def maxNumber : Nat := 2147483647

def number (n : Nat) : Json := .number (toString n)

private def field (j : Json) (key : String) : Except String Json :=
  match j.field? key with
  | some value => .ok value
  | none => .error ("presenter: missing " ++ key)

private def natural (j : Json) : Except String Nat := do
  let .number text := j | throw "presenter: expected natural number"
  let some n := text.toNat? | throw "presenter: expected natural number"
  if n > maxNumber then throw "presenter: number exceeds signed 32-bit range"
  return n

private def natField (j : Json) (key : String) : Except String Nat := do
  natural (← field j key)

private def optional (read : Json → Except String α) : Json → Except String (Option α)
  | .null => .ok none
  | j => some <$> read j

def frameOf (j : Json) : Except String LayerFrame := do
  return ⟨← natField j "id", ← natField j "bandTop", ← natField j "bandHeight",
    ← natField j "keepFrom", ← natField j "keepTo"⟩

def stateOf (j : Json) : Except String State := do
  return ⟨← natField j "view", ← natField j "scroll",
    ← optional frameOf ((j.field? "shown").getD .null),
    ← optional natural ((j.field? "asked").getD .null)⟩

def inputOf (j : Json) : Except String Input := do
  match j.getString? "kind" with
  | some "scrollTo" => return .scrollTo (← natField j "y")
  | some "resize" => return .resize (← natField j "h")
  | some "frame" => return .frame (← frameOf (← field j "frame"))
  | some "vsync" => return .vsync
  | _ => throw "presenter: unknown input kind"

def frameJson (f : LayerFrame) : Json := .object [
  ("id",number f.id), ("bandTop",number f.bandTop), ("bandHeight",number f.bandHeight),
  ("keepFrom",number f.keepFrom), ("keepTo",number f.keepTo)]

def stateJson (s : State) : Json := .object [
  ("view",number s.view), ("scroll",number s.scroll),
  ("shown",s.shown.map frameJson |>.getD .null), ("asked",s.asked.map number |>.getD .null)]

def outputJson : Output → Json
  | .present id offset => .object [("kind",.string "present"),("frameId",number id),("offset",number offset)]
  | .needBand scroll => .object [("kind",.string "needBand"),("scroll",number scroll)]

/-- The view's requested top row is within the rows of the shown band. This also rejects
scrolls before the band's top, where natural subtraction alone would return zero. -/
def isExact (f : LayerFrame) (view scroll : Nat) : Bool :=
  decide (f.bandTop ≤ scroll) && decide (scroll - f.bandTop ≤ f.bandHeight - view)

/-- Kind: equivalence. Says: an exact placement's offset selects the requested page row.
Does not say: that the band has enough content below the viewport or that a GPU obeys it. -/
theorem exact_offset (f : LayerFrame) (view scroll : Nat) (h : isExact f view scroll = true) :
    f.bandTop + offsetOf f view scroll = scroll := by
  simp only [isExact, Bool.and_eq_true, decide_eq_true_eq] at h
  unfold offsetOf
  rw [Nat.min_eq_right h.2]
  omega

def placement (s : State) : Json := match s.shown with
  | none => .null
  | some f => .object [("frameId",number f.id),("offset",number (offsetOf f s.view s.scroll)),
      ("exact",.bool (isExact f s.view s.scroll)), ("kept",.bool (keeps f s.scroll))]

def response (s : State) (i : Input) : Json :=
  let (next, outputs) := step s i
  .object [("state",stateJson next),("outputs",.array (outputs.map outputJson)),("placement",placement next)]

def answer (request : Json) : Except String Json := do
  let s ← stateOf (← field request "state")
  let i ← inputOf (← field request "input")
  return response s i

/-- Pure C boundary; called independently of the mutable document engine. -/
@[export web_presenter_step]
def compile (request : String) : String :=
  let result : Except String Json := do
    if request.utf8ByteSize > 4096 then throw "presenter: request exceeds 4096 bytes"
    let (j, pos) ← (JSON.parseJsonText request).mapError (fun _ => "presenter: invalid JSON")
    if !(request.drop pos).all Char.isWhitespace then throw "presenter: trailing request data"
    answer j
  match result with
  | .ok value => value.toString
  | .error message => (Json.object [("error",.string message)]).toString

#guard isExact ⟨1,100,300,100,300⟩ 100 50 == false
#guard isExact ⟨1,100,300,100,300⟩ 100 300 == true
#guard isExact ⟨1,100,300,100,300⟩ 100 301 == false
#guard (natural (.number "-1")).isError
#guard (natural (.number "2147483648")).isError
#guard (inputOf (.object [("kind",.string "unknown")])).isError

#print axioms exact_offset

end L4Factoidal.Presenter.Wire
