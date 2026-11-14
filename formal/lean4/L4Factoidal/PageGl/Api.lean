/-
L4Factoidal.PageGl.Api: the WebGL operations of the `web_api` import (ops 100 to 119; record:
docs/designissues/2026-11-14-webgl-webcodecs.md, section 3).

  * 100 `interface(version)`: the rendering context interface of WebGL `1` or `2` as text
    (`Idl.Interface.text`), from which the page glue builds the interface object.

The arguments are the fields of the import's argument block (`WebApi.fields`): strings in UTF-8,
numbers as decimal text. Answers are bytes; a negative number is an error of the import
(-2: not an op of this engine, -20: TypeError).
-/
import L4Factoidal.PageGl.Idl

namespace L4Factoidal.PageGl.Api

/-- Field `i` as text ("" when it is missing or is not UTF-8). -/
def strArg (fs : Array ByteArray) (i : Nat) : String :=
  match fs[i]? with
  | some b => (String.fromUTF8? b).getD ""
  | none => ""

/-- What the session keeps for WebGL between calls. -/
structure State where
  /-- Calls served (a counter for the frame-cost tests; no decision reads it). -/
  calls : Nat := 0
  deriving Inhabited

def op (s : State) (code : Nat) (fs : Array ByteArray) : State × Except Int ByteArray :=
  match code with
  | 100 =>
    match strArg fs 0 with
    | "1" => (s, .ok Idl.webgl1.text.toUTF8)
    | "2" => (s, .ok Idl.webgl2.text.toUTF8)
    | _ => (s, .error (-20))
  | _ => (s, .error (-2))

private def run (code : Nat) (xs : List String) : String :=
  match (op {} code (xs.map (·.toUTF8)).toArray).2 with
  | .ok b => (String.fromUTF8? b).getD "?"
  | .error e => s!"error {e}"

#guard (run 100 ["1"]).startsWith "c DEPTH_BUFFER_BIT 256\nc STENCIL_BUFFER_BIT 1024\n"
#guard ((run 100 ["2"]).splitOn "\n").contains "o getBufferSubData 3"
#guard ((run 100 ["2"]).splitOn "\n").contains "a canvas 1"
#guard ((run 100 ["2"]).splitOn "\n").contains "c TIMEOUT_IGNORED -1"
#guard run 100 ["3"] == "error -20"
#guard run 119 [] == "error -2"

end L4Factoidal.PageGl.Api
