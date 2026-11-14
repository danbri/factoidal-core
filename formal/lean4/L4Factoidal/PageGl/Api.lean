/-
L4Factoidal.PageGl.Api: the WebGL operations of the `web_api` import (ops 100 to 119; record:
docs/designissues/2026-11-14-webgl-webcodecs.md, section 3).

  * 100 `interface(version)`: the rendering context interface of WebGL `1` or `2` as text
    (`Idl.Interface.text`), from which the page glue builds the interface object, and a line
    `m NAME` for each command the state machine models (`State.modelled`).
  * 101 `context(version, alpha, depth, stencil)`: a new context; answers its number.
  * 102 `call(context, command, arguments...)`: one command through `State.step`; `getError`
    answers the error flag and clears it; `$raise` records an error the drawing path found.
    An argument is a field whose first character says what it is: `i` an integer, `f` a number
    kept as text, `s` a string, `o` an object's number (`o0` null, `o-` not an object of this
    context), `b` a buffer source (`b<bytes> <bytes of an element>`), `l` a list of integers,
    `u` nothing. The answer: `u` undefined, `d` the drawing path answers, `z` null, `i` an integer,
    `t` or `F` a boolean, `o` an object, `!` the command generated an error.

The arguments are the fields of the import's argument block (`WebApi.fields`): strings in UTF-8,
numbers as decimal text. Answers are bytes; a negative number is an error of the import
(-2: not an op of this engine, -20: TypeError).
-/
import L4Factoidal.PageGl.Idl
import L4Factoidal.PageGl.State

namespace L4Factoidal.PageGl.Api

/-- Field `i` as text ("" when it is missing or is not UTF-8). -/
def strArg (fs : Array ByteArray) (i : Nat) : String :=
  match fs[i]? with
  | some b => (String.fromUTF8? b).getD ""
  | none => ""

/-- Contexts of one session. -/
def maxContexts : Nat := 1024

/-- What the session keeps for WebGL between calls: its contexts, by number. -/
structure State where
  contexts : Std.HashMap Nat Ctx := {}
  next : Nat := 1
  deriving Inhabited

def argOf (b : ByteArray) : Arg :=
  let s := (String.fromUTF8? b).getD ""
  let rest := String.ofList (s.toList.drop 1)
  match s.toList.head? with
  | some 'i' => .int (rest.toInt?.getD 0)
  | some 'f' => .num rest
  | some 's' => .str rest
  | some 'o' => (match rest.toNat? with | some id => .obj id | none => .foreign)
  | some 'b' => (match (rest.splitOn " ").map (·.toNat?) with
    | [some size, some elem] => .bytes size elem
    | _ => .none)
  | some 'l' => .list ((rest.splitOn ",").filterMap (·.toInt?))
  | _ => .none

def replyText : Reply → String
  | .unit => "u" | .defer => "d" | .null => "z" | .int i => s!"i{i}"
  | .bool b => if b then "t" else "F" | .obj id => s!"o{id}" | .fail => "!"

/-- Is `p` the value of a constant of the context's interface? -/
def isConstant (version : Nat) (p : Nat) : Bool := (Idl.ofVersion version).consts.any (·.2 == (p : Int))

def interfaceText (i : Idl.Interface) : String :=
  i.text ++ "\n" ++ "\n".intercalate (modelled.map ("m " ++ ·))

def call (s : State) (fs : Array ByteArray) : State × Except Int ByteArray :=
  match (strArg fs 0).toNat? with
  | none => (s, .error (-20))
  | some id =>
    match s.contexts[id]? with
    | none => (s, .error (-20))
    | some c =>
      let op := strArg fs 1
      let args := (fs.extract 2 fs.size).map argOf
      if op == "getError" then
        let (c, e) := getError c
        ({ s with contexts := s.contexts.insert id c }, .ok s!"i{e}".toUTF8)
      else if op == "$raise" then
        match GlError.ofCode? (natAt args 0) with
        | some e => ({ s with contexts := s.contexts.insert id (raise c e) }, .ok "u".toUTF8)
        | none => (s, .ok "u".toUTF8)
      else
        let (c, r) := step c (isConstant c.st.version) op args
        ({ s with contexts := s.contexts.insert id c }, .ok (replyText r).toUTF8)

def op (s : State) (code : Nat) (fs : Array ByteArray) : State × Except Int ByteArray :=
  match code with
  | 100 =>
    match strArg fs 0 with
    | "1" => (s, .ok (interfaceText Idl.webgl1).toUTF8)
    | "2" => (s, .ok (interfaceText Idl.webgl2).toUTF8)
    | _ => (s, .error (-20))
  | 101 =>
    if s.contexts.size ≥ maxContexts then (s, .error (-5)) else
    let version := if strArg fs 0 == "2" then 2 else 1
    let c : Ctx := { st := { version, alpha := strArg fs 1 == "1", depth := strArg fs 2 == "1", stencil := strArg fs 3 == "1" } }
    ({ contexts := s.contexts.insert s.next c, next := s.next + 1 }, .ok s!"{s.next}".toUTF8)
  | 102 => call s fs
  | _ => (s, .error (-2))

private def runs (calls : List (Nat × List String)) : List String :=
  (calls.foldl (fun (s, out) (code, xs) =>
    let (s, r) := op s code (xs.map (·.toUTF8)).toArray
    (s, out ++ [match r with | .ok b => (String.fromUTF8? b).getD "?" | .error e => s!"error {e}"])) (({} : State), ([] : List String))).2
private def run (code : Nat) (xs : List String) : String := (runs [(code, xs)]).headD ""

#guard (run 100 ["1"]).startsWith "c DEPTH_BUFFER_BIT 256\nc STENCIL_BUFFER_BIT 1024\n"
#guard ((run 100 ["2"]).splitOn "\n").contains "o getBufferSubData 3 u,l,V,~l,~u"
#guard ((run 100 ["2"]).splitOn "\n").contains "a canvas 1"
#guard ((run 100 ["2"]).splitOn "\n").contains "c TIMEOUT_IGNORED -1"
#guard run 100 ["3"] == "error -20"
#guard run 119 [] == "error -2"
#guard ((run 100 ["1"]).splitOn "\n").contains "m getParameter"
-- A context, a texture bound and read back; a WebGL 2 parameter on WebGL 1 is INVALID_ENUM, once.
#guard runs [(101, ["1", "1", "1", "0"]), (102, ["1", "createTexture"]), (102, ["1", "bindTexture", "i3553", "o1"]),
    (102, ["1", "getParameter", "i32873"]), (102, ["1", "getParameter", "i35869"]), (102, ["1", "getError"]), (102, ["1", "getError"]),
    (102, ["1", "getParameter", "i7938"]), (102, ["1", "drawArrays", "i4", "i0", "i3"]), (102, ["1", "$raise", "i1282"]), (102, ["1", "getError"]),
    (102, ["1", "bindTexture", "i3553", "o-"]), (102, ["1", "getError"]), (102, ["7", "getError"])] ==
  ["1", "o1", "u", "o1", "!", "i1280", "i0", "d", "d", "u", "i1282", "!", "i1282", "error -20"]
#guard runs [(101, ["2", "0", "0", "0"]), (102, ["1", "getParameter", "i3413"]), (102, ["1", "getParameter", "i2968"]),
    (102, ["1", "vertexAttrib1fv", "i0", "l1"]), (102, ["1", "vertexAttrib4fv", "i0", "b12 4"]), (102, ["1", "getError"])] ==
  ["1", "i0", "i4294967295", "u", "!", "i1281"]

end L4Factoidal.PageGl.Api
