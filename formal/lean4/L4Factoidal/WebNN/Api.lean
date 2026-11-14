/-
L4Factoidal.WebNN.Api: the Web Neural Network API as one bytes-in, bytes-out call, for the
page host (`WasmVM/Hosts/WebApi.lean`, web_api op 140) and any other embedder. The arguments
are fields: the first names the command, the rest are its arguments as text (numbers in
decimal, doubles as the 16 hexadecimal digits of their bits, tensor data as raw bytes).

The answer is text. A refusal starts with `!`: `!T` and a message is a `TypeError`; `!D`, a
DOMException name, `:` and a message is that DOMException. No other answer starts with `!`.
`read` answers bytes: a 0 byte and the tensor's data, or a 1 byte and a refusal text.

A page that never touches `navigator.ml` never makes this call, and `State` is then the empty
record it starts as.
-/
import L4Factoidal.WebNN.Graph

namespace L4Factoidal.WebNN

private def str (fs : Array ByteArray) (i : Nat) : String :=
  match fs[i]? with
  | some b => (String.fromUTF8? b).getD ""
  | none => ""

private def nat (fs : Array ByteArray) (i : Nat) : Nat := ((str fs i).toNat?).getD maxObjects

private def refusal : Err → String
  | .type m => "!T" ++ m
  | .dom n m => "!D" ++ n ++ ":" ++ m

/-- Name and value pairs from field `i` on. -/
private def pairs (fs : Array ByteArray) (i : Nat) : List (String × String) :=
  (List.range ((fs.size - i) / 2)).map fun k => (str fs (i + 2 * k), str fs (i + 2 * k + 1))

private def text (r : M (State × String)) (s : State) : State × ByteArray :=
  match r with
  | .ok (s, t) => (s, t.toUTF8)
  | .error e => (s, (refusal e).toUTF8)

private def unit (r : M State) (s : State) : State × ByteArray :=
  match r with
  | .ok s => (s, ByteArray.empty)
  | .error e => (s, (refusal e).toUTF8)

/-- One call of the API. -/
def api (s : State) (fs : Array ByteArray) : State × ByteArray :=
  match str fs 0 with
  | "table" => (s, tableText.toUTF8)
  | "limits" => (s, supportLimitsJson.toUTF8)
  | "context" => text ((createContext s).map fun (s, i) => (s, toString i)) s
  | "destroyContext" => (destroyContext s (nat fs 1), ByteArray.empty)
  | "lost" => (s, (if ctxLost s (nat fs 1) then "1" else "0").toUTF8)
  | "builder" => text ((newBuilder s (nat fs 1)).map fun (s, i) => (s, toString i)) s
  | "input" => text (addInput s (nat fs 1) (str fs 2) (str fs 3) (str fs 4)) s
  | "constant" => text (addConstant s (nat fs 1) (str fs 2) (str fs 3) (fs[4]?.getD ByteArray.empty)) s
  | "scalar" => text (addScalar s (nat fs 1) (str fs 2) (str fs 3)) s
  | "constantTensor" => text (addConstTensor s (nat fs 1) (nat fs 2)) s
  | "op" => text (call s (nat fs 1) (str fs 2) (str fs 3) (pairs fs 4)) s
  | "build" =>
    let bid := nat fs 1
    text ((build s bid (pairs fs 2)).map fun s => (s, graphText s bid)) s
  | "destroyGraph" => (destroyGraph s (nat fs 1), ByteArray.empty)
  | "tensor" =>
    let flags := str fs 4
    let flag (c : Char) := flags.toList.contains c
    text ((createTensor s (nat fs 1) (str fs 2) (str fs 3) (flag 'r') (flag 'w') (flag 'c') fs[5]?).map
      fun (s, i) => (s, toString i)) s
  | "write" => unit (writeTensor s (nat fs 1) (nat fs 2) (fs[3]?.getD ByteArray.empty)) s
  | "read" =>
    match readTensor s (nat fs 1) (nat fs 2) with
    | .ok b => (s, (ByteArray.mk #[0]) ++ b)
    | .error e => (s, (ByteArray.mk #[1]) ++ (refusal e).toUTF8)
  | "destroyTensor" => (destroyTensor s (nat fs 1), ByteArray.empty)
  | "dispatch" =>
    let nIn := nat fs 3
    let named (start count : Nat) : List (String × Nat) :=
      (List.range count).map fun k => (str fs (start + 2 * k), nat fs (start + 2 * k + 1))
    let nOut := (fs.size - 4 - 2 * nIn) / 2
    if 4 + 2 * nIn > fs.size then (s, "!Tthe tensors could not be read".toUTF8)
    else unit (dispatch s (nat fs 1) (nat fs 2) (named 4 nIn) (named (4 + 2 * nIn) nOut)) s
  | c => (s, ("!T" ++ c ++ " is not a command").toUTF8)

end L4Factoidal.WebNN
