import WebState

/-! `web-state`: the ops of `WebState` over standard input and output, one JSON request
per line (`{"op": NAME, ...}`), one JSON answer per line. The Deno test of the browser
state uses it (`browser_state_test.ts`), and so does a native host whose engine was built
before `WebState` (`native_state.ts`). The engine answers the same ops through
`web_document_call` (`WebDocument.lean`). -/
open L4Factoidal

def answer (line : String) : String :=
  let failed := fun (e : String) => (JSON.Json.object [("error", .string e)]).toString
  match WebState.parse line with
  | none => failed "the request is not JSON"
  | some request =>
    match request.field? "op" with
    | some (.string name) =>
      match WebState.op name request with
      | .ok (some a) => a
      | .ok none => failed s!"unknown op {name}"
      | .error e => failed e
    | _ => failed "the request has no op"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    stdout.putStrLn (answer line.trimAscii.toString)
    stdout.flush
