/- Parse JSON query records with the production Lean WDQS-prefix parser.
Input is an array of objects with `id` and `query` string fields. Emits JSONL;
it never evaluates queries or contacts endpoints. -/
import Lean
import L4Factoidal.Wikidata.Rewrite
open Lean
private def inspect (mode : Option String) (j : Json) : Except String Json := do
  let id ← (← j.getObjVal? "id").getStr?
  let query ← (← j.getObjVal? "query").getStr?
  if let some language := mode then
    return Json.mkObj [("id", toJson id),
      ("result", toJson (L4Factoidal.Wikidata.rewriteQuery query language))]
  let (accepted, message) := match L4Factoidal.Wikidata.parseQuery query none .v11 with
    | .ok _ => (true, "")
    | .error e => (false, e.msg)
  return Json.mkObj [("id", toJson id), ("accepted", toJson accepted), ("message", toJson message)]
def main (args : List String) : IO UInt32 := do
  let some (path, mode) := (match args with
    | [path] => some (path, none)
    | [path, "--rewrite"] => some (path, some "")
    | [path, "--rewrite", language] => some (path, some language)
    | _ => none) |
    IO.eprintln "usage: ParseBatch INPUT.json [--rewrite [LANGUAGE]]"
    return 1
  let text ← IO.FS.readFile path
  let .ok doc := Json.parse text | IO.eprintln "invalid JSON"; return 1
  let .ok items := doc.getArr? | IO.eprintln "expected JSON array"; return 1
  let stdout ← IO.getStdout
  for item in items do
    match inspect mode item with
    | .error e => IO.eprintln s!"invalid record: {e}"; return 1
    | .ok result => stdout.putStrLn result.compress
  return 0
