import Lean
import L4Factoidal.Wikidata.Source

/-! Compare token sequences without deleting content inside strings or IRIs.
Input may have passed through the same Jena parser and serializer beforehand.
This is a syntactic diagnostic. It makes no claim about SPARQL equivalence. -/
open Lean L4Factoidal.SPARQL L4Factoidal.Wikidata

private def normalTokens (original : List String) (text : String) :
    List Token × List Token := Id.run do
  let tokens := (tokenizeAt .v11 text).map (·.tok)
  let mut names : Std.HashMap String String := {}
  let mut alpha := #[]
  for token in tokens do
    if let .var v := token then
      if !(original.contains v) then
        let normalized := names[v]?.getD (":" ++ toString names.size)
        names := names.insert v normalized
        alpha := alpha.push (Token.var normalized)
      else alpha := alpha.push token
    else alpha := alpha.push token
  return (tokens, alpha.toList)

private def inspect (j : Json) : Except String Json := do
  let id ← (← j.getObjVal? "id").getStr?
  let source ← (← j.getObjVal? "source").getStr?
  let left ← (← j.getObjVal? "left").getStr?
  let right ← (← j.getObjVal? "right").getStr?
  let names := (tokenizeAt .v11 source).filterMap fun t =>
    match t.tok with | .var v => some v | _ => none
  let (leftTokens, leftAlpha) := normalTokens names left
  let (rightTokens, rightAlpha) := normalTokens names right
  return Json.mkObj [("id", toJson id), ("tokens_equal", toJson (leftTokens == rightTokens)),
    ("alpha_equal", toJson (leftAlpha == rightAlpha))]

def main (args : List String) : IO UInt32 := do
  let [path] := args | IO.eprintln "usage: NormalizeBatch INPUT.json"; return 1
  let text ← IO.FS.readFile path
  let .ok doc := Json.parse text | IO.eprintln "invalid JSON"; return 1
  let .ok items := doc.getArr? | IO.eprintln "expected JSON array"; return 1
  let stdout ← IO.getStdout
  for item in items do
    match inspect item with
    | .error e => IO.eprintln s!"invalid record: {e}"; return 1
    | .ok result => stdout.putStrLn result.compress
  return 0
