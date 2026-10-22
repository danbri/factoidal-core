/-
Exercise the actual AtomicDirect reader and certified decision on original
RDF/XML ontologies extracted from the W3C OWL catalog. This is IO plumbing,
not a semantic implementation. The Python driver retains test provenance,
accounts for every selected case, and distinguishes unknown from a verdict.
-/
import L4Factoidal.OWL.AtomicDirect
import L4Factoidal.Syntax.RdfXml
import Lean

open L4Factoidal.OWL

def runCorpusRow (row : Lean.Json) : Except String Lean.Json := do
  let caseId ← (← row.getObjVal? "id").getStr?
  let input ← (← row.getObjVal? "input").getStr?
  let base ← (← row.getObjVal? "base").getStr?
  let common := [("id", Lean.toJson caseId)]
  match L4Factoidal.Syntax.RdfXml.parseRdfXml input (some base) with
  | .error error =>
      return Lean.Json.mkObj (common ++ [
        ("status", Lean.toJson "parse-error"),
        ("error", Lean.toJson error.msg)])
  | .ok graph =>
      let verdict := AtomicDirect.decide graph .close
      return Lean.Json.mkObj (common ++ [
        ("status", Lean.toJson (if (AtomicDirect.readOntology graph).isSome
          then "supported" else "unsupported")),
        ("tripleCount", Lean.toJson graph.length),
        ("consistent", Lean.toJson verdict.consistent)])

def main (args : List String) : IO UInt32 := do
  let [inputPath] := args | do
    IO.eprintln "usage: AtomicDirectCorpus.lean INPUT.jsonl"
    return 2
  let content ← IO.FS.readFile inputPath
  let mut count := 0
  for line in content.splitOn "\n" do
    if !line.isEmpty then
      match Lean.Json.parse line >>= runCorpusRow with
      | .error error =>
          IO.eprintln s!"case input error: {error}"
          return 2
      | .ok result =>
          IO.println ("ATOMIC_DIRECT_CASE=" ++ result.compress)
          count := count + 1
  if count == 0 then
    IO.eprintln "empty corpus input"
    return 2
  return 0
