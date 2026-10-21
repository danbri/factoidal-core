/-
Wasm.ErrorModelTests — build-time checks that bind each error producer of the
dispatch table to its code (`Wasm/Ops/ErrorModel.lean`,
https://github.com/danbri/factoidal/issues/882 item 4).

Every check runs the real entry (`L4Wasm.call`) on an input that triggers the
condition, so a change of a message text that moves a refusal to another code
fails the build. Positive and negative cases: a correct input answers no code.
-/
import Wasm.Dispatch

namespace L4Wasm.ErrorModelTests

open L4Wasm.Ops
open L4Factoidal.JSON

private def args (xs : List String) : String := (Json.array (xs.map Json.string)).toString

private def codeOfCall (op : String) (xs : List String) : Option String :=
  codeOf? (L4Wasm.call op (args xs))

private def fieldOfCall (op : String) (xs : List String) (k : String) : Option Json :=
  (parseJson? (L4Wasm.call op (args xs))).bind (·.field? k)

private def nt : String := "<http://e/a> <http://e/p> \"x\" .\n"
private def tt : String :=
  "<http://e/a> <http://e/p> <<( <http://e/a> <http://e/p> <http://e/o> )>> .\n"

-- parse.syntax, with a position and the Turtle grammar section
#guard codeOfCall "parseToDatasetJson" ["<http://e/a> <http://e/p> .", "turtle", ""]
  == some "parse.syntax"
#guard fieldOfCall "parseToDatasetJson" ["<http://e/a> <http://e/p> .", "turtle", ""] "spec"
  == some (.string "https://www.w3.org/TR/rdf12-turtle/#sec-grammar")
#guard (match fieldOfCall "parseToDatasetJson" ["<http://e/a>\n <http://e/p> .", "turtle", ""] "position" with
  | some p => p.field? "line" == some (.number "2") | none => false)
#guard codeOfCall "parseToDatasetJson" [nt, "turtle", ""] == none
-- RDF/XML has no position and is still parse.syntax, with the RDF/XML grammar
#guard codeOfCall "parseToDatasetJson" ["<rdf:RDF", "rdfxml", ""] == some "parse.syntax"
-- parse.rdf12-required
#guard codeOfCall "parseToDatasetJson" [tt, "turtle", ""] == some "parse.rdf12-required"
#guard codeOfCall "parseToDatasetJson" [tt, "turtle12", ""] == none
-- term.invalid-iri and term.invalid-langtag from the parsers
#guard codeOfCall "parseToDatasetJson" ["<a b> <http://e/p> \"x\" .", "ntriples", ""]
  == some "term.invalid-iri"
#guard codeOfCall "parseToDatasetJson" ["<http://e/a> <http://e/p> \"x\"@1-- .", "ntriples", ""]
  == some "term.invalid-langtag"
-- format.unknown
#guard codeOfCall "parseToDatasetJson" ["x", "bogus", ""] == some "format.unknown"
-- query.syntax, with a position into the query text
#guard codeOfCall "queryDataset" [nt, "SELEC * WHERE {}"] == some "query.syntax"
#guard (match fieldOfCall "queryDataset" [nt, "SELECT *\nWHERE { ?s }"] "position" with
  | some p => p.field? "line" == some (.number "2") | none => false)
#guard codeOfCall "queryDataset" [nt, "SELECT * WHERE { ?s ?p ?o }"] == none
-- update.syntax
#guard codeOfCall "updateDataset" [nt, "INSERT DATA { "] == some "update.syntax"
#guard codeOfCall "updateDataset" [nt, "INSERT DATA { <http://e/a> <http://e/p> 1 }"] == none
-- canon.unsupported-rdf12
#guard codeOfCall "canonicalizeToNQuads" [tt] == some "canon.unsupported-rdf12"
#guard codeOfCall "canonicalizeToNQuads" [nt] == none
-- owl.unsupported-rdf12
#guard codeOfCall "owlIsConsistent" [tt, ""] == some "owl.unsupported-rdf12"
#guard codeOfCall "owlIsConsistent" [nt, ""] == none
-- call.arity, call.arguments, op.unknown
#guard codeOfCall "queryDataset" [] == some "call.arity"
#guard codeOf? (L4Wasm.call "queryDataset" "{}") == some "call.arguments"
#guard codeOfCall "noSuchOp" [] == some "op.unknown"
-- every error answer of the table carries a declared code
#guard ((L4Wasm.call "xpathEval" (args ["<a/>", "///"])) |> codeOf?).all errorCodes.contains

end L4Wasm.ErrorModelTests
