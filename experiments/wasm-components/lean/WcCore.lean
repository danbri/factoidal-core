/-
WcCore: the Factoidal subset that the wasm component experiments build
(https://github.com/danbri/factoidal/issues/1167, milestone 1).

Two entry points, both over existing library code (no second
implementation): the Turtle reader (`L4Factoidal.Syntax.parseTurtle`,
RDF 1.1 Turtle) and the query op of the shipped wasm
(`L4Wasm.Ops.queryParsedDataset`, SPARQL 1.1 Query). The answers are the
JSON envelopes the shipped `queryDataset` op gives, so the outputs of the
Emscripten build and of the component builds can be compared byte for byte.
This module is an experiment; it is not part of any build root.
-/
import L4Factoidal.Syntax.Turtle
import Wasm.Ops.Query

namespace WcCore
open L4Factoidal.RDF L4Factoidal.Syntax L4Wasm.Ops

/-- RDF 1.1 Turtle text to canonical N-Quads (default graph only). -/
def turtleToNQuads (ttl base : String) : Except String String :=
  match parseTurtle ttl (if base.isEmpty then none else some base) with
  | .error e => .error s!"Turtle parse error: {fmtParseError e}"
  | .ok g    => .ok (Dataset.toCanonicalNQuads { default := g, named := [] })

/-- Parse Turtle, run one SPARQL 1.1 query; the `queryDataset` envelope. -/
def queryTurtle (ttl sparql : String) : String :=
  match parseTurtle ttl none with
  | .error e => errJson s!"Turtle parse error: {fmtParseError e}"
  | .ok g    => queryParsedDataset { default := g, named := [] } sparql

/-- The C ABI. A result string that starts with `!` is an error message. -/
@[export wc_turtle_to_nquads]
def turtleToNQuadsC (ttl base : String) : String :=
  match turtleToNQuads ttl base with
  | .ok s    => s
  | .error e => "!" ++ e

@[export wc_query_turtle]
def queryTurtleC (ttl sparql : String) : String := queryTurtle ttl sparql

#guard turtleToNQuads "<http://e/a> <http://e/p> \"v\" ." "" ==
  .ok "<http://e/a> <http://e/p> \"v\" .\n"

end WcCore
