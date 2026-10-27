/-
L4Factoidal.SHACL.Rules — the `.srl` entry points the rules runner
(`Harness/ShaclRulesRun.lean`, `lake exe l4shacl-rules`) calls.

Until 2026-10-27 this module was a port of `formal/fstar/SHACL.Rules.fst`:
string scanners that translated each `RULE` to a SPARQL CONSTRUCT, ran a
naive fixpoint, read `NOT` as `FILTER NOT EXISTS`, and approximated
stratification. It is now four names over `L4Factoidal.SPARQLRL`, the
implementation of the SPARQL 1.2 RL editor's draft (abstract syntax, parser
from the draft's EBNF, well-formedness, dependency graph, stratification,
semi-naive evaluation):
https://github.com/danbri/factoidal/issues/1099 (SPARQL-RL for 0.20.0).
The F\* module `SHACL.Rules.fst` stays as the record of the earlier form.

| Name | Meaning |
|---|---|
| `srlValidSyntax` | the text parses (`SPARQLRL.validSyntax`) |
| `srlWellFormed` | it parses and every rule is well-formed |
| `srlStratifiable` | it parses, is well-formed, and meets the stratification condition |
| `runRules` | the inference graph (`SPARQLRL.inferText`); empty on any error |
-/
import L4Factoidal.SPARQLRL.Text

namespace L4Factoidal.SHACL

open L4Factoidal.RDF

def srlValidSyntax (srl : String) : Bool := SPARQLRL.validSyntax srl

def srlWellFormed (srl : String) : Bool := SPARQLRL.wellFormedText srl

def srlStratifiable (srl : String) : Bool := SPARQLRL.stratifiableText srl

/-- The triples inferred from `data` by the rules in `srl` (the inference
graph: data-block triples and derived triples not in `data`). An empty graph
when the rule set has a syntax error, is not well-formed, is not
stratifiable, or has `IMPORTS` (no loader here). Use
`SPARQLRL.inferText` to see the error. -/
def runRules (data : Graph) (srl : String) : Graph :=
  match SPARQLRL.inferText srl data with
  | .ok g => g
  | .error _ => []

end L4Factoidal.SHACL
