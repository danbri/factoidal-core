/-
L4Factoidal.RML.Run — read, validate and evaluate a mapping graph.

The one entry point a runner or a host calls: it joins the three
library layers in the order RML-Core implies. A mapping that breaks a
MUST clause is rejected BEFORE any record is read (`RML.Validate`); a
valid mapping is read into the model (`RML.FromGraph`) and evaluated
(`RML.Eval`), and any data or source error the evaluation meets rejects
the whole run.

## A rejected run has no quads

RML-Core says a data error is an error of the run, not of one triple:
"Otherwise, raise a data error". A processor that kept the triples
generated before the error would hand a caller a partial dataset that
looks like a complete one. `EvalResult.quads` is therefore empty
whenever `errors` is not, and `Rejected` names the case.
-/
import L4Factoidal.RML.Validate
import L4Factoidal.RML.Eval

namespace L4Factoidal.RML

open L4Factoidal.RDF
open L4Factoidal.JSON

/-- Validate a mapping graph, then evaluate it. -/
def runMappingGraph (g : Graph) (defaultBase : Option String)
    (docFor : String → Option Json) : EvalResult :=
  let static := validateMapping g
  if !static.isEmpty then { quads := [], errors := static }
  else
    let r := evalMappingE defaultBase (mappingOf g) docFor
    if r.errors.isEmpty then r else { quads := [], errors := r.errors }

/-- Was the run rejected? -/
def EvalResult.rejected (r : EvalResult) : Bool := !r.errors.isEmpty

end L4Factoidal.RML
