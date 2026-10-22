/-
Harness.ProofObligations — open proof obligations as expected failures.

CLAUDE.md, "A stated shortfall is a failing test plus an open issue":
a module header that says a theorem is NOT proved must have a test that
fails today, marked as an expected failure with its issue, and the
suite must turn red when the case passes unexpectedly.

A missing theorem cannot be tested by running the library, so the test
here is about the environment: each row names a theorem that does not
exist yet. `lake build` (no target) elaborates this module, because the
`Harness` lib is a default target.

* While the theorem is absent, the build prints
  `XFAIL <name> (<issue URL>)` and continues.
* When a theorem with that name appears, the build FAILS with
  `UNEXPECTED PASS`. The commit that proves the theorem must then also
  remove the row, remove the shortfall prose from the module header,
  apply the consequence named in the row, and close the issue item.

This module imports `Lean` to read the environment. It is in the
`Harness` lib, not in `L4Factoidal`, so no library module, executable
or wasm build imports it.
-/
import Lean
import L4Factoidal.RDFS.SemiNaiveTheorems
import L4Factoidal.OWL.RLSemiNaiveTheorems
import L4Factoidal.RDF.SinkJsonLd

namespace Harness.ProofObligations

open Lean Elab Command

/-- One open obligation: the theorem's full name, its statement in
words, the issue that tracks it, and what changes when it is proved. -/
structure Obligation where
  name        : Name
  statement   : String
  issue       : String
  onProof     : String

def obligations : List Obligation :=
  [ { name := `L4Factoidal.RDFS.semiNaive_saturated
      statement := "∀ g : Graph, Saturated (semiNaive g): closureFuelBound g rounds " ++
        "are enough for the RDFS delta loop (L4Factoidal/RDFS/SemiNaiveTheorems.lean header)"
      issue := "https://github.com/danbri/factoidal/issues/756"
      onProof := "drop the isNaiveFixpoint check and the closureFix fallback from " ++
        "closureSemiNaiveChecked (issue 756, item 4)" },
    { name := `L4Factoidal.OWL.RL.closureFix_saturated
      statement := "∀ g : Graph, step (closureFix g) = closureFix g ∧ " ++
        "ListFuelAdequate (closureFix g) (listFuel (closureFix g)): closureFuelBound g " ++
        "rounds and listFuel are enough for the OWL 2 RL loop, naive and semi-naive " ++
        "(the same list by indexedClosureSN_eq; L4Factoidal/OWL/RLSemiNaiveTheorems.lean " ++
        "header, L4Factoidal/OWL/RLTheorems.lean header items 2 and 3)"
      issue := "https://github.com/danbri/factoidal/issues/756"
      onProof := "drop the saturation and ListFuelAdequate hypotheses from " ++
        "indexedClosureSN_complete and mem_indexedClosureSN_iff (issue 756, item 4 for OWL RL)" },
    { name := `L4Factoidal.RDF.Sink.jsonLdStream_readBack
      statement := "the flattened JSON-LD document of the stream writer (Writer.jsonld with " ++
        "jsonLdStream), read by JSONLD.parseJsonLd, has the quads the writer got, up to blank " ++
        "node labels (L4Factoidal/RDF/SinkJsonLd.lean header; checked by #guards and " ++
        "tests/sbm11/export_roundtrip.sh only)"
      issue := "https://github.com/danbri/factoidal/issues/943"
      onProof := "remove the 'checked, not proved' sentences from SinkJsonLd.lean, Sink.lean " ++
        "and the parsing-strategy record section 3m" } ]

run_cmd do
  let env ← getEnv
  let mut xfail : Nat := 0
  for o in obligations do
    if env.contains o.name then
      throwError m!"UNEXPECTED PASS {o.name} ({o.issue}): the theorem now exists. " ++
        m!"Remove this row, {o.onProof}, and close the issue item."
    else
      logInfo m!"XFAIL {o.name} ({o.issue}): not proved: {o.statement}"
      xfail := xfail + 1
  logInfo m!"proof obligations: 0 pass, 0 fail, {xfail} expected-fail (out of {obligations.length})"

end Harness.ProofObligations
