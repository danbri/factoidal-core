/-
Wasm.Ops.FromDataset — run a stateless op on a dataset the caller has
already parsed.

The stateless RDF ops (`queryDataset`, `updateDataset`,
`canonicalizeToNQuads`, `owlClosure`, ...) take N-Quads text. The command
line (`Wasm/Cli.lean`) reads its input in any format into a `Dataset` and,
until 2026-10-10, wrote that dataset as canonical N-Quads and handed the
text to the op, which parsed it again: 74.7 percent of the instructions of
a COUNT query (https://github.com/danbri/factoidal/issues/724).

`withOpsDataset mode ds k` gives `k` the dataset that round trip produces,
through `RDF.datasetForOps` (`RDF/DatasetNormalize.lean`): the normalised
dataset, built without text, when `roundTripSafe mode ds` holds, and the
text round trip otherwise. `withOpsDataset_eq` proves the result equal to
the round trip's for EVERY dataset, so each `*Of` op in `Query.lean`,
`Canon.lean` and `Reason.lean` answers the envelope the text op answers on
`Dataset.toCanonicalNQuads ds`, byte for byte (`queryDatasetOf_eq` and the
others).

Targeted imports only — never the L4Factoidal umbrella (see
`Wasm/Abi.lean`'s import note).
-/
import Wasm.Ops.Support
import L4Factoidal.RDF.DatasetNormalize

namespace L4Wasm.Ops

open L4Factoidal.RDF
open L4Factoidal.Syntax

/-- Run `k` on what the op family would parse from `ds` written as canonical
N-Quads, in `mode`; a failure of that parse is the op's error envelope. -/
def withOpsDataset (mode : Mode) (ds : Dataset) (k : Dataset → String) : String :=
  match datasetForOps mode ds with
  | .error e => errJson (fmtParseError e)
  | .ok ds' => k ds'

/-- `withOpsDataset` answers what parsing the canonical text answers. -/
theorem withOpsDataset_eq (mode : Mode) (ds : Dataset) (k : Dataset → String) :
    withOpsDataset mode ds k =
      (match parseNQuadsFast (Dataset.toCanonicalNQuads ds) mode with
       | .error e => errJson (fmtParseError e)
       | .ok ds' => k ds') := by
  unfold withOpsDataset
  rw [datasetForOps_eq]

end L4Wasm.Ops
