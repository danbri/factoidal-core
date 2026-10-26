/- Positive control for `CertifiedDatasetDuplicate.lean`: the same construction
with the triple once. This file MUST elaborate, so that the failure of the
duplicate fixture comes from the duplicate and not from a broken fixture. No
build target imports it; `tools/check-certified-dataset.sh` runs it. -/
import L4Factoidal.RDF.CertifiedDataset

open L4Factoidal.RDF

def singleDataset (t : Triple) : CertifiedDataset :=
  ⟨{ default := [t], named := [] }, by
    constructor <;> simp [Graph.KeyNodup, Dataset.names]⟩
