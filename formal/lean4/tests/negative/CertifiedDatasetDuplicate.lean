/- Negative fixture: this file MUST FAIL to elaborate. No build target imports
it; `tools/check-certified-dataset.sh` runs it.

A `CertifiedDataset` whose default graph lists one triple two times needs a
proof of `Dataset.IsSet`, and that proof does not exist: the tactic leaves the
goal `False`. Compare `CertifiedDatasetSingle.lean`, the same text with one
occurrence, which elaborates. -/
import L4Factoidal.RDF.CertifiedDataset

open L4Factoidal.RDF

def duplicateDataset (t : Triple) : CertifiedDataset :=
  ⟨{ default := [t, t], named := [] }, by
    constructor <;> simp [Graph.KeyNodup, Dataset.names]⟩
