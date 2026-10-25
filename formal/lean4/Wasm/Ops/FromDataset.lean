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
import L4Factoidal.RDF.NormalizeSet

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

/-- `withOpsDataset` for a dataset that is a set of quads (RDF 1.1 Concepts section 3):
`datasetForOpsSet` does not index the triples a second time
(`RDF/NormalizeSet.lean`). -/
def withOpsSetDataset (mode : Mode) (ds : Dataset) (h : ds.IsSet) (k : Dataset → String) : String :=
  match datasetForOpsSet mode ds h with
  | .error e => errJson (fmtParseError e)
  | .ok ds' => k ds'

/-- `withOpsSetDataset` answers what `withOpsDataset` answers. -/
theorem withOpsSetDataset_eq (mode : Mode) (ds : Dataset) (h : ds.IsSet) (k : Dataset → String) :
    withOpsSetDataset mode ds h k = withOpsDataset mode ds k := by
  unfold withOpsSetDataset withOpsDataset
  rw [datasetForOpsSet_eq]

/-! ### Named graphs with no triple (https://github.com/danbri/factoidal/issues/876)

RDF 1.1 Concepts section 4: a named graph can be empty, and TriG states one (`GRAPH <g> { }`).
N-Quads cannot, so the text round trip drops it. `keepEmptyNamed ds d` adds to `d` each named
graph of `ds` that has no triple and whose name `d` does not carry (once per name), after the
graphs of `d`. When `ds` has no such graph the result is `d` (`keepEmptyNamed_of_noEmpty`). -/

/-- Add the empty named graphs of `ds` that `d` lacks. -/
def keepEmptyNamed (ds d : Dataset) : Dataset :=
  { d with named := ds.named.foldl (fun acc ng =>
      if ng.graph.isEmpty && !(acc.any (fun x => x.name == ng.name)) then acc ++ [ng] else acc) d.named }

private theorem foldl_keepEmpty_id (l acc : List NamedGraph) (h : ∀ ng ∈ l, ng.graph.isEmpty = false) :
    l.foldl (fun acc ng =>
      if ng.graph.isEmpty && !(acc.any (fun x => x.name == ng.name)) then acc ++ [ng] else acc) acc = acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons ng rest ih =>
    simp only [List.foldl_cons]
    have h1 : ng.graph.isEmpty = false := h ng (List.mem_cons_self ..)
    rw [h1]
    simp only [Bool.false_and]
    exact ih acc (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem keepEmptyNamed_of_noEmpty (ds d : Dataset) (h : ∀ ng ∈ ds.named, ng.graph.isEmpty = false) :
    keepEmptyNamed ds d = d := by
  unfold keepEmptyNamed
  rw [foldl_keepEmpty_id _ _ h]

/-- `withOpsSetDataset` that keeps the named graphs with no triple. -/
def withOpsSetDatasetKeepEmpty (mode : Mode) (ds : Dataset) (h : ds.IsSet) (k : Dataset → String) : String :=
  withOpsSetDataset mode ds h (fun d => k (keepEmptyNamed ds d))

end L4Wasm.Ops
