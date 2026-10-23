/-
L4Factoidal.Storage.Sbm11.StoreCapsConnection — how the SBM11 store and the
`StoreCaps` records meet (https://github.com/danbri/factoidal/issues/975,
phase B, step B1).

## Why `Sbm11.IdQuery.Store` is not a `StoreCaps`

The two interfaces differ in four ways, each by design:

1. Effects. `Store m` returns `ExceptT String m _`: a read can fail (a short
   file, a bad block), and the I/O store runs in `IO`. `StoreCaps` is pure and
   total; its only failure channel is the `decodeFailure` flag.
2. Level. `Store m` gives blocks, PRB1 bytes and term ids, and the dictionary
   (`idOf`, `termOf`). `StoreCaps.solve` gives decoded triples.
3. Graph scope. One `Store m` holds the whole dataset; the graph id is a column
   of each row. A `StoreCaps` record holds one graph (`PatternBound` has no graph
   position); a dataset is a `DatasetCaps` or a `DatasetBackend`, one record per
   graph.
4. Evaluation. The SBM11 engine evaluates a whole pattern on ids
   (`IdQuery.evalBgpM`, merge joins, semi-joins) and decodes only the final
   rows. It never asks a per-pattern triple solve. A `StoreCaps` view of SBM11
   would be a decode adapter that the SBM11 engine does not call, so a theorem
   about it would say nothing about the engine.

## Where they meet: the denotation

Both sides are stated against one `DatasetDen`:

* the SBM11 side: `PackSpec.den_packSpec`, the generation denotes its input
  (`G.den = inputDen qs decl`), and `PackSpec.harness_where_allowed_den`, the
  WHERE clause of the harness answers `Allowed` for every set `D` that denotes
  the input;
* the `StoreCaps` side: `indexedDatasetBackend_exact` (`Storage/PlannerSoundness`),
  the dataset record of `D` is lawful with the denotation `D.den`.

`sbm11_record_denotes`: for the generation of `packSpec` and a set `D` that
denotes the input, the dataset record of `D` is lawful with the generation's
own denotation `G.den`. So the SBM11 answers (through
`harness_where_allowed_den`) and the answers of the `StoreCaps` evaluator over
`indexedDatasetBackend D` are both about the one dataset `G.den`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.DenotationTheorems
import L4Factoidal.Storage.PlannerSoundness

namespace L4Factoidal.Storage.Sbm11.PackSpec

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11.MemGen
open L4Factoidal.Storage.PlannerSoundness

/-- **The SBM11 generation and a lawful record denote one dataset.** -/
theorem sbm11_record_denotes (B : Nat) (qs : List Quad) (decl : List Subject) (G : MemGen)
    (F : FileGen) (h : packSpec B qs decl = some (G, F)) (D : Dataset) (hset : D.IsSet)
    (hdist : distinctNames D.named) (hden : D.den = inputDen qs decl) :
    DatasetBackendExact G.den (SPARQL.StoreDataset.indexedDatasetBackend D) := by
  rw [den_packSpec B qs decl G F h, ← hden]
  exact indexedDatasetBackend_exact hset hdist

#print axioms sbm11_record_denotes

end L4Factoidal.Storage.Sbm11.PackSpec
