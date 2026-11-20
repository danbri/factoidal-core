# Paralliverse ordered partition results

19 November 2026. This work contributes a partition-result contract to the wider CPU, worker, remote and GPU programme. [Work item 641](https://github.com/danbri/factoidal-core/issues/641) · [Paralliverse 604](https://github.com/danbri/factoidal-core/issues/604)

## The question

A coordinator assigns ordinal `0` through `n - 1` to a fixed list of tasks. Each successful reply carries its ordinal and a value. How can a coordinator combine the values in planned order when replies arrive in completion order? For stable word packing and ordered query scans, concatenating in completion order can change the answer.

The opt-in `Ordered.collect?` sorts the replies by ordinal and compares the resulting ordinals with `List.range n`. The value type needs no equality or ordering operation. The exact success condition is

```lean
collect? n replies = some values ↔
  values.length = n ∧ replies.Perm ((List.range n).zip values)
```

A two-task job rejects zero, one or three replies. Even two replies fail if their ordinals are `[0, 0]` or `[0, 2]`. For a three-task job, arrivals `[(2, [7]), (0, [7]), (1, [])]` yield `[[7], [], [7]]`, preserving both equal values and the empty task. A job with zero tasks accepts the empty reply list.

The second obligation connects ordinals to actual tasks. For a list `tasks`, an evaluator `run : TaskInput → Except Error Value`, and a successful collection, if every reply agrees with `run` on its own indexed task then `tasks.mapM run` returns the collected values. The coordinator validates the ordinal set. Each evaluator or caller must establish the correspondence between an input and its reply.

## Two existing computations

* **Stable packing.** Each element of an array holds one part of an input, in source order. `Par.mapChunks workers (fun part => packParallel part prior) parts` is the existing CPU task map applied to the count, exclusive-scan, scatter and readback model. Attach the planned ordinals to those answers and permit any permutation. Collecting and flattening produces `packSpec parts.toList.flatten` for every worker count, partition, and prior word memory. The proof uses the existing CPU mapping and packing equalities and associativity of ordered concatenation. [CPU task map](../formal/lean4/L4Factoidal/Par/Chunked.lean) · [Packing theorem](../formal/lean4/L4Factoidal/Paralliverse/OrderedPackTheorems.lean)
* **SBM11 ordered block scans.** The native query driver forms `rangeBounds c metas.size` after asking its store for the metadata matching the query key. Its first range runs on the caller. It spawns the others and appends their tables in planned order. The theorem uses `metasFor fullMetadata.toArray spec.key`, these same range bounds, and each range's `boundsList`. The per-task evaluator `scanAccOf` uses the existing `scanBlockM` loop. Concatenating the collected rows gives the single list scan over the selected metadata. [Driver](../formal/lean4/Harness/Sbm11Query.lean) · [Metadata selection](../formal/lean4/L4Factoidal/Storage/Sbm11/PrmRangeTheorems.lean) · [Range construction](../formal/lean4/L4Factoidal/Storage/Sbm11/ParallelScan.lean) · [Ordered scan theorem](../formal/lean4/L4Factoidal/Storage/Sbm11/OrderedScanTheorems.lean)

A key may select an interior slice whose first block starts after PRB1 header byte 6. The complete permutation passes `prmAdmitted`. Requiring that check again on the selected slice would exclude such queries. The split-scan proof needs the selected blocks' row bounds and successful decodes. The new `parallel_acc_eq_of_selected` separates the complete permutation from its selected metadata. Membership transfers the row bounds and successful decodes to each selected block. The existing `parallel_acc_eq` retains its statement. [Split-scan proof](../formal/lean4/L4Factoidal/Storage/Sbm11/ParallelScanTheorems.lean) · [Selection membership](../formal/lean4/L4Factoidal/Storage/Sbm11/MetaCountTheorems.lean)

The existing `Dataflow.Graph` manages named ports, stage assumptions and their composition. Collection is one operation inside a stage. It has no graph vocabulary and introduces no scheduler. The Paralliverse static-compute specification continues to govern programme extraction, lowering and device dispatch. [Dataflow graph](../formal/lean4/L4Factoidal/Dataflow/Graph.lean) · [Static compute specification](../formal/lean4/L4Factoidal/GpuKernel/STATIC_COMPUTE_V0_1.md)

## Assumptions and evidence

An ordinal identifies a position within the coordinator's selected job. A network host must establish job identity, input binding, payload integrity and successful execution. The collector rejects an unprocessed duplicate retry and reports failure for an incomplete batch. There is no timing, progress or retry policy.

The pack result concerns a mathematical word buffer and the logical result of Lean's `Task.spawn`. The scan result uses the `Store Id` instance and ordered lists of rows. Its existing premises require a supported scan specification and denotation, permutation reads that match the given byte array, admitted metadata, decodable blocks, and a disabled overlay. Native IO, table allocation, statistics, Web Workers, remote transports, shaders and device execution need their own evidence.

## Compiled theorems

Lean 4.33.1 compiled all five public declarations at `4956af6cc69a9155456b94e2b2b827a3801d7471`. The fresh packing and scan jobs compiled six and 141 modules respectively. All compiler exits were zero. Each declaration reported exactly `[propext, Classical.choice, Quot.sound]` and both hygiene checks passed. The compiler used one thread, a 2 GiB Lean cap, a 4 GiB operating-system cap and a 180-second limit per source. [Packing log](https://github.com/danbri/factoidal-core/actions/runs/44566901613/job/135711022833) · [Scan log](https://github.com/danbri/factoidal-core/actions/runs/44566901613/job/135711023500)

All names in the table start with `L4Factoidal.`.

| Import | Public declaration within `L4Factoidal` |
| --- | --- |
| `Paralliverse.Ordered` | `Paralliverse.Ordered.collect?_eq_some_iff`, `Paralliverse.Ordered.mapM_eq_of_collect?` |
| `Paralliverse.OrderedPackTheorems` | `Paralliverse.StaticPack.collect_mapChunks_pack` |
| `Storage.Sbm11.ParallelScanTheorems` | `Storage.Sbm11.ParallelScanTheorems.parallel_acc_eq_of_selected` |
| `Storage.Sbm11.OrderedScanTheorems` | `Storage.Sbm11.ParallelScanTheorems.scan_rangeBounds_eq_collected` |

The pre-existing `parallel_acc_eq` also passed strict compilation with the same axiom report. The optional Lake target is `ParalliverseOrderedProofs`. Its modules are independent of the browser demonstration.

## Executable examples

Nine guards passed in the packing job above. Seven exercise the collector directly. One reverses the results of actual CPU packing tasks with an empty part and repeated words. One reverses the native driver's three bounds over five block positions. [Example source](../formal/lean4/Harness/ParalliverseOrderedGuards.lean)

The tenth guard passed in the scan job above. It decoded the eleven-block PRB1 fixture, selected key `3`, and returned four ranges in reverse. The selection started after the first block, ended before the last block, and produced all sixteen expected projected tuples with their duplicates. The per-block evaluator in this guard is `blockOut`. The general theorem above uses `scanAccOf`. [Storage example](../formal/lean4/Harness/ParalliverseOrderedScanGuards.lean) · [Verification record](https://github.com/danbri/factoidal-core/issues/641)
