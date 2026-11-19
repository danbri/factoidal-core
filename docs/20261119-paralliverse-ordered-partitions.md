# Paralliverse ordered partition results

19 November 2026. This work contributes a partition-result contract to the wider CPU, worker, remote and GPU programme. [Work item 641](https://github.com/danbri/factoidal-core/issues/641) · [Paralliverse 604](https://github.com/danbri/factoidal-core/issues/604)

## The question

A coordinator assigns ordinal `0` through `n - 1` to a fixed list of tasks. Each successful reply carries its ordinal and a value. How can a coordinator combine the values in planned order when replies arrive in completion order? For stable word packing and ordered query scans, concatenating in completion order can change the answer.

The proposed opt-in `Ordered.collect?` sorts the replies by ordinal and compares the resulting ordinals with `List.range n`. The value type needs no equality or ordering operation. The exact success condition is

```lean
collect? n replies = some values ↔
  values.length = n ∧ replies.Perm ((List.range n).zip values)
```

A two-task job rejects zero, one or three replies. Even two replies fail if their ordinals are `[0, 0]` or `[0, 2]`. For a three-task job, arrivals `[(2, [7]), (0, [7]), (1, [])]` yield `[[7], [], [7]]`, preserving both equal values and the empty task. A job with zero tasks accepts the empty reply list.

The second obligation connects ordinals to actual tasks. For a list `tasks`, an evaluator `run : TaskInput → Except Error Value`, and a successful collection, if every reply agrees with `run` on its own indexed task then `tasks.mapM run` returns the collected values. The coordinator validates the ordinal set. Each evaluator or caller must establish the correspondence between an input and its reply.

## Two existing computations

* **Stable packing.** Each element of an array holds one part of an input, in source order. `Par.mapChunks workers (fun part => packParallel part prior) parts` is the existing CPU task map applied to the count, exclusive-scan, scatter and readback model. Attach the planned ordinals to those answers and permit any permutation. The proposed theorem states that collecting and flattening produces `packSpec parts.toList.flatten` for every worker count, partition, and prior word memory. The proof uses the existing CPU mapping and packing equalities and associativity of ordered concatenation. [CPU task map](../formal/lean4/L4Factoidal/Par/Chunked.lean) · [Packing definitions and refinement](../formal/lean4/L4Factoidal/Paralliverse/StaticPack.lean)
* **SBM11 ordered block scans.** The native query driver forms `rangeBounds c metas.size` after asking its store for the metadata matching the query key. Its first range runs on the caller. It spawns the others and appends their tables in planned order. The theorem uses `metasFor fullMetadata.toArray spec.key`, these same range bounds, and each range's `boundsList`. The per-task evaluator `scanAccOf` uses the existing `scanBlockM` loop. Concatenating the collected rows gives the single list scan over the selected metadata. [Driver](../formal/lean4/Harness/Sbm11Query.lean) · [Metadata selection](../formal/lean4/L4Factoidal/Storage/Sbm11/PrmRangeTheorems.lean) · [Range construction](../formal/lean4/L4Factoidal/Storage/Sbm11/ParallelScan.lean) · [Ordered scan theorem](../formal/lean4/L4Factoidal/Storage/Sbm11/OrderedScanTheorems.lean)

A key may select an interior slice whose first block starts after PRB1 header byte 6. The complete permutation passes `prmAdmitted`. Requiring that check again on the selected slice would exclude such queries. The split-scan proof needs the selected blocks' row bounds and successful decodes. The new `parallel_acc_eq_of_selected` separates the complete permutation from its selected metadata. Membership transfers the row bounds and successful decodes to each selected block. The existing `parallel_acc_eq` retains its statement. [Split-scan proof](../formal/lean4/L4Factoidal/Storage/Sbm11/ParallelScanTheorems.lean) · [Selection membership](../formal/lean4/L4Factoidal/Storage/Sbm11/MetaCountTheorems.lean)

The existing `Dataflow.Graph` manages named ports, stage assumptions and their composition. Collection is one operation inside a stage. It has no graph vocabulary and introduces no scheduler. The Paralliverse static-compute specification continues to govern programme extraction, lowering and device dispatch. [Dataflow graph](../formal/lean4/L4Factoidal/Dataflow/Graph.lean) · [Static compute specification](../formal/lean4/L4Factoidal/GpuKernel/STATIC_COMPUTE_V0_1.md)

## Assumptions and evidence

An ordinal identifies a position within the coordinator's selected job. A network host must establish job identity, input binding, payload integrity and successful execution. The collector rejects an unprocessed duplicate retry and reports failure for an incomplete batch. There is no timing, progress or retry policy.

The pack result concerns a mathematical word buffer and the logical result of Lean's `Task.spawn`. The scan result uses the `Store Id` instance and ordered lists of rows. Its existing premises require a supported scan specification and denotation, permutation reads that match the given byte array, admitted metadata, decodable blocks, and a disabled overlay. Native IO, table allocation, statistics, Web Workers, remote transports, shaders and device execution need their own evidence.

The examples above describe intended outcomes. Kernel evidence requires fresh compilation of each named theorem and its axiom report. The functional scope is the optional collector. Both existing workloads retain their entry points.
