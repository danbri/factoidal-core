# Typed Paralliverse programs and pure map fusion

19 November 2026. Paralliverse can express a standalone modular arithmetic computation, or compose that computation with its existing stable packing stages. Each program records its input and output shape and the primitive symbols it invokes. [Work item 644](https://github.com/danbri/factoidal-core/issues/644) · [Project 604](https://github.com/danbri/factoidal-core/issues/604)

## Writing a program

`Shape` builds types from application-defined scalar names, products and lists. A signature indexes each primitive symbol by its input and output. Identity, sequence, product, fanout and list map build a typed `Program`. The value interpretation of scalar names and the interpretation of primitive symbols are supplied separately. The syntax has no constructor for a Lean function literal. A new signature owns its choice of symbols, serialisation and backend support. [Program syntax and denotation](../formal/lean4/L4Factoidal/Paralliverse/Program.lean)

For example, the closed word signature has symbols for stable packing, multiplication by a `UInt32` literal, and addition of a `UInt32` literal. A standalone affine transform has this syntax.

```lean
.seq (.map (.prim (.multiply factor))) (.map (.prim (.add offset)))
```

`packedAffine` first packs its rows, then returns the packed words paired with the transformed words. `nestedAffine` applies the same arithmetic to nested rows and a companion flat list, preserving both output shapes. Specialising the symbols and literal parameters gives an ordinary static Lean program value. [Closed word programs](../formal/lean4/L4Factoidal/Paralliverse/ProgramWords.lean)

## The two evaluations

The reference interpreter runs list maps sequentially. The CPU interpreter visits the same constructors independently and uses the existing `Par.mapChunks` task implementation at every list map. Its compositional proof needs agreement on each primitive applied to an input. It then covers every complete program, including nested maps, for every worker count. The ordered-result theorem takes a permutation of the actual CPU map's ordinal-tagged results and relates collection to the sequential source meaning. It retains the host obligation to attribute each reply to the intended job. [CPU interpreter and ordered result](../formal/lean4/L4Factoidal/Paralliverse/ProgramCPU.lean) · [Existing task map](../formal/lean4/L4Factoidal/Par/Chunked.lean) · [Ordered collection](../formal/lean4/L4Factoidal/Paralliverse/Ordered.lean)

In the word signature, the reference pack uses `StaticPack.packSpec`. The other interpretation evaluates `DSL.packProgram` with count, exclusive scan and scatter dispatches, the supplied initial memories and the canonical valid schedule. Its readback refines the reference through `DSL.eval_packProgram_eq_packSpec`. The two arithmetic primitives use Lean's modular `UInt32` operations in both interpretations. The scalar primitive agreement for these operations is definitional. [Existing staged evaluator and theorem](../formal/lean4/L4Factoidal/Paralliverse/DSL.lean) · [Packing reference](../formal/lean4/L4Factoidal/Paralliverse/StaticPack.lean)

## What the pass changes

`fuseMaps` visits the source syntax bottom-up. At a sequential composition, if the transformed children are maps, it produces one map of their composed element programs. Its correctness law compares the denotation of the actual transformed tree with the original tree. For `packedAffine` there is also an exact syntax equation identifying one map inside the fanout. A pass can create another pair of adjacent maps inside a newly composed element body. The pass runs once and makes no fixed-point or performance claim.

Purity matters. For source values `[0, 1]`, suppose the first operation fails on `1` and the second operation fails on `0`. Two effectful list passes report the first operation's failure. An element-at-a-time fused pass would report the second operation's failure. An executable example exercises this difference. The typed program's denotation is total and has no effectful-map constructor. [Executable examples](../formal/lean4/Harness/ParalliverseProgramGuards.lean)

## Composition with Dataflow

`Program.asStage` uses the existing `Dataflow.Stage.ofFun`. Its implementation runs the fused CPU program and its contract compares the output with the original sequential meaning. An application with matching Dataflow wires can use `Component.ofStage` and `PortComponent.ofComponent` to expose it to the existing graph. Port compatibility and the graph's named assumptions remain governed by `Graph.guarantee_sound`. The Dataflow import is confined to the adapter. [Adapter](../formal/lean4/L4Factoidal/Paralliverse/ProgramDataflow.lean) · [Stage contracts](../formal/lean4/L4Factoidal/Dataflow/Stage.lean) · [Graph contract](../formal/lean4/L4Factoidal/Dataflow/Graph.lean)

## Evidence and limits

All eight public declarations below compiled at `d2f52e0d6a175a8b1654bf1315d2b6acd16f1a95` with Lean 4.33.1 in [fresh-source run 44594683425](https://github.com/danbri/factoidal-core/actions/runs/44594683425). The three lanes compiled 4, 9 and 81 source modules respectively; every compiler exit was zero. Each mandatory individual axiom report and each hygiene audit passed. Permitted axioms were only `propext`, `Classical.choice` and `Quot.sound`; the first fusion result needed only `propext` and `Quot.sound`, and the syntax equation only `propext`.

| Namespace | Checked declaration |
| --- | --- |
| `Program` | `eval_fuseMaps` |
| `Program` | `runCPU_eq_eval` |
| `Program` | `runCPU_fuseMaps_eq_eval` |
| `Program` | `collect_mapCPU_eq_eval` |
| `WordProgram` | `fuseMaps_packedAffine` |
| `WordProgram` | `runCPU_affine` |
| `WordProgram` | `runCPU_packedAffine` |
| `Program` | `asStage_run_iff` |

These namespaces are within `L4Factoidal.Paralliverse`. The nine executable guards also passed, separately from those universal proofs. They cover empty and repeated words, wraparound, nested lists, product, fanout, reverse-order receipts and the effectful counterexample. The physical GPU evidence for the existing packing workload is recorded separately in the project issue. This milestone concerns typed syntax, pure source semantics, one syntactic rewrite and the Lean CPU task evaluator. General shader emission, target-specific admission, task progress and measured speed require further work. [Exact-source evidence](https://github.com/danbri/factoidal-core/issues/644) · [Next typed GPU lowering milestone](https://github.com/danbri/factoidal-core/issues/646) · [Existing GPU work](https://github.com/danbri/factoidal-core/issues/604)
