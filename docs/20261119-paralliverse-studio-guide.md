# Developing with the Paralliverse studio

Paralliverse separates a typed program, its sequential meaning, and its execution path. The studio exposes those parts: edit a small program, inspect the original and fused syntax trees, run the CPU interpretation, and compare an admitted GPU plan with that result. [Open the Hub](https://danbri.github.io/factoidal/web/hub/paralliverse/) · [Studio work and evidence](https://github.com/danbri/factoidal-core/issues/647) · [Typed-program foundation](20261119-paralliverse-typed-programs.md)

## Start with an experiment

Choose **Word studio**, or select one of its experiment cards. Enter a program such as:

```text
map multiply 3
map add 1
```

Enter a flat JSON array of unsigned decimal words, for example `[0, 1, 4294967295]`. Choose **Run CPU + GPU**, or press Command/Control + Enter. Live updates run after edits; turn them off to inspect a result before the next run. Editing while paused clears the old result and waits for an explicit run.

Use **CPU result** or **GPU readback** to choose the coloured field's source. Each view keeps its own actual returned words; the GPU view waits for GPU readback. One cell represents one returned word, and its colour mapping is only a display convention. The numeric CPU and GPU results remain visible below it. A match is an actual byte comparison from that run. An empty output is a successful zero-word result, not an unavailable result.

**Signal loom** can request a bounded sequence of 32 phases. Choose **Play 32 frames**, **Step one frame** or **Stop**. The input fixture stays fixed while the requested add operand moves through 0, 8, …, 248 after actual matching GPU results. Each phase still goes through Lean and GPU execution. The next request is scheduled only after the current request's GPU comparison succeeds. Stop, edits, mode changes, a refusal or a runtime/device failure stop the sequence; a previously submitted frame can finish. Playback starts only by an explicit action. These presentation controls are host behaviour, separate from the program-equivalence theorems.

The browser editor accepts the bounded command language above. Lean parses it and constructs the typed program. It does not compile arbitrary Lean source in the browser. Commands are case-sensitive; spaces and tabs separate tokens, surrounding whitespace and blank lines are accepted, and comments are not part of this command grammar. Operands are unsigned decimal `UInt32` values; an operand with leading zeros other than `0` is rejected.

Three or more commands can still produce a CPU result, up to the command limit. The present GPU selector then gives an explicit refusal. The page does not label the CPU result as a GPU result.

**Stable packing** is a separate experiment. Its input is a JSON array of rows, such as `[[8, 3], [], [8, 0]]`. The result keeps the row order and duplicates while omitting empty rows. Its existing GPU plan uses Count, Scan and Scatter. Switching experiments keeps the two input forms separate.

## Use the same typed program from Lean

The following self-contained example uses the ergonomic pipeline constructors. `pipeline` takes a first pass and a list of subsequent passes, so it always constructs a nonempty program.

```lean
import L4Factoidal.Paralliverse.StudioProgram

namespace ParalliverseGuide
open L4Factoidal.Paralliverse

def experiment : Studio.WordPipeline :=
  Studio.pipeline (Studio.multiply 3) [Studio.add 1]

#guard Studio.runCPU 4 experiment [0, 1, 4294967295] ==
  [1, 4, 4294967294]

example (workers : Nat) (xs : List UInt32) :
    Studio.runCPU workers experiment xs =
      Program.eval WordProgram.base (@WordProgram.reference) experiment xs :=
  Studio.runCPU_eq_source workers experiment xs

example (factor offset : UInt32) :
    Studio.pipeline (Studio.multiply factor) [Studio.add offset] =
      WordProgram.affine factor offset :=
  Studio.pipeline_affine factor offset

end ParalliverseGuide
```

The guard is an executable example. The subsequent propositions reuse the library's refinement and source-correspondence theorems. Word multiplication and addition wrap modulo 2³². They do not implement unbounded natural-number arithmetic.

`Studio.runCPU` evaluates the fused program through the existing task-based CPU interpreter. Its worker count is a parameter to that interpreter, not a promise that the host will use that many physical threads. In the Hub's Wasm runtime, the worker also keeps program evaluation off the page's main thread. Task scheduling, resource use and speed are separate from result equality.

The underlying pieces are available independently:

| Need | Module or definition |
| --- | --- |
| Shapes, typed syntax and sequential meaning | `L4Factoidal.Paralliverse.Program` |
| Task-based interpretation and its generic refinement | `L4Factoidal.Paralliverse.ProgramCPU` |
| Closed word operations, affine and packed-affine examples | `L4Factoidal.Paralliverse.ProgramWords` |
| Ergonomic word pipelines and command parsing | `L4Factoidal.Paralliverse.StudioProgram` |
| Studio reports, exported source and initial GPU buffers | `L4Factoidal.Paralliverse.Studio` |
| Partial GPU selection and fixed shader exports | `L4Factoidal.Paralliverse.WordMapGPU` |
| Optional existing Dataflow stage adapter | `L4Factoidal.Paralliverse.ProgramDataflow` |

## Read the rewrite and the GPU plan separately

The source program has two whole-list maps. `Program.fuseMaps` rewrites adjacent pure maps into one map whose scalar body composes multiplication and addition. `Program.eval_fuseMaps` relates the actual transformed syntax to the original sequential meaning. It is one bottom-up pass, not a claim of a canonical normal form or measured improvement.

The rewrite applies to pure, total interpretations. It must not be transferred to effectful or fallible traversals without another proof: two staged traversals and an element-at-a-time fused traversal can report different first errors.

The current GPU selector deliberately recognises original one-map or two-map syntax. It returns fixed add/multiply shader tags and the source program's coefficients. It does not recognise the fused scalar sequence inside one map. The studio therefore evaluates the fused form on the CPU and selects the original form for the GPU. These are distinct transformations with distinct correctness obligations.

This self-contained example names the actual selection boundary:

```lean
import L4Factoidal.Paralliverse.WordMapGPU

namespace ParalliverseSelectionGuide
open L4Factoidal.Paralliverse

example (factor offset : UInt32) :
    WordMapGPU.select? (WordProgram.affine factor offset) =
      some (.two ⟨.multiply, factor⟩ ⟨.add, offset⟩) :=
  WordMapGPU.select_affine factor offset

example (factor offset : UInt32) :
    WordMapGPU.select? (Program.fuseMaps (WordProgram.affine factor offset)) = none :=
  WordMapGPU.select_fused_affine factor offset

end ParalliverseSelectionGuide
```

The **GPU execution plan** inspector shows the Lean-produced buffer contents, source/destination identifiers, coefficients, shader selectors, workgroups and expected complete readback. A word buffer has a two-word header followed by its logical payload and spare tail. Each pass reads one buffer and writes to a distinct destination, preserving its header and tail. For two passes, the first returned destination becomes the second source without intermediate CPU reconstruction. Its second header word already holds the coefficient needed by the second pass.

The host submits those passes and reads the final destination. The complete-frame comparison checks the header and spare tail as well as the logical payload. It is possible to inspect each expected word in the plan. This catches some transport and addressing errors that a payload-only comparison would miss; it does not prove the browser's GPU implementation.

## Define another primitive language

`Shape` constructs types from named scalars, pairs and lists. A `Signature` assigns each primitive symbol an input and output shape. `Program` then supplies identity, sequential composition, product, fanout and list map. `PrimitiveEval` gives meanings to the symbols separately from the program tree.

Here is a complete small extension with a closed add symbol. Explicit `UInt32.add` keeps the scalar operation clear across the dependent shape interpretation.

```lean
import L4Factoidal.Paralliverse.ProgramCPU

namespace ParalliverseExtensionGuide
open L4Factoidal.Paralliverse

inductive Scalar where
  | word

abbrev word : Shape Scalar := .scalar .word

def base : Scalar → Type
  | .word => UInt32

inductive Op : Shape Scalar → Shape Scalar → Type where
  | add (amount : UInt32) : Op word word

def meaning {a b : Shape Scalar} :
    Op a b → Shape.Value base a → Shape.Value base b
  | .add amount, value => UInt32.add value amount

def addEach (amount : UInt32) : Program Op (.list word) (.list word) :=
  .map (.prim (.add amount))

example (workers : Nat) (amount : UInt32) :
    Program.runCPU base (@meaning) workers (addEach amount) =
      Program.eval base (@meaning) (addEach amount) :=
  Program.runCPU_eq_eval base (@meaning) (@meaning)
    (fun _ _ => rfl) workers (addEach amount)

end ParalliverseExtensionGuide
```

This example uses the same primitive interpretation on both sides. Its primitive agreement is definitional; the reused theorem covers the program structure and task-based mapping. To use a different primitive implementation, supply that implementation and establish agreement with the reference on every primitive input. The generic CPU refinement lifts that premise to the complete typed program.

The syntax has no host-function-literal constructor. An extension can nevertheless put functions inside its own scalar carriers or symbol parameters. Extension authors must choose closed symbols and an encoding when they need serialisation or compilation. A new signature does not automatically gain the word shader backend merely because one of its operations is called `add`.

The optional `Program.asStage` adapter exposes a fused CPU program through the existing `Dataflow.Stage` interface. It takes the error type, scalar interpretation, reference and implementation interpretations, their primitive agreement, the worker count and the typed program. Importing that adapter is separate from importing the generic core. Port wiring, named assumptions and whole-graph guarantees remain obligations of the existing Dataflow graph interfaces.

## Limits and diagnostics

| Boundary | Current admission |
| --- | --- |
| Studio program text | ASCII commands, at most 512 UTF-8 bytes |
| Program length | One through sixteen nonempty map commands |
| Word operand | Decimal integer from 0 through 4294967295 |
| Flat Studio input text | At most 16,382 UTF-8 bytes |
| Logical word input | At most 1,024 words, including empty input |
| Combined Studio ABI request | At most 16,895 bytes, including the NUL separator |
| Word GPU source syntax | One map, or one sequence of two admitted maps |
| Word GPU launch | Workgroup size 64; at most sixteen workgroups |
| Packing input | At most 128 rows and 1,024 logical words |
| Share link | At most 16 KiB of encoded experiment state before base64 |
| Signal loom playback | At most 32 phase requests per explicit Play action; one current frame awaiting acknowledgement |

The program and request byte-limit checks precede their parser work. Syntax errors identify the relevant command line. Larger valid CPU pipelines get a GPU refusal rather than a fabricated GPU output. Empty programs, unsupported commands, invalid words and exceeded input limits get diagnostics. The current constraints are explicit boundaries of this implementation, not restrictions on all possible Paralliverse extensions.

## Save an experiment and inspect its source

**Share this experiment** puts the mode, original editable program and input in a URL fragment. The fragment is local page state, not a certificate or a precomputed answer. Opening it still sends the program and input through Lean before execution. A malformed or oversized fragment is rejected. When clipboard access is unavailable, the page exposes a selectable link.

**Copy Lean source** and **Download .lean** use `leanSource` returned by the runtime after a successful Studio request. The page does not synthesise another Lean implementation. The exported file imports `StudioProgram` and defines the actual original constructor tree as a `Studio.WordPipeline`. Place it in the matching Factoidal Lean project. Add inputs and call `Studio.runCPU`, or use the generic reference and refinement theorems as in the first example. Changing the editor invalidates the old export until the next successful run.

## Interpret the evidence

The [typed-program worknote](20261119-paralliverse-typed-programs.md), [GPU work item](https://github.com/danbri/factoidal-core/issues/646) and [Studio evidence record](https://github.com/danbri/factoidal-core/issues/647) name exact source revisions, compiler jobs, public theorem names and remaining obligations. The number of checked declarations must come from those successful compiler records; this guide does not assign a count to an in-progress source revision.

Keep these three results distinct:

- Kernel-checked equations relate the stated Lean functions and formal execution models under their hypotheses.
- Executable guards and CPU/GPU byte comparisons test concrete executions. A successful comparison is not a theorem about every input.
- Lean compilation, Wasm glue, byte transfer, browser shader compilation, the driver, hardware and actual command ordering remain trust or host boundaries unless a separate result covers them.

CPU parsing/evaluation times and GPU end-to-end times include different work. Neither is an isolated hardware compute measurement, and the studio does not infer a speedup ratio. No performance measurement is established merely by compiling the equations.

Further source constructs, more general GPU plan composition and GPU lowering of fused scalar bodies are next work in [the compiler item](https://github.com/danbri/factoidal-core/issues/646) and [the Studio item](https://github.com/danbri/factoidal-core/issues/647). The typed core already permits other signatures and structural programs; extending the admitted shader fragment requires its own semantics, successful compilation and appropriate device tests.
