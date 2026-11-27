# BubblePopJS JIT: proven equivalent to the interpreter

Copied to `main` on 2026-11-27 from branch `wip/jit-c` (PR 486,
https://github.com/danbri/factoidal-core/pull/486), unchanged below this note, so that its
measurements stay findable when PRs 475, 476 and 486 are closed. Since then, tier 1 landed as the
run's `Mode` parameter (PR 557), and tier 2 as a property cache was measured and not landed
(`designissues/2026-11-25-tier2-property-reads.md`). Order of work from 2026-11-27: CLAUDE.md,
"BubblePopJS JIT: order after tier 2".

Status: design draft, 2026-11-15. Tracking issue:
[BubblePopJS JIT: proven equivalent to the interpreter](https://github.com/danbri/factoidal-core/issues/471). Related: [BubblePopJS plan and key results](https://github.com/danbri/factoidal-core/issues/378),
[the plan record](https://github.com/danbri/factoidal-core/blob/claude/foafnaut-perf-bottlenecks-7hpt38/docs/designissues/2026-11-09-bubblepopjs-plan.md),
[WasmVM AOT record](designissues/2026-11-08-wasmvm-aot.md).

## Goal

BubblePopJS gets faster tiers of execution, and every tier is proved to compute what the
interpreter computes. "The interpreter" is the definitional evaluator of
[`JS/Interp.lean`](../formal/lean4/L4Factoidal/JS/Interp.lean): `evalExpr`, `evalStmt`,
`callClosure` and the rest of its mutual block, over the heap of `JS/Value.lean`, in the monad
`EStateM Abrupt Heap`. It is the reference: a tier is correct when it gives the same
`EStateM.Result` as the evaluator, which is the same value or the same abrupt completion
(a thrown JavaScript value, or a halt: fuel, step budget, full heap) together with the same
heap, so the same console output, the same DOM commands and the same step count.

The JIT targets the speed of pure JavaScript execution. The cost of the bridge between scripts
and the DOM (Wikipedia script turns of 30 to 65 s) is separate work and is not in this record.

## Where the engine is today

- The evaluator: about 10,600 lines, one mutual block of structural recursion on a fuel
  argument (`termination_by structural`), so every function is total and has equation lemmas.
  `defaultFuel` is 2^31 - 1; fuel falls by one for each nested evaluation and each loop
  iteration. The script's real budget is `Heap.steps` (`tick`, `tickCall`, `charge`).
- The resolver ([`JS/Resolve.lean`](../formal/lean4/L4Factoidal/JS/Resolve.lean)): names to
  `Expr.local name hops idx`, function layouts (`FunInfo`). A slot is a hint: `lookupLocal`
  compares the slot's name with the name and falls back to the plain lookup, so a wrong hint
  costs time, never a wrong value.
- The register machine ([`JS/Compile.lean`](../formal/lean4/L4Factoidal/JS/Compile.lean),
  `vmLoop`): functions whose environment no closure can keep (`frameLocal`) with plain
  parameters, and top-level loops (`Stmt.compiled`). It is on by default (`useVm`) and it is
  **not proved**: it is tested by running Test262 and the benchmarks with it on and off.
  In the terms of this record it is an unproved tier, and the work below either proves it or
  replaces it.
- Theorems about the evaluator today are about helpers (number conversions, `tick`, keys,
  descriptors: `JS/Theorems.lean`). No theorem unfolds `evalExpr`.

## Why tier 1 is data, not Lean closures

"Compile once to Lean closures" (each node becomes a `Nat → Ctx → M Value` made once) is the
classic closure-compilation JIT. In Lean it cannot be cached where the evaluator could find it:

- the heap cannot hold a closure over `M`, because `M` is a state monad over the heap
  (a field of type `… → EStateM Abrupt Heap Value` inside `Heap` is not strictly positive);
- the syntax tree (`FunInfo`) is defined before the heap and the monad, so it cannot name the
  closure's type either;
- a code table threaded outside the heap would have to be an argument of every function of the
  mutual block.

So tier 1 is a **pre-resolved tree**: first-order data that the resolver computes once per
function and stores in the syntax tree, as it already stores `FunInfo.code` for the register
machine. The evaluator runs it. This keeps the property that matters for proof: the tier is a
term of the same mutual block, so its correctness is a local statement, proved by unfolding
both sides one step, with no induction over the whole block.

## Tiers

| Tier | What runs | Where | Proof |
| --- | --- | --- | --- |
| 0 | The evaluator on the resolved tree | everywhere | the reference |
| 1 | Pre-resolved tree: specialised nodes chosen once at resolve time (resolved slots, fused leaf operations, blocks known to need no environment, constant conditions, numeric fast paths) | everywhere, every function (closures included) | `rewrite_sound` for each specialisation: the evaluator on the specialised node equals the evaluator on the node it replaces, for every fuel, context and heap |
| 2 | Inline caches over shapes, with guards and deoptimisation to tier 0/1 | everywhere, after shapes and interned keys land (stage C of the plan) | `ic_sound`: guard true implies the cached path equals the lookup; guard false runs the tier-0 path from the same state |
| 3 | Generated WebAssembly run by BubblePopWASM (`WasmVM.Aot` path), later machine code from build-time templates | hosts with a WebAssembly engine (the Hub), later native | `template_refines` against `WasmVM.Spec`, plus a composition lemma; the Wasm engine is trusted as stated below |

The register machine sits between tier 1 and tier 2 in speed. Its compiler gets the tier-1
treatment later (one `step_refines` lemma per instruction against a register-to-slot relation),
or its instructions are rebuilt as tier-1 nodes, whichever proves cheaper.

## The equivalence statement

For each tier T there is a compile function `compileT` from the resolved tree, and the theorem

```
∀ fuel ctx heap e,  runT fuel ctx (compileT e) heap = evalExpr fuel ctx e heap
```

(and the same for statements, statement lists and function bodies). Equality in
`EStateM Abrupt Heap` is the strongest simulation there is: equal value, equal abrupt
completion, equal final heap. Because the heap holds the console output, the host's command
queue, the step counter and the call depth, an equal heap means an equal observable trace.

Two consequences shape the proofs:

- **Fuel is mirrored, not bounded.** A specialised node consumes fuel exactly as the nodes it
  replaces: where the original evaluates a child at `n` and a grandchild at `n - 1`, the
  specialised node matches on the fuel and runs out at the same point with the same
  `halt "fuel"`. The theorem holds for every fuel, not only for large fuel.
- **Steps are mirrored.** `tick`, `tickCall` and `charge` happen at the same points with the
  same arguments, so a script stops at its step budget at the same place in every tier. A tier
  that wants to batch steps (charge a loop's ticks at once) needs a separate theorem that the
  batched charge and the sequence of ticks agree, as `fused_charges_parts` does for WasmVM.

### From local lemmas to the whole run

Tier 1 lives in the evaluator's own mutual block, so the dispatch to it is part of the
evaluator. The local lemma for a specialisation states that the evaluator on the specialised
node equals the evaluator on the original node, with every sub-evaluation done by the same
functions. Since the resolver only ever replaces a node by a specialisation whose lemma holds,
the evaluator run on the specialised tree equals the evaluator run on the unspecialised tree,
by induction on the tree (each rewrite is applied below a node whose evaluation is congruent in
its children). The end-to-end theorem is stated over the tree transformation:

```
∀ fuel ctx heap s,  evalStmts fuel ctx (Tier1.stmts s) heap = evalStmts fuel ctx s heap
```

The fallback is the identity: a node that tier 1 does not handle is left as it is, and the
identity case of the theorem is `rfl`. So "fallback = interpreter" is proved by construction.

### Guards and deoptimisation (tier 2)

A cached fast path has a guard the machine tests (object tag, shape id equal to the cached one,
slot in range). The theorem has two halves:

- guard true: the cached result equals the result of the full lookup on the same state
  (`ic_get_sound`, `ic_set_sound`, from an invariant that a shape id determines the key-to-slot
  map, `shape_lookup_sound`);
- guard false: the node runs the tier-0 code from the state the guard saw. Deoptimisation is
  then not a jump into a different machine: the tier-0 code is the else-branch of the same
  node, so the resumed state is the very state the interpreter would have had, and the
  simulation relation is equality. A tier that keeps values in registers (tier 3, the register
  machine) deoptimises by writing the registers back to the environment slots; the relation is
  "the environment slots equal the registers mapped through the layout", and the lemma is that
  the write-back gives the interpreter's state.

### Termination and fuel

All tiers are total Lean functions, so there is nothing to prove about the tier's own
termination. Fuel is a structural argument; the step budget bounds the run in practice; the
call depth (`maxDepth`) bounds recursion. A tier never adds a loop that the evaluator does not
have; batched work is charged through `charge`.

## What is trusted

- Lean's kernel for the proofs; Lean's compiler and runtime for the evaluator and the tiers
  alike (the tiers add no new trusted code: they are Lean functions).
- Tier 3 adds the WebAssembly side: the relation between `WasmVM.Spec` and the host's engine
  that runs the generated module (the host engine is trusted to implement WebAssembly), and the
  encoder of `WasmVM.Aot`. Machine code later adds one new trusted primitive (writing and
  running executable pages), not started without a separate decision.
- No `sorry`, axioms, `native_decide`, `unsafe` or `implemented_by` anywhere in a tier.

## How equivalence is also tested

Proofs cover the tier's logic; tests cover the build and the parts not yet proved:

- the Test262 tree run with each tier on and off (`leanjs test262 … --list`), verdict by verdict,
  must be identical, with any difference a failure of the change;
- the benchmark corpus (`bubblepop_perf/realworld.py`) on each tier, answers compared with
  QuickJS-NG (differential only: QuickJS-NG is a reference engine, never a fallback);
- `JS/RegressionTests.lean` `#guard`s run with the tier on.

## Performance targets and benchmarks

Measured with `leanjs bench` and the corpus, interpreter and tier on the same build:

- tier 1: at least 1.3 times faster than the evaluator on code the register machine does not
  take (functions with closures, top-level code), and no slower anywhere;
- tier 2: property reads on a monomorphic site at least 3 times faster than the evaluator;
- tier 3: within 3 times of QuickJS-NG on `fib(30)` on the Hub;
- the plan's key results (`fib(30)` at most 30 ns a call, corpus within 2 times QuickJS-NG)
  remain the overall measure.

Benchmarks: `fib`, loops with closures (`for` with `let` in a function that makes a closure),
string building, object property loops, and a real-script workload (a library bundle from the
corpus).

## Where the time goes (measured)

`leanjs` at `5029cc163` on the Mac, a function that makes a closure (so the register machine
does not take it), one million iterations, best of one run each:

| Loop body | ns per iteration |
| --- | --- |
| empty (`for (var i = 0; i < N; i++) {}`) | about 160 |
| `s = s + i` | about 270 |
| `s = s + i * i` | about 360 |
| `s = f(s)` (a call) | about 450 |
| `s = s + o.x` | about 290 |

A sampling profile of the empty loop: more than half of the time is allocation and freeing
(`lean_alloc_ctor`, `mi_free`, `mi_malloc_small`, reference counts, and the thread-local
lookup of the allocator, `_tlv_get_addr`, alone about 18%). Each call of a monadic function of
the evaluator returns a fresh `EStateM.Result`, and each number is a boxed `Value.num`. Writing
`tick` so that it updates the heap in place made no measurable difference, so the heap copies
of `get`/`set` are not the cost; the number of monadic calls per JavaScript operation is.

So tier 1 earns its speed by **fewer evaluator calls per operation**: a specialised node does
in one call, often with no monadic call at all, what the plain tree does in four to eight, and
it falls back to exactly the plain calls whenever its fast path does not apply.

## Tier 1 in this branch

[`JS/Tier1.lean`](../formal/lean4/L4Factoidal/JS/Tier1.lean) rewrites each function body once,
after the resolver and after the register machine's compiler has seen the plain tree, behind the
flag `Tier1.enabled`. It does not enter generator or async bodies (their machine matches on the
syntax), patterns, or top-level loops compiled for the register machine. Four nodes:

| Node | Stands for | Fast path | Theorem |
| --- | --- | --- | --- |
| `incLocal pre inc x h i` | `update pre inc (local x h i)` | a number in a writable slot is read and written in place, with no call of `lookupLocal`/`assignLocal` | `incLocal_eq` |
| `setLocal x h i v` | `assign none (local x h i) v`, `v` not a function expression | no `evalRef`, no pair of options, no `putTarget`; an initialised writable slot is written in place | `setLocal_eq` |
| `arith op a b` | `binary op a b`, `op` one of `+ - * /` | numbers from leaves and nested `arith` nodes combined with no step of the monad (`pureNum`); else the code of `binary` | `arith_eq` (with `arith_fast`, `operand_eval`) |
| `blockN ss` | `block ss`, `ss` declares nothing lexical | no `evalBlock`, no `enterBlock`, no scan of the statements | `blockN_eq` |

Each theorem in [`JS/Tier1Proofs.lean`](../formal/lean4/L4Factoidal/JS/Tier1Proofs.lean) is an
equality of functions of the heap in `EStateM Abrupt Heap`, for every fuel and context, with the
same children on both sides. `tE_incLocal`, `tE_setLocal`, `tE_arith` and `tS_blockN` state that
the pass makes each node only from the node its theorem names, under that theorem's side
condition. The proofs use only Lean's standard axioms (`propext`, `Classical.choice`,
`Quot.sound`). They unfold the evaluator's equations by definitional unfolding (`rfl`): the
generated equation lemmas of the 8,000-line mutual block time out, definitional unfolding at a
known constructor takes milliseconds.

Not mechanised: the step from the local equalities to whole runs (above, "From local lemmas to
the whole run"). It is the next proof task: state the evaluator as the fixed point of one
functional over a record of its functions, then the step is one induction on fuel.

### Measured (Mac, 2026-11-15, `5029cc163` against `wip/jit`, best of 3, other builds running)

- Test262, the 6,301 files of the tree: 5,871 pass, 426 fail, 4 skip on both; the verdict lists,
  failure messages included, are identical.
- The real-world corpus (`bubblepop_perf/realworld.py`, lodash, acorn, pako, marked,
  immutable): the same answers on all five; run time over the interpreter 0.97, 1.05, 0.93,
  0.97, 1.00.
- Loops in a function that makes a closure (the register machine does not take them):
  empty `for`, 3 million iterations, 0.59 to 0.54 s; `s = s + i*i - 1` 1.30 to 1.21 s;
  `while (i < n) i++` 0.61 to 0.58 s; a call per iteration 0.48 to 0.46 s.

So tier 1 as it stands gives 5 to 10% on loops and nothing measurable on real code: below the
target of 1.3. The profile explains it: the cost is per evaluator call (the result object, the
reference counts of the tree and the context, the large frame of `evalExpr`), and these four
nodes remove one or two calls from operations that take five to nine.

### Findings for the next steps

- Parameters of the tree and the context are owned, so every call increments and decrements
  them. Marking them borrowed (`@&`, which changes no definition and so needs no proof) made
  loops with work in them 10 to 20% faster (an assignment, a call) and the empty loop 35%
  slower, in one trial build: the hot functions disagree
  on ownership. Worth a systematic pass.
- `evalExpr` is one function with every case of the language: a large frame on each call. Tier
  1 nodes that run whole loops in a small function of their own (a `for` whose test, update and
  body are tier-1 nodes) avoid both the frame and most result objects. Their proofs follow the
  pattern here, with an induction on fuel for the loop.
- Writing `tick` to update the heap in place changed nothing measurable.
- Tier 2 (shapes and inline caches) needs the heap layout of stage C of the plan
  ([#378](https://github.com/danbri/factoidal-core/issues/378)); the guard-and-fallback pattern
  of `arith` (guard: both operands known numbers; else the original code) is the pattern its
  proofs will follow.

## Region code: every function on the register machine (measured 2026-11-15)

Rank 1 of the design review: a function body the register code does not take (it makes a
closure, has parameters that are not plain, uses `arguments`, `try`, `switch`, ...) is
compiled as region code (`Compile.compileRegion`, `Code.region`). Its variables stay in the
evaluator's environments, registers hold temporaries only, register 0 holds `this`, and
anything the compiler does not handle runs in the evaluator from inside the machine
(`evalE`, `evalS`, with `break`, `continue` and `return` completions mapped back). Blocks
and `for (let ...)` loops make, copy, release and leave environments exactly as the evaluator
does (`enterBlk`, `newEnv`, `copyEnv`, `popEnv`), so the heap is the evaluator's heap at
each instruction boundary up to the register scratch fields. Generators and async functions
stay on their own machine; a script with direct `eval` or `with` stays unresolved.

The `for` loop now ticks, copies, updates and tests in the order of `forLoop` (register code
too).

Tools: `BUBBLEPOP_VMSTATS=1 leanjs run F` counts calls by how they ran and, for the tree,
why the register code did not take the function (computed only when counting);
`BUBBLEPOP_VM=off|noregion`; `bubblepop_perf/tiershare.py` splits a `sample` profile between
the register machine and the tree; `bubblepop_perf/wikilike.js` is a closure-heavy script in
the style of a wiki's start-up code (an original construct).

Proved (`JS/RegionProofs.lean`): with the machine or region code off the wrapper statement is
the body one unit of fuel later (`compiled_off`, `compiled_noregion`, `block_is_body`,
`enterBlock_plain`); `pushEnv` puts the record at the slot it answers, with its parent
(`pushEnv_get`, `pushEnv_parent`). Tested, not proved: the instructions against the
evaluator. Test262 (6,301 files): off, register code only, and region code give identical
verdict lists, failure messages included (5,871 pass, 426 fail, 4 skip). The corpus gives
the same answers in all three modes.

Measured (Mac, loaded by other builds, best of 3, user CPU seconds, whole run incl. load):

| Workload | calls in register code before / with regions | tree time share before / with | off | register only | regions |
| --- | --- | --- | --- | --- | --- |
| lodash 4N | 98.9% / 100% | 5% / 6% | 0.77 | 0.40 | 0.40 |
| acorn 4N | 86% / 100% | 52% / 28% | 0.95 | 0.80 | 0.80 |
| pako 4N | 98.4% / 100% | 42% / 13% | 1.94 | 1.73 | 1.71 |
| marked 4N | 66% / 100% | 65% / 7% | 0.20 | 0.21 | 0.20 |
| immutable 4N | 95% / 100% | 13% / 4% | 1.27 | 0.80 | 0.78 |
| wikilike 200 | 67% / 100% | 78% / 40% | 0.31 | 0.29 | 0.33 |

Loops in a function that makes a closure (3M iterations; `callper` 1M): empty `for` 0.57 /
0.54 / 0.44; `s = s + i*i - 1` 1.17 / 1.20 / 0.88; `while` 0.52 / 0.51 / 0.44; a call per
iteration 0.58 / 0.53 / 0.39; a closure call in a `let` loop 0.56 / 0.54 / 0.47.

Findings:

- The premise that real libraries run in the tree does not hold for this corpus: 66 to 99%
  of dynamic calls already ran in register code (the callbacks are small and frame-local;
  the closure-making outer functions run once).
- Region code takes the rest (100% of calls) and moves 30 to 60 points of time from the
  tree to the machine, with no change in run time on the corpus (within noise) and 1.1 to
  1.4 times on closure-heavy loops.
- Where the time is: helpers both machines call (property reads and writes, built-ins,
  allocation and freeing, boxed numbers in environment slots) and, inside the machine, the
  dispatch of `vmLoop` itself (60% of an arithmetic loop's samples are in `vmLoop`'s own
  frame: boxed `Instr`, `Nat` registers and program counter).
- Go/no-go: **no-go** for 2 times on the corpus by rank 1. The register machine over the
  whole register-machine-to-tree gap is 1.0 to 1.9 times on the corpus already (off against
  on), and region code adds nothing measurable there. The next gains are rank 2 (stage C:
  word values, flat heap, shapes and inline caches) and rank 4 (flat instruction words,
  `USize` counters), as the review says. Region code is still worth keeping as the single
  machine that later work proves (`compile_correct` covers every function), and it is
  needed for unboxed locals in closure-making functions.

## Stage C spike: the inner loop, and where stage C pays (measured 2026-11-15)

Branch `wip/jit-c` on `wip/jit-vm`. What was measured first, then what was built.

Where the register machine's time goes. `vmLoop` is one function with an arm for every
instruction, in the evaluator's monad. A loop of number instructions in a frame-local function
(`s = s + i*i - 1`) retires about 1,500 machine instructions per iteration, about 200 per
register-machine instruction, all in `vmLoop`'s own frame (no calls, no allocation). A model of
the same arms in a small function (`bubblepop_perf`-style standalone file, not committed) runs
them in about 90; the same model with flat `UInt32` instruction words and `USize` counters in
about 75. So the size of `vmLoop` costs about 2 times on dispatch, and flat words add about 1.2
times on top: the instruction encoding is not where the time is.

What was built:

- `JS/VmFast.lean`, `vmFastGo`: the register machine's inner loop, a small function over the
  same state (instructions, registers, float registers, the heap). It runs moves, constants,
  number arithmetic and comparisons on number registers, jumps, the step of the budget, the
  heap's fast property read (`HeapOf.fastGetV`), dense array elements, environment slots
  (`getUp`, `setUp`) and the global-name cache. Each arm is `vmLoop`'s arm for the instruction
  written with the same expressions; where an operand fails its test, it stops and `vmLoop` runs
  that instruction. A number written into an environment slot reuses the old number's box
  (`setNumSlot`), so such a loop allocates nothing.
- `Compile.markFastLoops`: the `tick` at the head of a loop becomes `tickF` when every
  instruction from the head to the jump back is one the inner loop runs. Only at `tickF` does
  `vmLoop` call the inner loop. Entering it at every loop head (the first version) made the
  corpus 5 to 14% slower: on a loop whose body calls a function, the entry and exit cost more
  than the few instructions it ran. With the marking, other loops run exactly as before.
- `BUBBLEPOP_VM=nofast` (`HeapOf.vmFastOn`): the inner loop off, for the differential test.

Proved (`JS/VmFastProofs.lean`, `JS/VmFastSteps.lean`, standard axioms only): with the inner
loop off, `vmFast` returns at once and changes nothing (`vmFast_off`), and `tickF` is `tick`
(`vmLoop_tickF_off`); marking only turns a `tick` into `tickF` and keeps the size
(`markAt_cases`, `markFastLoops_size`); the slot write with box reuse is the plain write
(`setNumSlot_eq`, `fastSetSlot_fl`, `fastSetSlot_val`); and for each instruction the inner loop
runs, one step of `vmLoop` with the operands that pass the test is the inner loop's step, one
unit of fuel later (`vmLoop_add`, `vmLoop_jnltK`, `vmLoop_tick`, `vmLoop_getUp_num`,
`vmLoop_getMember_num`, ... 25 theorems). The proofs unfold `vmLoop` by `vmLoop.eq_def`, which
Lean generates in a few seconds. Not mechanised: the induction that strings these steps into
"a run of the inner loop is that many steps of `vmLoop` with the inner loop off", and the step
from there to whole runs, which needs fuel monotonicity (the inner loop uses less fuel than the
steps it stands for; `jit-proof`'s spike). Tested: Test262 (6,301 files) gives the same verdict
list, messages included, with the machine off, region code off, the inner loop off and on; the
corpus and the loops give the same answers in all modes.

Stage C (shapes and inline caches) on the present heap: an object's own properties are a short
key array scanned by pointer first (`PropMap`), so a cache of the slot for a site saves a scan
of a few keys and nothing else, unless "a shape determines the keys" holds, which needs the key
arrays moved out of the objects into a shape table: a change to every property operation of
the evaluator. In sampled profiles of acorn, immutable and pako the property-lookup code
(`fastGet`, `PropMap.scan`, string hashing for big maps, `getOwn`) is 5 to 15% of the samples;
allocation and freeing (`mi_free`, `mi_malloc_small`, `lean_dec_ref_cold`, `lean_del`) 15 to 25%;
`vmLoop`'s own frame 30 to 45%. Go/no-go: inline caches on the present heap, no-go (at most 1.15
times on the corpus); shapes as a heap redesign, only together with word values (the
allocation share), as issue 378 plans; the inner loop, go for loops.
