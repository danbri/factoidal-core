# BubblePopJS JIT: proven equivalent to the interpreter

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

## After the design review (issue 471): fuel monotonicity and the statement for tiers

The review asked for three things before more tier-1 work: the register machine as a parameter
of the run, the `blockN` cases in the syntax scanners, and a proof spike on fuel monotonicity
of the whole evaluator block, the property every whole-run statement needs.

Done, on `wip/jit-proof` (PR 487, for main) and here:

- `HeapOf.useVm` (default on; `BUBBLEPOP_VM=off` for `leanjs`): the reference is the evaluator
  with the machine off. Test262 tree: the same verdict lists with the machine on and off.
- `blockN` in `Stmt.contOutF` and `genEnter` (this branch only: tier 1 is not on main). A
  module's top-level statements are never rewritten into `blockN`: the module's function is a
  generator and tier 1 does not enter generator bodies (test in `ModuleTests`); top-level
  `await` is not parsed yet.
- **Fuel monotonicity was false.** 69 handlers in the block caught every completion, halts
  included. IteratorClose after a throw dropped everything, so an out-of-fuel halt in an
  iterator's `return` was dropped and the run went on: a `for`-`of` over such an iterator,
  whose body throws, ended `ok [caught]` at fuels 18 to 59 and `ok [closed, caught]` above. Now
  `catchJS` passes every halt (fuel, steps, full heap) through its handler; only `Expr.chain`
  (optional chaining's `shortSignal`) and the handlers that restore state and rethrow keep
  `tryCatch`. No difference on Test262.
- The relation `Le x y` ("`x` ran out of fuel, or ends exactly as `y` does": value or
  completion and the whole heap, so output, jobs, host state and steps left; a host call
  receives the steps left and sees the same count) with rules for the monad, handlers and the
  library's loops and maps (`JS/FuelMono.lean`). A generator (`tools/fuelmono-gen.py`) writes
  the induction hypothesis over the 116 functions of the block that take fuel and a step lemma
  per function, proved by one tactic that walks the two bodies apart. **75 of 116 steps are
  proved** (31 s, peak 3.1 GB). Not proved: 21 bodies with local closures (`do` join points;
  inlining them ran out of memory) and the 20 largest bodies. Whole-block monotonicity is not
  proved yet.

What it cost and what blocked:

- Equation lemmas are available, slowly: `evalStmt` 3 s, `evalExpr` 25 s, `extraNative` 111 s,
  `callNative` 573 s with no heartbeat limit. They time out under the default limit.
- Memory, not time, is the limit. One file with all 116 steps reached 17 GB and filled swap;
  proof checks now run one group per process under a memory cap. Splitting pure `match`es and
  inlining `let`s multiplies the goals; extracting the `let`s (`lift_lets; extract_lets`) took
  `binop` from out of memory to 4 s.
- Next, in order: a tactic that pairs the two sides' join points and proves them related once;
  the natives moved out of the block behind their entry points (the review's suggestion), which
  removes about 3,500 lines and the two slowest equation lemmas; then the 20 large bodies one
  per process.

### The tier statement, restated

For a tier `T` and its compile function, the statement is now: for every heap `s` (any host
and `hostCall`, machine off) and fuel `n`, if the evaluator at `n` ends with a result other than
`halt "fuel"`, then for every large enough fuel `m` the tier ends with the same result: the same
value or completion and the same heap, so the same output, host state and steps left at every
host call. For tier 1 the node lemmas (`incLocal_eq`, `setLocal_eq`, `arith_eq`, `blockN_eq`)
are equalities at every fuel, which is stronger and implies this statement for each node.

The composition for tier 1 (a run with rewritten function bodies against a run with the
plain ones) is still out of reach, and for a reason the spike makes precise: tier 1 rewrites
the bodies stored in closures in the heap, so the two runs have different heaps, and the walk
that proves the steps above relies on the two sides being the same term but for fuel (every
helper call closes by reflexivity). The composition needs a heap relation ("equal but for
tier-1 rewriting of function bodies") preserved by every helper that reads an object: the 206
definitions of `Interp.lean` outside the block as well as the 116 inside. Fuel monotonicity is the smaller
first instance of the same induction; it should be finished before this one is started.
