---
name: danbri-function-precrime-checkers
description: Catch a function's resource-scaling defects — stack depth, live memory, or time that grows with input size — by MEASUREMENT during the ordinary test run, before the defect causes a crash on a large input in production. Use when adding or changing any parser, decoder, serializer, closure, or fold over input-proportional data; when writing a new stress or corpus test; when a crash "only happens on big inputs"; and when deciding whether a green suite actually proved the code scales. The name is the owner's (2026-09-07); the idea is not well known under any standard name, so it keeps his.
---

# Function pre-crime checkers

A function that recurses, allocates, or loops in proportion to its input has a
crash latent in it that the test suite does not see, because the test files
are small. The disaster arrives later, on a real input, in a place with a
smaller budget than the test machine (a browser tab's ~1 MB stack, a phone's
memory, a request timeout). This session paid for that four times in two days:
a manifest decode that overflowed a tab at 36,000 entries, an XML pre-pass
that overflowed at ~7,000 characters, an F\* SHACL command that segfaulted at
2,610 shapes, and a wasm packer that leaked 15.6 bignums per quad. Every one
ran the whole existing suite green first.

The defect has a signature you can measure BEFORE it crashes: **a resource
whose peak tracks the input size.** Pre-crime checking is watching for that
correlation during the ordinary run, so the defect is a failing test at size
1,000 rather than a support ticket at size 1,000,000. It is the resource
analogue of the repository's score discipline: a green test that never
measured scaling is the resource version of an unlabelled numerator.

## The three resources and how each betrays itself

| resource | crash it causes | the signature | the fix pattern |
|---|---|---|---|
| stack depth | stack overflow / segfault | one frame per input item: a recursive call not in tail position | accumulator or worklist loop; keep the recursive spec, prove a `@[csimp]` twin |
| live memory | out-of-memory / allocator abort | bytes retained per input item after the item is processed | free per item; on wasm32 watch for `Nat`/`Int` literals ≥ 2^31 boxed per call (`skills/lean4-wasm-export` trap) |
| time | timeout / apparent hang | superlinear wall time: a nested scan, a quadratic dedup, a re-decode per query | index, sort-then-scan, or hoist the repeated work; measure, do not guess |

The stack and the quadratic-time defects look identical from a distance ("it
hangs on big inputs") and are cured differently. On 2026-09-07 the 36,000-entry
manifest was BOTH: a non-tail decode that overflowed a tab, and, separately, a
quadratic `uniqueArtifactKeys` that owned the 300-second wall time. Making the
decode tail-recursive fixed the overflow and moved the tab from crash to hang;
only the quadratic fix removed the hang. **Do not assume one cause.** Measure
which resource is scaling before you fix anything.

## Three checkers, cheapest first

### 1. The static scan (Lean: `tools/lean-tail-recursion-audit.py`)

Reads the compiled IR (`formal/lean4/.lake/build/ir/**/*.c`): Lean turns a
direct tail self-call into `goto _start`, so any self-call surviving as a real
C call is one stack frame per step. It lists every such function and every
mutual-recursion cycle, maps each back to its Lean declaration, and classifies
what bounds the depth: input length, input tree depth, a counter, or a fixed
structure. `--gate` fails the build on a NEW input-length recursion against
`tools/lean-tail-recursion-allow.txt`; `--fstar` runs the coarser scan over
`formal/fstar/ocaml-output/*.ml` (OCaml compiles only direct tail calls to
jumps too, so the same defect exists there — issue 674, the SHACL segfault).

Limits, stated in the tool: it cannot see recursion through higher-order
combinators (`List.foldr` and friends), inlined or specialised bodies, or the
memory and time resources at all. It is the first line, not the whole line.
Its own war story: the first version delimited a C body by a `}` in column 0
and truncated every body at its first nested block, reporting 24 recursions
instead of 833 and missing both known cases — an audit that finds almost
nothing is evidence about the audit's reach before the code (anti-pattern 28).

### 2. The canary run: the whole suite under a small budget

Run the existing corpora once with a deliberately small stack, so anything
input-proportional fails early WITH A NAME instead of on a giant input later:

- native probes: `LEAN_STACK_SIZE_KB=512` in the environment of the run, never
  `ulimit -s` (the Lean runtime sizes the stack of the thread that runs `main`
  itself; see "The canary measured nothing" below), and never without a
  control that shows the budget reached the process
  (`tests/stack/run.sh --canary` carries one);
- wasm: build the diagnostic module with `-sSTACK_SIZE=262144
  -sSTACK_OVERFLOW_CHECK=2` (emscripten then names the overflowing function
  instead of dying silently); the shipping module never carries these;
- Node: a small `--stack-size` on a worker thread (the main thread segfaults
  on macOS rather than throwing).

This needs no new inputs — the W3C corpora are already large enough to trip a
512 KB stack where an 8 MB one hid the defect. It is a CI job, not a debugger
session, and it covers the whole tree every run.

### 3. The scaling assertion: n, 2n, 4n

For each parser, decoder, serializer and fold, run inputs of size n, 2n, 4n
and record peak stack (a depth counter under a build flag, or `/usr/bin/sample`
stack sampling — the method of `docs/designissues/2026-09-05-shard-pack-profile-and-memory.md`),
peak RSS (`/usr/bin/time -l`), and wall time. Assert stack is FLAT in n, memory
is at most linear, time is at most linear (or the stated complexity). This is
what turns "it worked on the test files" into "it scales", which is the
property the suite was silently not testing. `tests/stack/` is the seed; the
assertion is what makes it a gate.

A worked example with a wall-clock bound is `l4jsonld-api --scale`
(`formal/lean4/Harness/JsonLdScale.lean`, wrapper
`tests/stack/jsonld_scaling.sh`). It builds five document shapes at n, 2n,
4n, 8n and 16n, keeps the minimum of several runs per point, and fails when
time(4x) exceeds 9.0 times max(time(x), 20 ms): a linear-times-log phase
gives about 4.5, a quadratic phase about 16, and the 20 ms floor stops a
sub-millisecond baseline from turning timer noise into a failure. Before
the 2026-10-10 repair of the JSON-LD node map, 11 of the 30 size pairs of
the node map and flatten phases failed (base 100, five shapes); after it, 0
of the 45 pairs of the node map, flatten and frame core phases fail.

A worked example that checks memory as well as time is
`tests/stack/lenient_scaling.sh` (the lenient parse of
https://github.com/danbri/factoidal/issues/716 through its streaming path):
n, 2n, 4n and 8n statements with errors spread through the input, under
`/usr/bin/time -v`; it fails when time(2x) exceeds 2.6 times max(time(x),
1 s) or when the peak resident set at 8n exceeds 1.25 times the one at n
plus 64 MiB. On 2026-10-10, 25 MB to 204 MB of N-Quads kept a peak of 26.9
to 27.3 MB.

## The rule

1. **A function over input-proportional data is not done until its scaling is
   measured, not assumed.** A green suite on small files proves correctness on
   small files.
2. **Measure which resource scales before fixing.** Stack, memory and time
   present the same symptom and have different cures; one input can carry more
   than one defect.
3. **Keep the readable definition; prove the fast one equal.** The accumulator
   or indexed version runs; the structural version stays for the proofs; a
   `@[csimp]` lemma or a stated equality theorem ties them, so no round-trip
   theorem is lost. Never a bigger stack, never `partial def`, never
   `native_decide` to paper over it.
4. **The scan is the gate for stack; the canary and the scaling assertion are
   the gate for what the scan cannot see.** A new input-length recursion that
   is genuinely bounded goes in the allow-list with the reason, the way a
   local test override carries its issue URL.

## Pointers

- `tools/lean-tail-recursion-audit.py` (the scanner and `--gate`),
  `tools/lean-tail-recursion-allow.txt` (the reasoned exceptions).
- `tests/stack/` (the deep-input stress suite and the canary run).
- `skills/lean4-performance/SKILL.md` (the fix patterns, measure-first rule),
  `skills/lean4-proof-patterns/SKILL.md` (the `@[csimp]` twin recipe),
  `skills/lean4-wasm-export/SKILL.md` (the big-literal memory trap),
  `skills/perf-benchmarking/SKILL.md` (the `sample` timing method),
  `skills/fstar-module-style/SKILL.md` (extraction is not stack-safe; the
  OCaml scan).
- War stories: issues 670 (manifest decode and the quadratic dedup), 673 (XML
  line-ending pre-pass), 674 (F\* SHACL segfault), 658 (the wasm bignum leak).

## Two corrections paid for on 2026-09-08

- **The canary IS portable; earlier "UNSUPPORTED on macOS" was too broad.** A
  browser-tab overflow is a V8 CALL-STACK overflow, and `node --stack-size=NNN`
  bounds that on macOS and Linux alike (measured: the 40k-entry manifest case
  throws under `--stack-size=512` before the fix, passes after). What is NOT
  controllable on macOS is a native Lean binary's main-thread stack (`ulimit
  -s` and `LEAN_STACK_SIZE` do not reach it), which is a DIFFERENT stack.
  (Superseded 2026-10-10: the native stack IS controllable, with
  `LEAN_STACK_SIZE_KB`; neither name measured on 2026-09-07 is read by the
  runtime. `tests/stack/run.sh --canary` now runs both routes.) The wasm
  canary runs the wasm cases in Node under a small `--stack-size`. The wasm
  shadow-stack flag `-sSTACK_SIZE` bounds yet another stack and is not what a
  tab overflow needs. This class hid behind the native canary once (https://github.com/danbri/factoidal/issues/678 and
  the manifest-inspect JSON overflow) — always run the wasm/JS canary.
- **`@[csimp]` does not rewrite a call inside a `mutual` block.** The
  manifest-inspect fix's first attempt swapped the JSON list writers with a
  csimp twin and the emitted C still had the non-tail call, because the writers
  are mutually recursive. The cure is accumulator functions with an equality
  theorem to the readable spec (`JSON/Serialize.lean` `toStringItemsAcc`), not
  csimp. Check the emitted C, never assume csimp took.
- **A still-broken shortfall is an expected-failure in the suite, not a red
  gate and not a silent skip** (https://github.com/danbri/factoidal/issues/678, turtle-collection): the case passes the
  suite WHILE it overflows and turns the suite red if it ever stops, so the fix
  flips the marker and closes the issue. (It worked as written on 2026-10-10:
  the repair made the native canary report "UNEXPECTED PASS: flip this xfail",
  and the flip is in the same commit as the repair; see the last section.)

## Two findings paid for on 2026-10-10 (https://github.com/danbri/factoidal/issues/746)

- **On Linux the native canary knob is `LEAN_STACK_SIZE_KB`, not `ulimit -s`
  and not `LEAN_STACK_SIZE`.** A Lean executable runs `main` on a thread
  whose stack the runtime sizes itself; the binary reads
  `LEAN_STACK_SIZE_KB` (the string is in every Lean executable). Measured on
  linux-x86_64 with toolchain 4.33.1: a verbatim copy of the old
  `OwlXml.readAxioms` ran 2,000,000 elements deep under `ulimit -s 1024` and
  overflowed only at 20,000,000 on the default stack, so `ulimit -s` did not
  reach it; under `LEAN_STACK_SIZE_KB=1024` the same copy aborted ("Stack
  overflow detected. Aborting.", exit 134) at about 18,500 elements.
  Until the repair of https://github.com/danbri/factoidal/issues/749 the
  native canary of `tests/stack/run.sh --canary` set `ulimit -s` and
  `LEAN_STACK_SIZE` (bytes) and so measured nothing on Linux either; it now
  sets `LEAN_STACK_SIZE_KB` and carries a control (next section).
- **The canary numbers for six repairs of that day** (200,000 elements, the
  replaced definition copied verbatim into a scratch executable, because a
  `csimp` theorem rewrites every call of the library's own copy):

  | function | old form under `LEAN_STACK_SIZE_KB=1024` | largest n that ran (1024 KB) | new form, 200,000 at 1024 KB | new form, 2,000,000 at 256 KB |
  |---|---|---|---|---|
  | `OwlXml.readAxioms` | Stack overflow | about 18,100 | ran, 110 ms | ran, 1,359 ms |
  | `OwlXml.elsOf` | Stack overflow | about 24,300 | ran, 24 ms | ran, 603 ms |
  | `XML.Canonical.canonNodes` | Stack overflow | about 24,300 | ran, 21 ms | ran, 219 ms |
  | `OWL.Comp.compListCells` | Stack overflow | about 11,900 | ran, 321 ms | ran, 3,420 ms |
  | `OWL.Struct.mapSeq` | Stack overflow | about 10,300 | ran, 53 ms | ran, 549 ms |
  | `RML.decodeUtf16?` | Stack overflow | about 14,600 | ran, 19 ms | ran, 416 ms |

  On the default native stack the old forms all ran at 200,000; only the
  reduced stack shows the defect. Run the canary with the reduced stack.
- **The audit cannot see a symbol that ends in `___redArg`.** The compiler
  emits a reduced-arity copy `f___redArg` for many definitions; the audit
  does not strip that suffix, cannot map the symbol to its Lean declaration,
  and classifies it `unknown`, outside the gate. `OwlXml.readList` was one
  (repaired in the same landing). Treat the `unknown` class as unaudited,
  not as clean.

## The canary measured nothing for a month (https://github.com/danbri/factoidal/issues/749, 2026-10-10)

The native canary of `tests/stack/run.sh --canary` was written on 2026-09-07
and set two things the Lean runtime does not read. Its own probe (`turtle-collection`
under the two old names) ran to completion, so the mode reported "UNSUPPORTED",
exited 0, and no native canary case ever ran. The 2026-09-07 note that `ulimit -s`
and `LEAN_STACK_SIZE` "do not reach a Lean binary's main thread on macOS" was
true of those two names and was read as a statement about the platform; the
header added "Linux honours `ulimit -s` for the main thread; run the canary in
CI", which the measurement of 2026-10-10 contradicts (a verbatim old
`OwlXml.readAxioms` ran 2,000,000 deep under `ulimit -s 1024`). Cost: 33 days
(2026-09-07 to 2026-10-10) with no native canary, and a wasm canary that scored
cases which had not run (below). The repair:

- **The knob, with its source.** `src/runtime/thread.cpp` of leanprover/lean4
  tag v4.33.1 (the elan toolchain ships no runtime sources, only the string in
  `libleanrt.a`): line 171 `const char * stack_size_env =
  std::getenv("LEAN_STACK_SIZE_KB");`, line 174 `sz = sz / 4 * 4 * 1024; // as
  in `Shell``, and line 193 `set_thread_stack_size_from_env();` in
  `lean_run_main`, which then runs `main` on a NEW thread of that size. The
  value is kilobytes, rounded down to a multiple of 4. The default thread
  stack is 1 GB on 64-bit (line 27; 8 MB for wasm), not the host's 8 MB.
  `LEAN_MAIN_USE_THREAD=0` runs `main` on the process main thread, where
  `ulimit -s` applies; the canary unsets it.
- **The control.** `tests/stack/StackControl.lean` holds `foldNonTail`, a
  non-tail fold over a list (one native frame per element) that imports
  nothing from `L4Factoidal`, so no library repair can change what it
  measures. `run.sh` compiles it with `lean -c` and `leanc` through `lake env`
  in `formal/lean4` (about 2 s) and runs it three times: 100 elements under the
  canary budget must run; N = max(200000, 400 x KB) elements under the canary
  budget must abort with "Stack overflow detected" (exit 134); the same N
  elements at the default budget must print the sum. If any run differs, or
  the control cannot be compiled, the native canary records one failing case
  named `control`, scores none of the canary cases, and prints
  `native canary: NOT SCORED (...)`. `tests/stack/canary_control.sh` shows the
  control can fail: with `STACK_CANARY_VAR=LEAN_STACK_SIZE` (the old name) the
  control must refuse (2 pass, 0 fail, out of 2). `run.sh --control-only`
  runs the control alone.
- **Measured 2026-10-10, linux x86_64, Lean 4.33.1, control program.** Largest
  n that ran under `LEAN_STACK_SIZE_KB` = 256: 12,142; 512: 20,334; 1024:
  36,718; 2048: 69,486; 4096: 135,022 (about 32 bytes per element). With no
  variable (1 GB), 20,000,000 elements ran in 3.6 s. At the 512 KB canary the
  control (204,800 elements) aborts in 15 ms.
  The 512 KB canary on the repository cases: `turtle-collection` (100,000
  items) aborts, tracked in https://github.com/danbri/factoidal/issues/678;
  `xml-entities` (10,000 sequential entity references) aborts, found by this
  run (below); the other five cases run.
- **The wasm canary passed a module that did not exist.** It decided "threw"
  by grepping the output for `call stack|RangeError|overflow`, so when
  `docs/web/hub/assets/l4/l4factoidal.mjs` was missing (the module is a build
  product, gitignored since the 2026-10-09 split and installed by
  `tools/fetch-builds.sh --set web`, so a fresh worktree lacks it) the
  case printed `ok:false, Cannot find module` and the canary scored "wasm ok
  under --stack-size=512" for six cases that never ran. The scoring now takes
  the case's own JSON line: `ok:true` is a run, `Maximum call stack size
  exceeded` is an overflow, everything else is an error, and a missing module
  records one failure and scores nothing. Rule: score a pass only from a
  positive answer of the thing measured (here `ok:true`); never from the
  absence of an error message.
- **A cause found by gdb, not by the audit.** `xml-entities` under
  `LEAN_STACK_SIZE_KB=512` aborts; `gdb -batch -ex run -ex 'bt 12' --args
  l4wasm-cli call parseToDatasetJson args-xml.json` names the repeating frame:
  `L4Factoidal.XML.scanRefs` (`XML/Parser.lean:1173`), one frame per entity
  reference, because the recursive call is followed by the combination of its
  result. The tail-recursion audit's report on this tree does not list it. The
  case is an expected failure naming the open issue
  https://github.com/danbri/factoidal/issues/673 in the native canary, the wasm
  canary and the wasm route; it turns the suite red when it starts to pass.
- **Result after the repair.** `tests/stack/run.sh --canary` on 2026-10-10:
  29 pass, 0 fail (out of 29), of which six rows are expected failures
  (`xml-entities` and `turtle-collection`, each in the native canary, the wasm
  canary and the wasm route). Before the repair the suite could not start
  (the generator raised `RecursionError`, exit 2).
- **The case generator.** `tests/stack/gen_cases.py` built the 5,000-deep
  JSON-LD case as a nested dict and called `json.dumps`, which raises
  `RecursionError` at that depth on Python 3.13, so the suite could not start.
  It writes the nesting as text now (byte-identical to the old output at
  depths 0, 1, 2, 3 and 10).

## A mutual-block recursion where each step needs the NEXT step's result (https://github.com/danbri/factoidal/issues/678, 2026-10-10)

`Syntax/Turtle.lean` `readCollectionRest` read a collection `( e1 ... en )`
with one recursive call per element, inside the `readObject` mutual block.
It is not an accumulator conversion: cell i's `rdf:rest` is cell i+1's blank
node, which is allocated only after element i+1 is read. The repair, and the
pattern for this shape:

- **Two passes inside the block, the second a fold.** `readCollectionCells`
  reads an element (`readObject`), allocates the element's cell, pushes
  (node, term, triples) onto a newest-first list and makes a tail call. At
  the `)` the fold `linkCollectionCells` writes the cells' triples, last cell
  first. The allocation order is unchanged (element, then its cell), so the
  blank-node labels are unchanged. Check the emitted C: `readCollectionCells`
  and `linkCollectionCells` each carry one `goto _start;` and no self-call.
- **The readable form moves out of the block, with three theorems.**
  `readCollectionRest` is now defined after the block (it calls `readObject`,
  which is a constant there). `readCollectionCells_eq` proves the loop equal
  to it with the earlier cells linked in front, for every fuel, errors
  included; `readCollection_eq` restates `readCollection` in the F* source's
  form; `@[csimp] readCollectionRest_eq_TR` covers any caller of the readable
  form. The audit row of `readCollectionRest` moved from `unknown` (the audit
  does not map mutual-block definitions; https://github.com/danbri/factoidal/issues/750)
  to `replaced`.
- **Measure the output, not only the stack.** `l4factoidal parse --out
  nquads`, strict and `--lenient`, on the 1,022 `.ttl` and `.trig` files of the
  W3C RDF 1.1 and 1.2 suites, against a copy of the binary from before the
  change: 2,044 of 2,044 outputs byte-identical. The W3C runner compares
  graphs up to blank-node renaming, so it cannot see a label change; the byte
  comparison can.
- **Canary numbers, native, `LEAN_STACK_SIZE_KB=512`, `parseToDatasetJson` on
  `ex:s ex:p ( 0 1 ... n-1 ) .`:**

  | | largest n that ran | first n that overflowed | n = 100,000 |
  |---|---|---|---|
  | before | about 4,500 | 4,531 | overflow (also at 1,024 and 4,096 KB) |
  | after | 100,000 (not limited by stack) | none found | ran, 200,001 quads |

  `tests/stack/run.sh --canary`, after: 29 pass, 0 fail (out of 29);
  `turtle-collection` runs in the native canary (512 KB), the wasm canary
  (Node `--stack-size=512`, 4,545 ms) and the wasm route (4,313 ms); the
  only expected failures left are the three `xml-entities` rows
  (https://github.com/danbri/factoidal/issues/673). Before the repair the
  same suite was 29 pass, 0 fail (out of 29) with six rows expected failures
  (the issue 749 section above); the wasm module of that run was not rebuilt
  here, so the wasm "before" is that record, not a new measurement.
- **The bound that stays is nesting.** Three frames per nesting level
  (`readObject`, `readCollection`, `readCollectionCells`): at 512 KB,
  `( ( ( ... ) ) )` ran at 2,897 levels and overflowed at 2,909 (before:
  2,000 ran, 2,500 overflowed). That is a `depth` bound, which the document's
  own nesting sets.
- **A probe past the suite's sizes can exhaust the machine.** The probe at
  n = 1,000,000 through `l4wasm-cli call parseToDatasetJson` was killed by
  the memory cgroup (exit 137) at about 13.7 GB resident, and the kernel
  killed another agent's job in the same cgroup. Run such a probe under
  `prlimit --as=4000000000`, so that it fails alone. Node cannot run
  WebAssembly under that limit (it reserves the wasm memory's address space
  in advance); size a wasm probe from the native peak first
  (`/usr/bin/time -v`).
