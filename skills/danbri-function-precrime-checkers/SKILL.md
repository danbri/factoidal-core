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
structure. `--gate` fails the build when a recursive declaration of class
length, depth, counter or unknown has no line in
`tools/lean-tail-recursion-allow.txt` (since 2026-10-10 a declaration is
recursive when it is on a cycle of its module's C call graph, mutual cycles
included; `tools/test_lean_tail_recursion_audit.py` is the tool's self-test);
`--fstar` runs the coarser scan over
`formal/fstar/ocaml-output/*.ml` (OCaml compiles only direct tail calls to
jumps too, so the same defect exists there — issue 674, the SHACL segfault).

Limits, stated in the tool: it cannot see recursion through higher-order
combinators (`List.foldr` and friends), inlined or specialised bodies, or the
memory and time resources at all. It is the first line, not the whole line.
Its own war story: the first version delimited a C body by a `}` in column 0
and truncated every body at its first nested block, reporting 24 recursions
instead of 833 and missing both known cases — an audit that finds almost
nothing is evidence about the audit's reach before the code (anti-pattern 28).

A `for` loop in `Id.run do` is one of those combinators. On 2026-10-12 the
gate passed `Qlvr.mergeSortBy` (three `for` loops in `Id.run`), and the
`tests/stack` case `sbm11-dict` aborted with a stack overflow under the
512 KB canary sorting 20,000 keys: gdb showed
`Std.Legacy.Range.forIn'.loop` called back through `lean_apply_*`, one frame
per element, in Lean's own library where the audit does not look. The same
canary run found `NQuadsStreaming.splitCompleteLines` (allow-listed since the
first baseline) using one frame per character of each 64 KiB parser chunk.
Repairs (https://github.com/danbri/factoidal/issues/788): `mergeSortBy` as
tail calls with fuel; `splitCompleteLines` through a `@[csimp]` loop over
the reversed buffer, proved equal. Write loops over data as tail-recursive
functions, and give every new decoder, sort or fold a canary case: the
canary saw both, the audit saw neither.

Run it as CI runs it: `python3 tools/lean-tail-recursion-audit.py --gate`,
after a full `lake build`, and read the exit code. Without `--gate` the tool
exits 0 whatever it finds. Cost of not doing so: on 2026-10-11 a landing
agent ran the audit without `--gate`, reported "exit 0", and the landing
(factoidal-core 4bfa8b49) went to `main` with 10 recursive declarations
outside the allow list. The next danbri/factoidal-builds run failed at
this gate, so the wasm build and the npm suite did not run
(https://github.com/danbri/factoidal-builds/actions/runs/38141637018). The
repair is 196b62d6.

A green gate does not cover the allow list's UNTRIAGED lines: the gate
passes them, and nothing bounds their depth. Cost, 2026-10-11:
`Syntax.readStringLiteralBody` and `readIriRefBody` were UNTRIAGED. Each
used one stack frame per character of a literal, so a 6,000-character
`geo:asWKT` literal in danbri/londat exhausted Node's default stack in the
npm 0.9.0 wasm `parse()` (https://github.com/danbri/factoidal/issues/779),
with every gate green. The native canary at 512 KB showed it at once
(about 8,100 nested frames). Repair: 6135ee02, which makes both functions
tail calls with an accumulator, proves them equal to the old definitions
(`@[csimp]`), and adds the `tests/stack` case `nquads-long-literal`. Before
relying on an UNTRIAGED function for input-proportional data, triage it.

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

**Set the bound from the stated complexity, with its parameters.** The SBM11
packer phase 2 gate (`tests/sbm11/phase2_scaling.sh`, issue 804) first used
4n ≤ 4.84 × n, "2.2 per doubling", from runs on a quiet machine. The
algorithm is a loser-tree merge of k runs, and with `--run-terms` fixed k grows
with n: the cost is about n · log2 k, and from n to 4n (k 244 to 836) the
model gives 4.89, above the bound. The gate failed at 5.05 under load
(2026-10-13) with no code change. It now uses 6.25 (2.5 per doubling): above
the model plus 10 % for load, far below the 16 of the quadratic defect it
guards. Write the model and the defect's ratio next to every bound.

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

A worked example where the input-proportional quantity is hidden is
`tests/sbm11/phase2_scaling.sh` (https://github.com/danbri/factoidal/issues/804,
2026-10-12). The SBM11 packer's k-way merge of term runs scanned all k run
heads per record. Each run holds at most a fixed number of terms (a memory
bound), so k grows with the source and the scan is quadratic: 799 s of a
1,334 s pack on 8.9 M terms, while olympics (12 runs) looked linear. The test
packs synthetic sources of 0.5, 1 and 2 million lines with
`l4sbm11-pack --phase2-only --run-terms 32768` (124 to 417 runs) and fails
when the two doublings together exceed 2.2 each (4n at most 4.84 times n).
Three details: a merge through a tree still costs log2 k comparisons per
record, one more per doubling, so the ratio per doubling is 2.05 to 2.15,
not 2.0; one run varied by up to 18 % at load 1 to 2.5 on 4 vCPUs, also in
CPU time (other processes share the caches), so single doublings measured
1.86 to 2.38 and the test bounds the two together, with the median of three
runs per size taken in rounds of n, 2n, 4n; and the test reads the CPU time
of the merge thread (`/proc/thread-self/schedstat`), which removes the
scheduling share of the noise. Before the fix: 7,842, 28,769 and 100,264 ms;
after: section 4.1 of
`docs/designissues/2026-10-12-sbm11-stage3.md`.

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
  line-ending pre-pass, then the reference scan `scanRefs`), 674 (F\* SHACL
  segfault), 658 (the wasm bignum leak).

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
  Precisely (measured 2026-10-10, issue 673): csimp cannot replace a call from
  one MEMBER of a `mutual` block to another, because the block is compiled
  before a theorem about its members can be stated. A function that is NOT a
  member, defined and csimp-replaced BEFORE the block, is replaced at its
  call sites inside the block: `XML.scanRefs` is called from the `mutual`
  pair `parseChildren`/`parseElement`, and after
  `@[csimp] scanRefs_eq_scanRefsFast` the emitted C of both calls
  `scanRefsFast`.
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

## The audit passed while two recursions overflowed (https://github.com/danbri/factoidal/issues/750, 2026-10-10)

On core 4b5892b0 `--gate` passed, and the 512 KB canary overflowed in two
functions it did not report. Causes, found in the generated C and the tool:

- `XML.scanRefs` (`lp_l4factoidal_L4Factoidal_XML_scanRefs`, two surviving
  self-calls) was mapped, but classed `counter`: its input is `s : Chars`,
  and `Chars` is `abbrev Chars := Array Char`. The classifier knew only the
  words `List`, `Array`, `String`. The gate did not check `counter`, although
  issue 750 itself said it did.
- `Syntax.readCollectionRest` was classed `unknown`, which the gate did not
  check: a doc-comment line of `readPnameNs` starts with "namespace token, ..."
  (Syntax/Turtle.lean:447), the indexer read it as a `namespace` command, and
  every later declaration of the file got the wrong name. Its seven-function
  mutual cycle was printed and never gated.
- The same audit of the audit found: `section X ... end X` popped a namespace;
  the closure suffix `___lam__N` was not stripped (the tool stripped
  `_lambda_N`, which Lean 4.33 does not emit); a recursive `inductive` was seen
  only with `->`, not `→`; `where` helpers, `let rec` and derived instances
  were not indexed; and the `@[csimp]` mark by short name hid
  `Syntax.readAnnotations` and four more namesakes.

The repair (same landing): comments and string literals are blanked before
indexing; type aliases of list, array and string types count as length
inputs; `counter` and `unknown` are gated; every member of a strongly
connected component of a module's call graph is a gated row; `@[csimp]`
names resolve against the enclosing and opened namespaces. Before: 935
self-recursive C functions, 138 `unknown`, 333 cycles ungated. After: 2,273
recursive C functions (940 with a self-call, 1,333 only through a cycle), 0
`unknown`; 776 declarations were new to the gate. 126 of them are triaged on
the allow list (28 as `(a) PENDING`, listed in
https://github.com/danbri/factoidal/issues/752 and issues 673 and 678), 138
derived `Repr` instances are one pattern line, and 512 cycle members are
marked `UNTRIAGED` (https://github.com/danbri/factoidal/issues/753). Rules:

- Gate every class except those whose bound the tool states (`bounded`,
  `replaced`). Both misses were in an ungated class.
- An indexer that reads source text must skip comments and strings. Without
  that, a prose line that starts with `namespace`, `section` or `end` is read
  as that command.
- Each miss gets a fixture in the tool's self-test that fails on the version
  that missed it (the self-test runs against an older copy with `--tool`).

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

## Nested entity expansion on a worklist (https://github.com/danbri/factoidal/issues/755, 2026-10-12)

The nesting bound recorded at the end of the next section (issue 673) is
repaired.
Three functions recursed once per level of ENTITY nesting (the replacement
text of entity N references entity N-1): `expandEntityValue` (text and
attribute values), `entityHasWsCharRef` (the white-space character-reference
note, called from `scanRefs`) and the markup re-parse of `parseChildren`. Each
now has a twin that keeps the waiting texts on a list (`expandEntityLoop`,
`entityWsLoop`, the mutual pair `parseChildrenW`/`parseElementW`), proved
equal to the readable definition by its functional induction
(`expandEntityLoop_eq`, `entityWsLoop_eq`, `parseChildrenW_eq`), and run by
the compiler through `@[csimp]`. WFC: No Recursion is enforced as before: in
text by the `visited` names, in markup because a self-referencing markup
entity exhausts the fuel and its replacement text then does not parse as
content (WFC: Parsed Entity). There is no nesting limit.

What the repair taught:

- **A chain of `<b>&eN;</b>` measures ELEMENT nesting.** The issue measured
  markup chains of that shape (1,000 ran, 3,000 overflowed natively at
  512 KB). 3,000 plainly nested elements with no entity overflow at 512 KB
  too (`xmlWellformed`, measured 2026-10-12), so that number was the element
  parser's, class (b), and a worklist of replacement texts cannot change it.
  The stack case `xml-markup-chain` therefore keeps the elements flat (level
  N is `<ex:p>N</ex:p>&m(N-1);`): only the entity nesting grows. Before
  choosing a deep-input shape, check that it is deep in ONE dimension.
- **The proof pattern** (induct on the specification, a measure with a
  run-time bound, one named function for an expression both definitions
  match on) is in `skills/lean4-proof-patterns/SKILL.md`, section 9a.

Canary numbers, linux x86_64, Lean 4.33.1, Node 22.22.0, RDF/XML through
`parseToDatasetJson`:

| chain | before, native 512 KB | before, wasm `--stack-size=512` | before, wasm default | after, native 512 KB | after, wasm `--stack-size=512` | after, wasm default |
|---|---|---|---|---|---|---|
| text, 10,000 levels (`xml-text-chain`) | overflows (3,000 runs) | overflows (3,000 runs) | overflows | runs, 3.8 s | runs, 3.2 s | runs, 3.4 s |
| attribute value, 10,000 levels | overflows (3,000 runs) | overflows (3,000 runs) | overflows | runs | runs, 3.3 s | runs, 3.2 s |
| markup, flat, 3,000 levels (`xml-markup-chain`) | runs | overflows (1,000 runs) | runs | runs | runs, 0.4 s | runs, 0.5 s |
| markup, flat, 10,000 levels | overflows | overflows | overflows | runs, 3.8 s | runs, 2.8 s | runs, 2.7 s |
| text and markup, 30,000 levels, native 256 KB | | | | both run | | |
| `<b>&eN;</b>`, 3,000 levels (element nesting) | overflows | | | overflows (class (b)) | | |

`tests/stack/run.sh --canary`: before (base 24d5aab2 and its web build)
45 pass, 0 fail (out of 45), with four rows expected failures (the text chain
in the native canary, the wasm canary and the wasm route; the markup chain in
the wasm canary); after (this branch and a wasm module built from it) 45 pass, 0 fail (out
of 45), with no expected failure left.

## Sequential references read by a loop (https://github.com/danbri/factoidal/issues/673, 2026-10-10)

The `xml-entities` case that the repaired canary found (above) is repaired.
`XML.scanRefs` stays as the readable definition; `XML.scanRefsLoop` carries
the flags of the references already read in its arguments, so every
self-call is a `goto _start` in the emitted C (7 of them, no real
self-call), and `@[csimp] scanRefs_eq_scanRefsFast` (proved through
`scanRefsLoop_eq`) makes the compiler run it at both call sites, which are
inside the `mutual` pair `parseChildren`/`parseElement` (see the csimp note
above). Outputs are byte-identical: native `parseToDatasetJson` on 20
reference documents (10 shapes at 1,000 and 10,000 references), and the
scoreboard rows `l4xmlconf` 1861 pass, 0 fail (out of 1861 scored),
`l4rdfxml-probe`, `l4xslt`, `l4mathml`, `l4schematron`, `l4xsd-datatypes`
and `l4w3c` RDF 1.1, all 14 rows the same before and after.

Canary numbers, linux x86_64, Lean 4.33.1, Node 22.22.0
(`tests/stack/run.sh --canary`, 512 KB):

| run | native canary | wasm canary (`--stack-size=512`) | wasm (Node default) | suite |
|---|---|---|---|---|
| before (core 4b5892b0) | `xml-entities` overflows (expected failure, 673) | overflows (expected failure) | overflows (expected failure) | 29 pass, 0 fail (out of 29) |
| after (scanRefsLoop) | `xml-entities` runs | runs, 89 ms | runs, 155 ms | 37 pass, 0 fail (out of 37) |

The 37 include two new cases, `xml-entities-attr` (10,000 references in one
attribute value) and `xml-entities-dtd` (an entity value of 10,000
character references and an attribute default of 10,000 entity
references), in each of the four routes, and the native control. The
remaining expected failures are the three `turtle-collection` rows
(https://github.com/danbri/factoidal/issues/678).

Thresholds of the reference run, measured with ten document shapes (general,
decimal, hexadecimal and `&amp;` references in content; general and decimal
references in an attribute value; DTD entity values and an ATTLIST default):

| shape | before, native 512 KB | before, wasm `--stack-size=512` | after, both |
|---|---|---|---|
| content and attribute value | 5,000 runs, 10,000 overflows | 1,000 runs, 5,000 overflows | 100,000 runs |
| DTD entity value, ATTLIST default | 10,000 runs | 10,000 runs | 100,000 runs |

Natively at `LEAN_STACK_SIZE_KB=256`, 400,000 references ran in 768 ms
(content) and 815 ms (attribute value).

What stayed recursive, with its bound (repaired 2026-10-12: the section on
nested entity expansion above):
the NESTED expansion of an entity
whose replacement text references another entity (`expandEntityValue` for
text and attribute values, the markup re-parse of `parseChildren`) costs
one frame per level. The depth is at most the number of declared general
entities, because WFC: No Recursion rejects a cycle (a self-referencing
entity is rejected at 512 KB without overflow). Measured 2026-10-10 with a
chain `e0` -> `e1` -> ... -> `eK`: natively at 512 KB, text and attribute
chains of 3,000 run and 10,000 overflow; a markup chain (`<b>&eN;</b>`) of
1,000 runs and 3,000 overflows. In wasm, a text chain of 3,000 runs under
`--stack-size=512`; a markup chain of 1,000 overflows there and runs on the
default Node stack, and 3,000 overflows on both.

Two traps of the day:

- **`prlimit --as` stops the wasm routes.** Under `prlimit --as=8000000000`
  every wasm case failed with `WebAssembly.instantiate(): Out of memory:
  Cannot allocate Wasm memory for new instance`: V8 reserves the wasm
  memory's address range (with guard regions) up front, so an address-space
  cap refuses it while the resident memory is small. Cap native runs with
  `prlimit --as`; run the Node routes without it.
- **The audit had the old shape in class `counter`**, which `--gate` does not
  check: the signature names `Chars`, an `abbrev` of `Array Char`, which the
  textual length match does not resolve, and the `Nat` fuel then decides the
  class. The fuel was the length of the scanned range, so the depth was the
  input length (https://github.com/danbri/factoidal/issues/750).

## Two list readers in one mutual block: an append and a frame per group (https://github.com/danbri/factoidal/issues/754, 2026-10-10)

`Syntax/Turtle.lean` read [8] `objectList` and [7] `predicateObjectList`
inside the `readObject` mutual block with two different defects, which the
audit triage of issue 750 had listed as one `(a) PENDING` line and two
`UNTRIAGED` lines:

- **Time.** `readObjectList` (F\* `parse_object_list_rev`) built its result
  with `acc ++ ...`, so one object list of n objects took time in
  proportion to n². The stack was flat; only the scaling row could see it.
- **Stack.** `readPredicateObjectList` and `readPredicateObjectListMore`
  (F\* `parse_trailing_semicolons_rev`) called each other once per `;` group,
  so one statement of n predicates took n frames.

The expected failures were committed first, each naming the issue: the
`tests/stack` case `turtle-predicates` (one statement of 10,000 `;` groups)
and the `lean_scaling.py` row `turtle-object-list` (25,000 against 100,000
objects). Both failed as expected before the repair.

The repair, and the pattern for this shape:

- **An object list: a reversed accumulator carried THROUGH the caller.**
  `readObjectListRev` pushes each object's triples onto a newest-first list
  (`List.reverseAux`) and reads the next object by a tail call. The caller
  passes its own reversed list in, so all triples of one statement go onto
  ONE list, which is reversed once at the statement's end.
- **Two mutually recursive functions become one function with a flag.**
  A call from `readPredicateObjectList` to `readPredicateObjectListMore` and
  back is a tail call in the source, but Lean compiles only a SELF tail
  call to `goto _start`; a tail call to a different function of the block
  is a real C call. One function `readPredicateObjectList ... (accRev :=
  []) (more := false)` covers both: `more` says whether the input stands at
  a verb or at a run of `;`. The flag also keeps the old fuel-0 behaviour of
  the `More` function (accept, read nothing). The defaults keep every caller
  (`readStatement`, `readObject`, `readAnnotations`, TriG) unchanged.
- **Check the emitted C.** `readObjectListRev` has one `goto _start;`,
  `readPredicateObjectList` four, and neither has a self-call left.
- **The readable forms move after the block, with theorems.**
  `readObjectList` (the `acc ++` form) and the mutual pair
  `readPredicateObjectListSpec`/`readPredicateObjectListMoreSpec` keep the
  F\* shape. `readObjectListRev_eq` and `readPredicateObjectList_eq` prove
  the loops equal to them for every fuel, errors and positions included,
  with the same state, so the blank-node labels are the same. Three
  `@[csimp]` theorems make a call of a readable form run the loop. Axioms:
  `propext`, `Classical.choice`, `Quot.sound` only.
- **Measure the output, not only the stack.** `l4factoidal parse --out
  nquads`, strict and `--lenient`, on the 1,022 `.ttl` and `.trig` files of
  the W3C RDF 1.1 and 1.2 suites, against the binary from before (stdout,
  stderr and exit code): 2,044 of 2,044 identical. The 239 RDF 1.2 files
  again with `--format turtle12` and `trig12`, which is the only mode that
  reads annotations: 478 of 478 identical. With `turtle` and `trig` only 51
  of the 239 parse, so a comparison in the 1.1 mode alone does not test the
  annotation path of `readObjectListRev`.

Measured, linux x86_64, Lean 4.33.1, Node 22.22.0 (before 2026-10-10, after
2026-10-12):

| | before (13ff0a9d) | after |
|---|---|---|
| `turtle-object-list`, 25,000 objects | 10.33 s | 0.058 s |
| `turtle-object-list`, 100,000 objects | no result in 120 s (expected failure) | 0.403 s, row passes (ratio 6.9, bound 9.0) |
| `turtle-predicates`, native 512 KB canary | overflow (expected failure) | runs |
| `turtle-predicates`, Node `--stack-size=512` | overflow (expected failure) | 264 ms |
| `turtle-predicates`, Node default stack | overflow (expected failure) | 282 ms |
| `tests/stack/run.sh --canary` | 41 pass, 0 fail (out of 41), 3 expected failures | 41 pass, 0 fail (out of 41), none |

The wasm "after" column is a module rebuilt from this tree; the "before"
column is the `web` build set of 1b06a9c8, whose `Syntax/` is the same as
13ff0a9d.

**A loop for one dimension cost the other dimension 16 bytes a level.**
Nesting of `[ ... ]` and `( ... )` stays recursive through `readObject`,
bounded by the document's nesting. The `readObject` frame grew from
`sub $0x38,%rsp` to `sub $0x48,%rsp`: its call to `readPredicateObjectList`
now has seven arguments, and on x86-64 the seventh goes on the stack. At
512 KB, nested collections ran at 2,890 levels before and 2,695 after
(overflow at 2,902 and 2,707); `ex:s ex:p [ ex:p [ ... 1 ] ] .` ran at
1,501 levels before and after (overflow at 1,507). Rule: after a change to
any function of a mutual cycle, measure the nesting bound again, and
write the new number in the allow-list line.

## A filter per call and a list issuer, under a row that passed (https://github.com/danbri/factoidal/issues/751, 2026-10-13)

After the repair of https://github.com/danbri/factoidal/issues/745 the row
`rdfc-bnode-unique` of `tests/stack/lean_scaling.py` passed: every blank node
of that input has its own first-degree hash, so RDFC-1.0 §4.4 step 5 has no
collision group and never runs Hash N-Degree Quads (§4.7). The row
`rdfc-bnode-collide` (`_:p{i} rdf:type ex:Person`, one shared hash) sends
every blank node through §4.7, and it was quadratic: two costs that the
first row could not reach.

- `hndqRun` gave `buildBucketsFor` every quad of the dataset, and
  `buildBucketsFor` tested each one, once per call.
- The issuer kept its identifiers in a list: a scan per lookup and
  `issued ++ [x]` per new identifier, in the §4.4 step 5.3 replay and in
  `filterUnissued` and `exploreMembers`.

The repair is a twin chain from the caller that sees every key
(`buildCanonicalMappingBudgetedFast`, which builds the §4.4 step 2 map once)
down to `hndqRunF`, with an issuer type `FIssuer` that holds the list as
`front ++ backRev.reverse` and a search tree whose agreement with the list is
a field of the structure. One `csimp` theorem on the top function,
`buildCanonicalMappingBudgeted_eq_fast`, reaches every caller. Record and
proofs: `docs/designissues/2026-10-10-npm-lean-only.md` § 10, "Issue 751".

The ladder, `l4factoidal canonicalize FILE --format nquads`, user CPU
seconds and peak resident memory (before: one run per point; after and the
references: minimum of 3 runs, rdf-canonize at 64,000 one run), beside two
RDFC-1.0 implementations on the same files and machine (the canonical output
of all three is byte-identical at every size):

| blank nodes | Lean before | Lean after | Oxigraph (pyoxigraph 0.5.11) | rdf-canonize 5.0.0 (Node 22.22.0) |
|---:|---:|---:|---:|---:|
| 2,000 | 0.16 s, 24 MB | 0.07 s, 26 MB | 0.02 s, 27 MB | 0.14 s, 66 MB |
| 4,000 | 0.59 s, 33 MB | 0.14 s, 33 MB | 0.05 s, 32 MB | 0.26 s, 75 MB |
| 8,000 | 2.66 s, 45 MB | 0.27 s, 47 MB | 0.09 s, 41 MB | 0.64 s, 87 MB |
| 16,000 | 10.83 s, 70 MB | 0.54 s, 70 MB | 0.19 s, 59 MB | 2.02 s, 115 MB |
| 64,000 | 327.67 s, 222 MB | 2.66 s, 222 MB | 0.96 s, 167 MB | 37.80 s, 197 MB |

Rules from this repair:

- **One row per path through the algorithm, not one row per function.** A
  canonicalizer has a cheap path (unique hashes) and an expensive one
  (collision groups). A scaling row on the cheap path passes while the
  expensive path is quadratic.
- **A reference implementation can be quadratic too.** rdf-canonize 5.0.0
  takes 2.02 s at 16,000 and 37.8 s at 64,000 blank nodes on this shape (19
  times for 4 times the input). Put each reference on the same ladder; do
  not take one size as the measure of state of the art.

## Twenty-six PENDING lines removed (https://github.com/danbri/factoidal/issues/752, 2026-10-13)

The audit repair of https://github.com/danbri/factoidal/issues/750 put 26
declarations on the allow list as `(a) PENDING`: each recursed once per
item, or once per unit of a value, of data. 25 left issue 752 (OKR batch 1
KR 2.6, https://github.com/danbri/factoidal/issues/768): 20 by conversion
with a proved equality, 2 by reclassification with the bound on the line,
and 3 stay `(a) PENDING` under a new issue with an expected failure. The
26th, COTTAS `namedGraphsAux`, stays `(a) PENDING` under issue 752 and is
not converted: owner, 2026-10-11, verbatim, "All work on cottas is
suspended" (CLAUDE.md). A conversion landed on the branch first and was
reverted, because the task list named it by mistake.

| family | declarations | new form | theorem |
|---|---|---|---|
| 10^n | `pow10` of Geo.Scaled, Math.Sigmoid, SPARQL, XPath.Num, XSD | the core `10 ^ n`: `Nat.pow` is one `lean_nat_pow` (GMP) call, and `Int.pow` of a non-negative base is `Nat.pow` | `pow10_eq_pow : pow10 n = 10 ^ n` by induction (`Nat.pow_succ` or `Int.pow_succ`, then `mul_comm`); `@[csimp] pow10_eq_fast` |
| x^n | MathML `powNat` | a loop that applies `mulRat x` to an accumulator k times | `powNatLoop_mulRat` (one step commutes with the loop), then `powNatLoop_eq`; no algebra of `mulRat` |
| digit counts | SPARQL `countDigitsFuel`, XSD `natDigits.go`, Geo WKT `takeDigits`, VC `natToBytesBE` | an accumulator loop | `loop … k = k + spec …` (`fun_induction` on the loop); `takeDigits` keeps value and count (`v * 10^n + vr`) and computes no power per digit; `natToBytesBE` puts the low byte on the front (`loop n acc = spec n ++ acc`), no append per byte |
| list walks | RDF `Graph.dedup`, SPARQL `dedupPath`, `fn:replace` `replaceLoop`, XMLLiteral `XmlCanon.walk`, JSON-LD `replaceFirst`, SHACL `distinctDups`, XML `validate.countList` | a newest-first accumulator reversed once; a block of output goes on with `List.reverseAux` | `loop l acc = acc.reverse ++ spec l`; `Graph.dedup` is `foldr step []`, and `List.foldl_reverse` makes it a left fold over the reversed list, with no new loop |
| collections in a `mutual` block | SPARQL `pCollection`, RDF/XML `collectionList`, XMLLiteral `serializeNodes` | the pattern of issue 678: the cells go on a newest-first list by tail calls, then a fold links them | the readable form moves after the block, `cells_eq` states the loop with the earlier cells linked in front |
| reclassified | Turtle `assignLabelsAvoiding` | (c): the label index runs 1 to 9 and stops | |
| reclassified | Regex `memStar` | (s), a new marker: specification only; no function of the emitted C outside its own module and its theorem module calls it | |
| open | Regex `cmatch`; RDFC-1.0 `hndqRun`, `hndqRunF` | expected failures `regex-replace-groups` (https://github.com/danbri/factoidal/issues/816) and `rdfc-bnode-chain` (https://github.com/danbri/factoidal/issues/817) in `tests/stack/run.sh` | |

Rules from this work:

- **A `csimp` on a `let rec` or `where` helper does not reach the definition
  that holds it.** The holder is compiled together with the helper, before
  the theorem exists, so its C still calls the helper. Put the `csimp` on the
  holder (`natDigits_eq_fast`, `validate_eq_fast`), or make the helper a
  top-level function that is defined and replaced before its caller
  (`FState.replaceFirstMatch`, `distinctDupsBy`).
- **A `mutual` pair that csimp cannot enter can be replaced from outside.**
  Define a twin pair after the readable pair, prove both members equal by
  induction on the fuel (one theorem with a conjunction), and put `csimp` on
  BOTH readable members (`serializeNode_eq_fast`, `serializeNodes_eq_fast`).
  Callers outside the pair then run the twin, and the audit marks both
  readable members `replaced`.
- **A loop over siblings still recurses per nesting level.** The twins of
  `validate.countElements` and of `serializeNodes` form a two-member cycle
  whose sibling step is a `goto _start`; the cycle is a `(b)` line (element
  nesting), and the line says so.
- **Measure the old limit before choosing a case size.** Under
  `LEAN_STACK_SIZE_KB=512`, natively, on base 7d314f43: an RDF/XML
  collection ran at 2,000 members and overflowed at 5,000; a SPARQL
  `INSERT DATA` collection the same; `REPLACE` over one literal ran at
  5,000 characters and overflowed at 20,000. An XMLLiteral with 9,000
  siblings in one element ran, because the frames are small, so that
  family has no case above the old limit (the 10,000 fuel caps it).
- **After a repair, run the case in every route: the next frame per item
  shows in the route with the largest frames.** With the SPARQL collection
  reader a loop, `INSERT DATA` with 8,000 members ran natively at 512 KB and
  256 KB, and overflowed in Node under `--stack-size=512`: gdb at 128 KB
  named `collectQuads`, which walks the join chain the desugaring builds,
  one join per member. Its allow-list line (first baseline, no reason) now
  names https://github.com/danbri/factoidal/issues/818, and the case is an
  expected failure in the wasm canary route only. `xfail_issue` takes the
  route as `$2`: `regex-replace-groups` runs on the default Node stack, so
  it is an expected failure in `canary` and `wcanary` only; an entry for all
  three routes turned the suite red with "UNEXPECTED PASS".
- **A fuel cap on data is a shortfall too, and needs its own expected
  failure.** https://github.com/danbri/factoidal/issues/818 records two
  constant fuels of 10,000 that the loops above made visible: a SPARQL
  collection of 10,001 members is a parse error, and an XMLLiteral element
  with 10,001 children loses its last children with no error. The
  tests/stack table counts stack overflows only, so these are `xfail` cases
  of `Wasm/native-smoke.sh` (`checkx`, through `xverdict`; each checks the
  correct result and has a 100-item control that passes), and the
  quadratic cell names are the `lean_scaling.py` row
  `sparql-collection-parse` in `XFAIL`.
- **Two recursions found here are also quadratic.** `cmatch` keeps every
  prefix outcome (1,000, 2,000, 4,000 repetitions: 36, 86, 274 MB), and a
  chain of blank nodes that share one first-degree hash makes RDFC-1.0
  §4.4 explore every member (300, 600, 900 nodes: 7.7, 30.9, 49.6 s).
  A loop does not repair either; each issue says so.

## Three scaling expected failures removed (OKR batch 1 KR 2.5, 2026-10-13)

### The SPARQL tokenizer took three length walks per token (https://github.com/danbri/factoidal/issues/802)

`tokenizeLoop` tested progress with `rest.length ≥ cs.length`, and `skipWs`
seeded its fuel with `cs.length + 1`: three walks over the rest of the request
per token. The repair (`formal/lean4/L4Factoidal/SPARQL/Tokenizer.lean`) keeps
both readable definitions. `skipWsLoop` scans whitespace and comments with a
flag and no fuel (`skipWs_eq_fast`, a `csimp` placed before `nextToken`, so
the compiled `nextToken` calls it). `nextToken_len` proves that one token moves
the position by the characters it consumes, or uses up the input; so the
length test is the F* test `pos' ≤ pos` (`nextToken_progress`), and
`tokenizeLoopFast` with that test is `tokenizeLoop` (`tokenizeLoop_eq_fast`,
`csimp` on `tokenize`, `tokenize12` and `tokenizeAt`).

| `l4factoidal`, one run per point | 1,000 | 2,000 | 4,000 | 8,000 |
|---|---:|---:|---:|---:|
| `update` INSERT DATA, n triples, before | 0.76 s | 3.27 s | 13.25 s | 89.4 s |
| the same, after | 0.11 s | 0.16 s | 0.51 s | 2.27 s |
| `query` ASK with VALUES of n IRIs, before (CPU) | | 0.52 s | 1.92 s | 6.97 s |
| the same, after (CPU, minimum of 3) | | 0.017 s | 0.024 s | 0.062 s |
| `l4sbm11 update`, SBM11 store of 600,001 quads | | | DELETE DATA 0.49 s | INSERT DATA 1.60 s |

The update row is still quadratic after the repair, from a second cost:
the parser appends each triple to the end of the block's BGP list
(`ggpAddTriple`, `.bgp (ts ++ [tp])`). It is the `lean_scaling.py` row
`sparql-update-insert`, an expected failure naming
https://github.com/danbri/factoidal/issues/821. The tokenizer row is
`sparql-tokenize`. The `tests/stack` case `sbm11-delta` now sends 4,000 and
8,000 quads (it sent 1,000 and 2,000 because of this cost).

Rules from this repair:

- **A length in a loop's guard is a walk per iteration.** `rest.length ≥
  cs.length` reads as a comparison and costs two list walks. Compare positions
  or counters that the loop already carries, and prove them equal to the
  readable test.
- **A fixed fuel can stop a row before it shows its curve.** At 16,000 VALUES
  the row failed with "recursion limit" (the constant 10,000 of
  https://github.com/danbri/factoidal/issues/818), not with a time. Choose the
  sizes below such a limit, or repair the limit first.
- **Make the per-item cost large enough to see.** With integers in the VALUES
  block the base tokenizer gave ratios of 2.8 and 3.2 per doubling, 9.1 for
  4x: a pass or a fail by noise. With 40-character IRIs it gave 3.7 and 3.6,
  13.4 for 4x.

### Four limits of one issue (https://github.com/danbri/factoidal/issues/818)

1. **The constant fuel 10,000 of the SPARQL parser.** Every sibling loop of
   the parser (collection members, the triples of a block, VALUES values)
   spends one unit per sibling. `parseSparql` and `parseSparqlUpdate` now
   parse once at `topFuel` and, when that pass rejects the request, once more
   at `scaledFuel` (`topFuel` + the request length). There is no theorem that
   more fuel gives the same answer (the parser is one mutual block of about
   100 functions, and some of them return a partial result when the fuel runs
   out), so the design makes the needed facts true by construction:
   `parseSparql_of_topFuel` (an answer of the first pass is the answer),
   `parseSparql_error` (a rejection is the first pass's rejection, with its
   message) and `parseSparql_ok` (every answer is an answer of
   `parseSparqlWith` at some fuel, so the theorems stated at every fuel hold);
   the same three for updates.
2. **`freshBnodeId` walked the rest of the token list once per cell.** The
   label is now the character offset of the token (`_:bnode_30`, where the F*
   and this port gave the remaining token count, `_:bnode_5`). The offsets
   increase along a token list (`#guard`s in `Tokenizer.lean`), so the labels
   stay distinct; three SSE snapshot guards in `ParserTests.lean` changed
   their label numbers.
3. **XMLLiteral children were cut after about 10,000, with no error.**
   `serializeNodeT`/`serializeNodesT` recurse on the node and the child list
   and have no fuel; `serialize_fuel_eq` proves them equal to the fuelled pair
   whenever the fuel covers `litNeed` of the node, so
   `serializeLiteralContent_eq_fuel` gives the old lexical form wherever the
   old one was complete. The loop twin is `serializeNodeTF`/`serializeNodesTLoop`.
4. **`collectQuads` used one native frame per join.** `collectQuadsLoop` keeps a
   work list (termination: twice the `sizeOf` of each pattern plus one, summed);
   `collectQuadsLoop_eq`, `csimp collectQuads_eq_fast`. The `tests/stack` case
   `sparql-collection` still overflows in the wasm canary route (Node,
   `--stack-size=512`): the next frame per member is `ggpLabeledBnodes`, the
   INSERT DATA blank node label check (gdb: native runs at 128 KB, overflows at
   64 KB). The case stayed an expected failure in that route under issue 818
   until `ggpLabeledBnodes` became a loop (section "The last three scaling
   expected failures of KR 2.5" below).

| `l4factoidal`, one run per point | before | after |
|---|---|---|
| `query` ASK, VALUES of 16,000 IRIs | parse error after 33.6 s | 0.13 s |
| the same, 32,000 IRIs | no answer in 200 s | 0.39 s |
| `query` SELECT, one collection of 10,001 / 20,000 / 40,000 members | parse error after 1.37 / 6.51 / 27.6 s | 0.44 / 2.03 / 8.80 s |
| `update` INSERT DATA, one collection of 10,001 / 20,000 / 40,000 members | parse error after 1.46 / 6.62 / 27.6 s | 6.02 / 25.0 / 132 s |
| `parse` RDF/XML, an XMLLiteral element with 10,001 / 40,000 children | 0.19 / 0.09 s, last children cut | 0.14 / 0.22 s, complete |

The two "after" rows that grow as n² are other costs, each with an issue and
an expected-failure row: the §19.6 blank node scope check walks the join chain
once per join (https://github.com/danbri/factoidal/issues/824, row
`sparql-collection-scope`), and `Dataset.insertQuads` scans the graph for each
new quad (https://github.com/danbri/factoidal/issues/821, row
`sparql-update-insert`).

Rules from this repair:

- **A repair that makes an input pass shows the next cost on that input.** The
  expected-failure checks of issue 818 tested the answer; the scaling row at
  2,000 and 8,000 members passed (ratio 6.9). At 40,000 members the same query
  took 8.8 s. Measure a repaired path at sizes past the old limit, not only at
  the sizes the old limit allowed.
- **When a monotonicity theorem is out of reach, make the extension
  conservative by construction.** A second pass that runs only on a rejection,
  and keeps the first rejection when it also fails, changes no answer the old
  code gave; the three theorems are a few lines each.

### The anonymous individual graph of the OWL 2 species check (https://github.com/danbri/factoidal/issues/812)

`componentsOf` (`L4Factoidal/OWL/SyntaxDL.lean`, Structural Specification
§11.2) adds one edge at a time to a list of components and looks for the
component of each end with `List.find?` over the whole list. The repair is
`componentsOfLoop`, which carries the set of vertices already in a component,
with two fast paths, each an exact equality with `addEdge`:

- neither end is in a component: no component contains either end
  (`find?_none_of_not_covered`), so the edge is a new two-vertex component
  without a scan;
- one end is the first vertex of the first component and the other end is in
  no component (one step along a chain, in either direction): the components
  are pairwise disjoint (`addEdge_disj`, proved for every step), so the first
  component is the only one equal to itself and `filter` returns the rest
  unchanged (`addEdge_head_left`, `addEdge_head_right`).

`addEdge_covered` states which vertices one step covers; `addEdgeSeen_eq` and
`componentsOfLoop_eq` carry the covered set and disjointness through the loop;
`componentsOf_eq_fast` (`csimp`) gives the same components in the same order,
so the verdict `anonymous-individuals-not-a-forest` and the number of
`anonymous-individual-tree-without-leaf` are unchanged for every input. Other
edges (a merge of two components, or an edge whose covered end is not first)
still scan the list.

| `l4owl-species`, minimum of 3 runs | 8,000 | 32,000 |
|---|---:|---:|
| n pairs `_:x p _:y`, before (one run) | 1.03 s | 15.71 s |
| the same, after the first fast path | 0.34 s | 1.57 s |
| one chain of n blank nodes, before (one run) | 0.49 s | 9.18 s |
| the same, after the first fast path (one run) | 0.61 s | 13.67 s |
| the same, after the second fast path | 0.22 s | 0.81 s |

Rules from this repair:

- **A fast path that is exact needs only the facts of its own case.** The
  first fast path needed one invariant (which vertices are covered) and made
  the pairs row linear; the chain row stayed quadratic and was measured as
  such before the second fast path, which needed one more invariant
  (disjointness). Each fast path is an equality with `addEdge`, so nothing
  downstream changed.
- **Add a row for each shape of the data structure, not only the shape in
  the issue.** The issue's row was disjoint pairs; a chain exercises the
  other branch of `addEdge`, and passed the first repair's gate unnoticed
  until it had its own row.

## The last three scaling expected failures of KR 2.5 (2026-10-13)

`tests/stack/lean_scaling.sh` went from 4 expected failures to 1
(`query-memory-fstar`, https://github.com/danbri/factoidal/issues/729).
Each repair keeps the readable definition and adds a proved equality
(`csimp`, or a theorem the parser's callers use). Standard axioms only.

### INSERT DATA (https://github.com/danbri/factoidal/issues/821)

Four costs, each found after the one before it was repaired:

1. **The parser appended each triple to the end of the BGP list.** The four
   triples-block functions of the grammar block now carry a `TriplesAcc`: the
   pattern and the triple patterns added since, newest first. `flushTriples`
   is the pattern it stands for (`ggpAddTriple` of each, oldest first) and
   runs as one append (`flushTriples_eq_fast`). The readable functions are in
   `SPARQL/TriplesBlockRef.lean` (the `pCollection` pattern: defined after
   the grammar block, calling it); `pTriplesBlock_eq_ref` and the three
   theorems before it prove that the parser computes them.
2. **`Dataset.insertQuads` scanned and copied the graph per quad.**
   `RDF/GraphIndex.lean`: a `GraphIx` holds the graph as `base ++
   rev.reverse` and a `Std.HashSet` of the KEYS of its triples. `Graph.mem`
   compares with `Triple.eqb` (tags case-insensitively, XMLLiterals by
   canonical form), so the key is the triple with `Term.joinKey` in the object
   position, and `Triple.eqb_iff_key` proves that equal keys are exactly
   `eqb`-equal triples. A graph slot makes its set on the SECOND add, so one
   insert into a large graph costs what it cost before.
   `insertQuads_eq_fast`: same dataset, same graph and triple order.
3. **`bnodesInBgp` used one native frame per triple and scanned a list per
   label.** An INSERT DATA block of 40,000 triples overflowed the 512 KB
   canary stack. `bnodesInBgp_eq_fast`: a `foldr` (compiled as
   `List.foldrTR`, over an array) with a set beside the label list, the same
   list. Native now runs 40,000 triples at 64 KB.
4. **The label check across data operations scanned a list per label.**
   `bnodeLabelsUnique_eq_fast`: the verdict depends on the labels only
   through membership, so a set gives the same Bool.

| `l4factoidal update`, empty dataset | before | after |
|---|---:|---:|
| INSERT DATA, 2,000 / 8,000 triples (row `sparql-update-insert`, min of 3) | 0.139 / 1.920 s | 0.032 / 0.105 s |
| INSERT DATA, 4,000 / 16,000 triples with blank-node subjects (before: one run; after: row `sparql-update-insert-bnodes`, min of 3) | 0.17 / 2.00 s | 0.049 / 0.257 s |
| INSERT DATA, one collection of 10,001 / 40,000 members (one run) | 6.02 / 132 s | 0.34 / 1.08 s |

The blank-node shape has its own row, `sparql-update-insert-bnodes`: the
first two repairs left it quadratic (0.09 s and 1.37 s), and the IRI row did
not show it.

### The merge of the browser update log (https://github.com/danbri/factoidal/issues/822)

`BrowserLog.applyBatchesFast` carries a `DatasetIx` (the index of item 2
above, for every graph of the dataset) through all the batches, so the index
is made once per merge, not once per batch: a log of one triple per record
would otherwise remake it for every record. An add entry is
`DatasetIx.insertQuad`; any other entry is `applyEntry` on the dataset the
index holds. `applyBatches_eq_fast` (`csimp`), so `merge` runs it and the
theorems of `BrowserLogTheorems.lean` hold for it.

| `deltaLogMerge`, records of one triple (CPU, min of 3) | 8,000 | 16,000 | 32,000 |
|---|---:|---:|---:|
| before | 1.33 s | 4.53 s | 17.23 s |
| after | 0.36 s | 0.81 s | 1.80 s |

### The §19.6 scope check and the labeled blank nodes (https://github.com/danbri/factoidal/issues/824, https://github.com/danbri/factoidal/issues/818)

`validateBnodeScope` called `preservesBgpScope` on both sides of each join
(a walk of the side), and both it and `ggpLabeledBnodes` used one native frame
per join of a collection's chain. `scopeLoop` and `labelsLoop` run over a work
list of steps (visit a pattern, or combine the two answers on top of a value
stack). The proof needs no induction over the mutual pattern type:
`fun_induction` over the loop, with the meaning of each step stated as a
function of the value stack (`scopeStepSem`, `labelStepSem`), and one lemma
per constructor that states the recursive definition's equation in that form
(`scope_join` and the others). Termination: three times the `sizeOf` of each
pattern to visit plus one, summed.

| `l4factoidal query`, one collection of n members (min of 3) | 10,000 | 40,000 |
|---|---:|---:|
| before | 0.440 s | 9.053 s |
| after | 0.061 s | 0.164 s |

INSERT DATA with one collection of 8,000 members: native overflowed at
64 KB in `ggpLabeledBnodes`; it now runs at 64 KB.

Rules from these repairs:

- **A `Std.HashSet` in a structure updates in place only when the structure
  is taken apart by a match.** `GraphIx.add` and `DatasetIx.insertQuad` match
  on the constructor; `{ x with keys := x.keys.insert k }` keeps `x` alive
  during the insert and copies the set.
- **A per-batch index is still quadratic when the batches are small.** Carry
  the index through the outer fold (`applyBatchesFast`), not only through
  one call of the inner one.
- **A set may replace a list where the result is a verdict.** The label
  checks of §19.6 read their lists only through membership, so a set gives the
  same Bool; where a list is returned, keep the list and put the set beside
  it (`strUnionSet`).
