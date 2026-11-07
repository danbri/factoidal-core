# VerifiedJS for foafnaut page scripts: measured results

Owner, 2026-11-07, verbatim: "We should move to VerifiedJS for JS. And get it
wired up via DOM. Behaviour in pages needs to be JS." and "VerifiedJS: implement
now, I will talk to them, we can always back out."

Result: VerifiedJS at the pin cannot run the script fixtures, so the `document`
binding was not added. QuickJS stays the only engine. Stage 1 and stage 2 are
complete. Stage 3 stopped; section 4 gives the reason. Stage 4 did not start.
Tracking: https://github.com/danbri/factoidal/issues/1252.

The acceptance gate is in the section "VerifiedJS assessment" of
[the architecture decision](2026-11-03-script-engine-architecture.md).

## 1. What was measured, and where

Pin: [`b6eabd76`](https://github.com/BasisResearch/VerifiedJS/commit/b6eabd76a1eab6573c0d422db8142869133eabb4)
(2 April 2026). The repository has no licence, so this repository holds no
VerifiedJS source, generated code or binary.
`labs/demos/foafnaut/web-render/script-engine/verifiedjs/fetch-verifiedjs.mjs`
fetches the pin into the ignored `.build/verifiedjs/` and checks the commit and
a SHA-256 of the tree.

The Lean builds ran on GitHub runners (4 vCPU), because the owner's laptop takes
no Lean build artifacts. `.github/workflows/verifiedjs-probe.yml` runs on the
branch `wip/verifiedjs-page-scripts` only. A run uploads text reports only.

- https://github.com/danbri/factoidal-core/actions/runs/42318218843 (cold build,
  upstream end-to-end suite, Test262, full build)
- https://github.com/danbri/factoidal-core/actions/runs/42319450564 (probe with
  raw output comparison, axioms of each pass theorem)
- https://github.com/danbri/factoidal-core/actions/runs/42320494877 (final probe:
  the expected-fail gate is green; unit tests)

## 2. Stage 1: build

| Item | Result |
| --- | --- |
| Toolchain | Lean 4.29.0-rc6, 15.7 s to install, 2.7 GB under `~/.elan` |
| `lake build verifiedjs` (cold, with dependency clones) | Passes: 101.5 s, peak RSS 1.36 GB, `.lake` 902 MB, binary 149.9 MB |
| `lake build` (default target, all proofs) | **Fails** after 428 s, peak RSS 2.29 GB |
| Upstream end-to-end suite (`scripts/run_e2e.sh`) | 175 pass, 28 fail (out of 203) |
| Upstream unit tests (`lake build Tests`) | **Fails**: 4 checks in `tests/unit/Tests/ParserTests.lean` (lines 339, 361, 385, 397) |

The full build fails in `VerifiedJS.Proofs.ClosureConvertCorrect` at line 6227:
`unexpected token '('; expected '}'`. `VerifiedJS.Proofs.EndToEnd` imports that
module, so at the pin **`flat_to_wasm_correct` is not type-checked**.

The lakefile requires Mathlib and the build clones it, but no file under
`VerifiedJS/`, `tests/unit/` or `tools/` names Mathlib. The compiler build needs
no Mathlib cache. The 2026-11-03 record says "requires Mathlib"; that is true of
the lakefile only.

Test262, the whole suite at the submodule pin, through the upstream harness
`scripts/run_test262_compare.sh`, with 20 s and 10 s limits added around each
compile and run, in 12 shards. The harness labels are: 78 pass, 883 fail, 45,227
xfail, 4,546 skip (out of 50,734). All 45,227 xfail cases have the label
`known-backend:wasm-validation`: the compiled module is not valid Wasm, so the
test did not run. Read as run and passed: **78 pass, 50,110 fail, 4,546 not run
(out of 50,734)**.

Two limits apply to the 78:

- The harness puts a prelude before each test, and the prelude has `try`/`catch`.
  The compiler emits invalid Wasm for `try`/`catch` (section 3; probe case
  `try-in-function`). This is the likely cause of the 45,227; I did not run each
  case to confirm it.
- The harness counts a negative test as a pass when compilation fails for any
  reason, and counts a positive test as a pass when the module prints nothing and
  exits 0. Of the 78 names, 51 contain `invalid` or `negative`.

The number therefore says little about language conformance in either direction.

## 3. Stage 2: fixtures outside the browser

`verifiedjs/fixtures.mjs` holds the 9 script sources of `session.test.mjs`,
`lean-dom.test.mjs` and `fixtures/scripted.html`, with `document` given by a small
ES5 stand-in written in the script itself. It also holds 42 single-feature cases
and the 9 sources with no stand-in. `verifiedjs/probe.mjs` runs each one at each
level and compares standard output with Node.

| Level | 9 fixtures | 42 feature cases |
| --- | --- | --- |
| Compiled Wasm under wasmtime | 0 same, 9 not | 10 same, 32 not |
| Core interpreter | 1 same, 8 not | 28 same, 14 not |
| Flat interpreter | 0 same, 9 not | 20 same, 22 not |
| ANF interpreter | 0 same, 9 not | 0 same, 42 not |

All sources parse and compile. The one Core pass, `lean-dom-named-error`, is an
accident: `Object` and `Error` are unbound, each use logs a ReferenceError, and
evaluation continues to the final line. The ANF interpreter printed no
`console.log` output for any case, so it cannot be compared.

Without the stand-in, every fixture fails: `document` is `undefined`.

Why the compiled Wasm fails, by feature (each is a probe case or a helper body in
`Wasm/Lower.lean` at the pin):

| Feature | Result | Cause |
| --- | --- | --- |
| Method call, callback | Trap: indirect call type mismatch (6 of 9 fixtures) | `call_indirect` takes its type from the argument count at the call site; not analysed further |
| `try`/`catch` | Module fails validation (3 of 9 fixtures) | Lowering leaves values on the stack at block end |
| `"Clicks: " + n` | Prints `undefined` | `__rt_binaryAdd` converts both sides to numbers |
| `'a' === 'a'` | `false` | Strings are not compared by content |
| Closure read and write | `undefined`, `0` | `__rt_getEnv` returns undefined; `__rt_makeEnv` returns a constant |
| Arrays | `undefined` | `__rt_arrayLit`, `__rt_getIndex` and `__rt_setIndex` are stubs |
| Uncaught throw | Exit 0, where Node exits 1 | `__rt_throw` returns undefined; a throw is a local branch or a return |
| Global lookup | `undefined` | `__rt_getGlobal` returns boxed undefined |
| 2,000 small objects | Trap: memory fault at 0x1003b, memory size 0x10000 | Bump allocation, no `memory.grow`, no collector |

The Core interpreter is the alternative to compiled Wasm, because it has fuel and
its string concatenation and arrays work. It also fails, and these failures
are in the Core semantics, which is the top of the proof chain:

| Case | Node | Core |
| --- | --- | --- |
| `var n=0; function f(){n=n+1} f(); f(); console.log(n)` | 2 | 0 |
| A counter closure from a factory, called twice | 2 | 1 |
| `o.f()` reading `this.n` | 3 | undefined |
| `console.log('a'); throw 1; console.log('b')` | `a` | `a`, `b` |
| `Error('stop').message`, `JSON`, `Object`, `globalThis` | Defined | ReferenceError logged, evaluation continues |

`FuncClosure.capturedEnv` holds a copy of the bindings, so a write in a closure
does not reach the outer variable. `fixtures/scripted.html` needs this write
(`++clicks` in a click listener). A preservation theorem for this Core gives a
guarantee about these results.

Two more interpreter results:

- `var n=7; function f(){return n;} console.log(f());` prints 7 at Core and
  `undefined` at Flat. `closureConvert_correct` says each Flat trace is a Core
  trace. I did not check that this program meets the hypotheses of that theorem.
  If it does, the statement is false for this program.
- The heap-growth case times out at 20 s at each interpreter level. Each step
  appends to the end of a list (`acc ++ [t]`).

## 4. Stage 3: why the binding stopped

A compiled module has this whole interface, measured in Node:

```text
imports: wasi_snapshot_preview1.fd_write
exports: main, _start, memory
```

- There is no import that returns a value. `getElementById` cannot get an answer
  from Lean. `__rt_getGlobal` has no host path.
- The function table is not exported. The host cannot call a listener.
- `main` runs the script again from the start. A click turn cannot keep state.

A `document` global therefore needs changes to VerifiedJS itself: new imports,
new exports and a global lookup. The click fixture also needs closure writes,
strings, `this`, arrays and exceptions, which do not work (section 3). A binding
in host JavaScript cannot supply them, and rule 36 forbids it to try. So no
`engine` setting was added: it would select an engine that fails every fixture.

The compiler must also run where the page runs, because a page's scripts are
known only at load time. It is a 149.9 MB native binary on Lean 4.29.0-rc6, and
our Lean Wasm build is on a later toolchain. Nobody has compiled it to Wasm.

## 5. Stage 4: the theorem for this path

Stage 4 did not run. The answer to "which theorem covers this path" is still
known. No theorem at the pin covers it:

- The end-to-end theorem `flat_to_wasm_correct` does not build (section 2). Its
  text starts from Core, not source. Its hypotheses exclude reachable `forIn` and
  `forOf`, and require `noCallFrameReturn`, `ExprAddrWF`, `ExprWellFormed`, and
  memory conditions.
- `#print axioms`, run 42319450564:
  - `anfConvert_correct`: `sorryAx`.
  - `lower_behavioral_correct`: 15 project axioms and 9 `native_decide` axioms.
    These include `lower_main_code_corr` and one axiom for each of the let, seq,
    if, while, tryCatch, labeled, yield, throw and await cases.
  - `emit_behavioral_correct`: 2 project axioms, for `call` and `call_indirect`.
  - `optimize_correct`: standard axioms only. The pass is the identity.
- Host calls, DOM effects and Lean arena commands are outside every theorem.

Interruption and memory, from the probes: compiled Wasm has no cooperative
interrupt, so only worker termination stops an infinite loop, and that is the
path `session.mjs` already has. A Wasm memory fault ends the instance. The
interpreters have a limit of 1,000,000 steps, but the loop case passed the 20 s
probe limit first.

## 6. What the owner can decide

Each option keeps QuickJS as the default until the gate passes.

1. **Wait for upstream.** Ask the authors for a licence and for the current state:
   the pin is seven months old, and the proof module does not build.
2. **Fork, after a licence exists.** The work is the host interface, the runtime
   (strings, closures, arrays, exceptions, property calls, allocation with
   growth), a change to Core closure semantics and `this`, a repair of the proofs
   that this change breaks, the standard library the fixtures use, and a Wasm
   build of the compiler. This is most of a JavaScript engine plus its proofs.
3. **Write a page-script engine in Lean here,** with semantics checked against
   Test262 and the DOM binding inside Lean. This needs no licence. See
   https://github.com/danbri/factoidal/issues/1203 (JSCert study).

## 7. How to back out

Nothing in the page path changed: `session.mjs`, `worker.mjs`, `guest.mjs` and
`WebRenderScript.lean` are as on `main`. To back out, delete
`labs/demos/foafnaut/web-render/script-engine/verifiedjs/`,
`.github/workflows/verifiedjs-probe.yml`, this record and its index lines, and
close https://github.com/danbri/factoidal/issues/1252.

## 8. Reproduction

```sh
node labs/demos/foafnaut/web-render/script-engine/verifiedjs/fetch-verifiedjs.mjs
```

Do not build on the laptop. Push to `wip/verifiedjs-page-scripts`: a change under
`script-engine/verifiedjs/` runs the build and the probe. Put `[test262]` or
`[proofs]` in the commit message to add those jobs. The probe exits 1 when a
fixture passes that the list `PASSING` in `fixtures.mjs` does not name, or when a
named fixture fails. The report is the artifact `compiler-report`.
