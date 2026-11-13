# Foafnaut safety map: which code can reach I/O

2026-11-13. Issue: https://github.com/danbri/factoidal-core/issues/427 (safety map of the
whole system: trust boundaries, I/O-free checks, escape-hatch inventory, metrics).

This record is step S1 of that issue. It also describes the tool of step S2,
`tools/safety-scan/`.

## 1. The question

Foafnaut is large (about 600,000 Lean lines in the modules the engine imports, plus about
16,000 lines of host TypeScript, Objective-C and C) and it changes fast, mostly by agent
commits. Two risks:

1. A design error: a part can do more than its authors intended. Example: a parser that
   can read a clock or a file.
2. An inserted fragment: a small change adds an effect or a leak, and review does not see
   it.

Review time is limited. The aim is to find the regions where a property of the code removes
these risks without review, and to make the remaining region small and visible.

## 2. The property that Lean gives

A Lean definition whose type contains no `IO`, `EIO`, `BaseIO`, `IO.RealWorld` or `IO.Ref`
cannot do I/O, unless the code that runs reaches an escape hatch:

| Hatch | Why it breaks the property |
| --- | --- |
| `@[extern]` in this project | C code runs; it can do anything |
| `@[implemented_by]` in this project, other than the copy that `partial def` makes | the code that runs is not the code that the kernel checked |
| `unsafe` definition written in source | can call `unsafeBaseIO`, `unsafeIO`, `unsafeCast` |
| `initialize` / `builtin_initialize` | runs an `IO` action when the module loads |
| core `dbgTrace`, `dbgTraceIfShared`, `dbgSleep`, `dbgStackTrace` | safe to name from pure code, and they write to standard error or sleep |

Lean refuses a safe definition that names an `unsafe` constant. So pure code can reach
`unsafeBaseIO` only through one of the first three rows. Lean's own `@[extern]` constants
(`Nat` arithmetic, `ByteArray`, `String`) are in the trusted base (section 5).

A module that has no effect in any type, and whose code reaches no hatch, is **io-free**.
An io-free module can compute a wrong answer. It cannot read or write a file, a socket, a
clock, standard error, or a global variable. Those modules leave the security review and
stay in the correctness review.

## 3. The scanner (step S2)

`tools/safety-scan/SafetyScan.lean` runs with `lean --run` on the `.olean` files of a build.
It writes nothing into the build. `tools/safety-scan/safety-scan.py` sets `LEAN_PATH`, adds
source line counts, and writes JSON and Markdown.

Method:

1. Read every constant of every project module (the top namespace of each root, plus the
   one-component lab module names).
2. Mark the hatches of section 2.
3. Edges: the constants named in the value of each definition and opaque, and the
   `@[implemented_by]` target. Theorem values are erased at run time and are not followed.
4. Walk back from each hatch and mark every constant that reaches it.
5. Give each module one class:
   - `effect-typed`: a declaration in it has an effect in its type (test runners, `main`,
     the host bridge, `initialize` cells);
   - `io-free`: no effect in any type, and no hatch reached;
   - `reaches-hatch`: no effect in any type, but the code reaches a hatch. The report names
     each hatch and the module that declares it.

The driver also counts build-time execution in the source (`#eval`, `run_cmd`, `run_elab`,
`run_meta`, `initialize`, `include_str`). That code runs on the machine that builds the
tree, which holds keys and tokens.

Reach: the scan reads only the modules that the roots import in that build. The report
counts the Lean files under `formal/lean4/L4Factoidal` and the lab that it did not read
(`files_not_scanned`). A file that was not read has no class. It is not io-free
(anti-pattern 28).

### Self-test

`safety-scan.py --self-test` compiles seven fixture modules
(`tools/safety-scan/fixtures/SafetyFixture/`) into a temporary directory. It checks each
class against `fixtures/expected.json`:

| Fixture | Plants | Expected |
| --- | --- | --- |
| `Clean` | pure code, a `partial def`, `runST` with a type variable | io-free |
| `Trace` | `dbgTrace` in a function with a pure type | reaches-hatch |
| `Ext` | `@[extern]` opaque | reaches-hatch |
| `Via` | uses `Ext` from another module, through a type class instance | reaches-hatch |
| `Impl` | `@[implemented_by]` an `unsafe` definition | reaches-hatch |
| `Init` | `initialize` of an `IO.Ref` | effect-typed |
| `Main` | `IO` in a type | effect-typed |

Result on 2026-11-13: 7 pass, 0 fail (out of 7). Two mutation checks show that the test can
fail. With `dbgTrace` removed from the list, 6 pass, 1 fail (out of 7). With no edges, 5
pass, 2 fail (out of 7): `Trace` and `Via`.

## 4. First measurement (prototype; not `main`)

The laptop had 7.8 GB free and another session's Web Platform Tests run was in progress, so
this run did not build. It read the existing build in the `factoidal-emoji` worktree
(library `.olean` files of 2026-11-08, lab `.olean` files of 2026-11-10, toolchain 4.33.1).
That build is older than `main`. Its lab still has the 29 `unsafe` and 29 `implemented_by`
that PR 413 (engine state as a value, issue 390) reduced to 3 and 3. The CI step (section 6)
gives the numbers for `main`.

Command:

```sh
E=~/working/factoidal-emoji
python3 tools/safety-scan/safety-scan.py --source-root $E --lab \
  --lean-path $E/formal/lean4/.lake/build/lib/lean:$E/labs/demos/foafnaut/.build/web-render/olean
```

Result, 1,575 modules read, 20 seconds, 2.5 GB peak memory:

- io-free: 1,490 modules, 611,411 lines (93.5 % of the lines read).
- reaches-hatch: 55 modules, 30,474 lines.
- effect-typed: 30 modules, 12,118 lines.
- Files not read: 199 (56 of them in the lab, 22 in WasmVM, 11 in Rendering).

The engine areas that the browser depends on, from the library:

- **All io-free:** HTML, DOM, WHATWG, Rendering, JS (BubblePopJS), HTTP, Net, FrameCost,
  PageGpu, PageCanvas and EventLoop. This holds for the modules that were read.
- **WasmVM:** 28 io-free, 15 reaches-hatch, 7 effect-typed. The hatches reached are the
  `@[extern c inline]` byte stores `WasmVM.Bytes.st16/st32/st64` (`Exec/Bytes.lean`) and
  `Prim.Bytes.pushU64LE`. The 7 effect-typed modules are benches, tests and WASI.
- **Crypto:** 10 modules reach the HACL\* `@[extern]` primitives. These are in the
  vendored, verified C (`skills/crypto-policy`).

The lab (the engine modules in `labs/demos/foafnaut/`) shows where effects enter the
engine today: 40 io-free, 5 reaches-hatch, 5 effect-typed. The hatches are of three kinds:

- **Caches kept between calls:** an `initialize` cell, plus `@[implemented_by]` an `unsafe`
  definition that reads or writes the cell through `unsafeBaseIO`. Examples:
  `NativeSVGText.wordKept`, `WebRender.imageStoreKept`, `WebDocument.keepLayout`.
- **Clock reads in pure code:** `WebWasm.timed`, `WebSparql.timed` (`unsafeIO`).
- **State and randomness for page scripts:** `WebScripts.take`, `WebScripts.peek`,
  `WebScripts.entropy`.

These are the effect points for step S5 (the effect interface). Each one is a place where
the value of a pure-typed function depends on more than its arguments.

## 5. What no theorem covers (trusted base)

- Lean: the compiler, the runtime, `lake`, and the core `@[extern]` constants.
- The C ABI shim `labs/demos/foafnaut/web_render_shim.c`, and the bodies of every
  `@[extern c inline]`.
- The desktop host (Deno TypeScript, `native_window.m`). `tools/host-purity-lint.sh` checks
  that a host makes no decisions. Deno's `fetch` gives TLS.
- The Hub host (`docs/web/hub/foafnaut/*.mjs`), and the host browser's sandbox and CSP.
- HACL\* C (vendored, verified in F\*/Low\*, compiled as is).
- QuickJS-NG (C compiled to Wasm). Its effects are limited to its imports if the WasmVM
  confinement theorem of issue 427 (T7) holds.
- The build and release path: `danbri/factoidal-builds`, CI workflows, npm trusted
  publishing.

## 6. CI

`.github/workflows/verify-lean4.yml`, step "Safety scan (report only)", runs the self-test
and the scan after the library build. It adds the Markdown to the job summary and keeps the
JSON in the `owl-reader-assurance` artifact. It has `continue-on-error: true` and fails no
gate. CI builds `L4Factoidal l4wasm`, not the lab, so the lab is not in that report.

## 7. Relation to the existing checks

| Check | What it sees | What it does not see |
| --- | --- | --- |
| `tools/lean-hygiene-audit.py` | source text: `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by`, `partial def` count | `@[extern]`, `dbgTrace`, `initialize`; anything outside its directory list; reach |
| `LabHygiene.lean` (issue 390) | counts per kind in the lab and in the `L4Factoidal` modules the lab imports, from the environment; a ratchet | which modules reach a hatch; `dbgTrace` |
| `#print axioms` in the build log | the axioms a theorem depends on | code that runs (an `implemented_by` is not an axiom) |
| `tools/host-purity-lint.sh` | decisions in host JavaScript and TypeScript | Lean code |
| this scan | per module: effect in a type, hatches reached, through imports and instances | correctness; what a host does; the C behind an `@[extern]`; Lean core |

## 8. Limits

- The edges come from the kernel's stored values. The compiler starts from the same
  definitions. `@[csimp]` replacements and `@[implemented_by]` targets change the code that
  runs: the scan follows `implemented_by`, and `tools/lean-csimp-reach.py` covers `csimp`.
- A hatch that is reached is not a defect. Most are intentional: a cache, the crypto C, a
  byte store. The scan makes each one visible and names it. Step S3 of issue 427 adds a
  list of approved hatches, each with a reason, and a gate that fails on a hatch that is not
  on the list.
- Build-time execution is counted from source text, not from the environment.

## 9. Next

Issue 427, steps S3 to S9: the approved-hatch list and gate; the map page from the JSON; the
effect interface (one `HostCmd` type) built from the lab effect points of section 4; the
policy theorems on each effect; WasmVM guest confinement; the unreviewed-change metric.
