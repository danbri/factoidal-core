# BubblePopJS and native performance: where the work stands

State on 9 November 2026, for anyone starting on BubblePopJS or native performance. Numbers are from the
branches named; they are native CPU time on a loaded Mac unless stated, so treat small differences as noise.

## Branches (on origin, not on main)

| Branch | Commit | What it holds | State |
|---|---|---|---|
| `wip/bpperf` | `cef6e2a36` | Stage A: Array push in place, environments as slot arrays with a checked resolver (`JS/Resolve.lean`), environment reuse, `PropMap`, `Obj.putOwn` no longer copies, quadratic `indexOf`, Map/Set insert, `delete`, regexp exec and `s += x` removed, `await`/`yield` in loop tests and branches, realm data in the Wasm build, benchmarks in `labs/demos/foafnaut/bubblepop_perf/` (`run.py`, `scaling.py`) | Cloud build failed: 21 declarations missing from `tools/lean-tail-recursion-allow.txt`, and `foafnaut-engines` exited 1 with no message after "Native framebuffer coordinate checks: 12 passed". Being fixed |
| `wip/bpperf-vm` | `d0da73373` | Stage B, on A: `JS/Compile.lean`, `vmLoop` register machine, unboxed numbers in registers, global-name slot cache, calls between compiled functions use no host stack (limit 20,000). 765 of 1,135 prelude functions compile | Not cloud-built; the same gate applies |
| `wip/bootstack` | `2f923ecf1` | Hub start: `LeanJS.snapshotData` no longer run at every engine start, `SfntKern.coverage` binary search, expected-colour probes only under `?check=`, scripts start one frame after the page, link at `-O3`, `hub_boot_breakdown.mjs` | Waiting for its cloud build |

The first two are finishing under the session that wrote them. Check their branch tips before starting on the same code.

## Comparators (native CPU ms, one Mac, machine load 7 to 9)

| Benchmark | Start of 9 Nov | A | B | QuickJS-NG | JSC no-JIT | V8 jitless |
|---|---|---|---|---|---|---|
| fib(26) | 370 | 129 | 79 | 17 | 10 | 14 |
| property read/write | 838 | 443 | 312 | 34 | 20 | 18 |
| method calls | 1319 | 651 | 430 | 57 | 44 | 26 |
| array | 1186 | 713 | 546 | 45 | 30 | 25 |
| string | 263 | 158 | 152 | 12 | 7 | 3 |
| closures | 1093 | 547 | 369 | 34 | 31 | 20 |
| allocation | 1017 | 586 | 499 | 55 | 27 | 16 |
| JSON | 183 | 196 | 197 | 43 | 6 | 12 |
| regexp | 11489 | 30 | 31 | 5 | 2 | 4 |
| mixed | 109 | 68 | 66 | 7 | 6 | 5 |

Stage B is still 4.6 to 12.6 times slower than QuickJS-NG. Nothing in A or B is proved: a build with `verifyLocals` on
found no resolver mismatch across the Test262 subset and the benchmarks, and Test262 went from 5,627 to 5,629 of 6,297 with
no passing file lost. Page-level numbers, Wasm numbers and WPT have not been taken on A or B.

Stage B's plan from there, in order: compile functions with captured variables, `try`, `switch`, for-of and derived
classes; cheaper instruction operands; shapes and real inline caches; a collector. For JIT-class speed, register code
could be translated to Wasm on the Hub and through WasmVM AOT natively. Neither is built.

## Real-site layout, on main

Native, 1600x1000 at 200%, liberal mode, scripts off, relayout in ms, before and after: Wikipedia 2,450 to 97, gov.uk 4,326
to 122, BBC News 58,648 to 537. See `2026-11-09-real-site-layout-speed.md`. On release `2aa065beb`, start and relayout:
Wikipedia 629 and 158, GOV.UK 422 and 122, BBC 611 and 367, w3.org 1,111 and 84, NHS 216 and 45. The next costs named there are
`layoutJSON` float formatting and parsing the whole request as JSON per call.

## Hub start, on `wip/bootstack`

Headless Chrome, median of 3, first frame in ms: default page 1,060 to 676, scripted page 870 to 490, the frame after the
script has run 1,320 to 753. Returning visits: 376 and 387.

## Things that cost time to rediscover

- Lean 4.33.1 types a `Nat` literal below about 2^63 as a scalar, so on 32-bit Wasm one of 2^31 or more given to two owners
  is freed twice. `tools/wasm32-nat-literals.py` and its gate work around it; see `2026-11-09-lean-upstream-wasm32.md`.
- Call depth on 32-bit Wasm is limited to 100. A probe page for a browser's real worker stack is at `/web/hub/wasm-stack/`.
- Cloud builds in `danbri/factoidal-builds` run one at a time with one pending; the hourly schedule replaces a pending
  dispatch. `publish.sh` publishes commits on main only, and a build of a branch is gates only.
- The Hub worker on main sends `zoomUnit`: a Pages deploy needs a released engine from main at or after `036198f21`.
- Local Mac builds go one at a time through a queue, and timings there are taken under load.
- Records of per-area measurements are in this directory, and `skills/foafnaut/SKILL.md` and `2026-11-09-foafnaut-handoff.md`
  describe the browser as a whole.

## Added 2026-11-09, 23:59 UTC, by a Linux cloud session

Branch `claude/foafnaut-perf-bottlenecks-7hpt38`. Records:
[2026-11-09-foafnaut-perf-exploration.md](2026-11-09-foafnaut-perf-exploration.md) (measurements) and
[2026-11-09-bubblepopjs-plan.md](2026-11-09-bubblepopjs-plan.md) (the plan from "compile functions with captured
variables" onward). Stage A (`e8d2a3e6e`) and stage B (`167605f4c`) were built on Linux x86_64 and measured by operation
(61 operations, CPU time and instruction counts) and on six real-world libraries, against QuickJS-NG and V8.

For the sessions that own those branches:

- On stage B `s += x` is quadratic (400,000 appends: 0.13 s on stage A, 1.86 s on stage B). `vmLoop`'s `.add` reads the
  string from its register and appends while the register still holds it, so the append copies. The evaluator lets the
  slot go first (`dropSlotStr`); the machine has no counterpart.
- Conversions to `Float` and `ToInt32`, `ToUint32` went through the big number runtime on every tree. The cloud branch
  has fast versions proved equal to the specifications (`L4Factoidal/Prim/FloatOfNat.lean`, `JS/Number.lean`,
  `JS/Lexer.lean`). They touch no file that stage A or B changes. With them stage B's `i | 1` goes from 394 to 92 ns,
  `a[i & 7]` from 433 to 121 ns, and five library workloads take 4 to 26% less time.
- `python3 tools/lean-literal-parse-audit.py` (also `--float-literals`, `--conversions`) lists what the generated C still
  converts at each call. On stage B: the literal `4294967295.0` in `vmLoop` and in `evalExpr` (the indexed write), and
  `9007199254740991.0` in `Number.isSafeInteger` (the slow case: 16,800 instructions a call).
- Stage B compiles 72 to 89% of the functions of those libraries and is 5.5 to 43 times slower than QuickJS-NG on them.
  43% of the run of a `js_of_ocaml` bundle is `Env.scan`: a variable of an enclosing scope found by its name.
- Eight defects with one-line reproductions (two in the lexer: `/` after `)` and after `++`): section 7.3 of the plan.
- Run BubblePopJS on unknown code under a memory limit: `new Array(4294967295)` takes all memory of the process.

## Added 2026-11-10, 07:00 UTC, by the same Linux cloud session

The branch `claude/foafnaut-perf-bottlenecks-7hpt38` now has `main` at `0fee0a14f` and stage B at `167605f4c` merged
(`d99abc842`), and five repairs on them. Details and measurements: section 6.6 of
[2026-11-09-foafnaut-perf-exploration.md](2026-11-09-foafnaut-perf-exploration.md). Each repair is one commit and can
be taken alone:

- `16577fc02`: the parser chooses between a division and a regular expression literal (`JS/Lexer.lean`,
  `JS/Parser.lean`). `if (s) /x/.test(s)`, `k++ / 2` and `o.default / 2` parse.
- `ff0ebeeef`: a function declaration has no private scope for its name (`JS/Interp.lean` `makeClosure`,
  `JS/Resolve.lean` `rFun`). `function f() { f = ... }` threw before; Babel's helpers do this.
- `5d6d0d10e`: `encodeURI`, `decodeURI`.
- `0861f4b91`: an index for a function environment with more than 24 names (`FunInfo.index`), and no linear scan of
  the `var` names in the parser. A `js_of_ocaml` bundle: run 8,031 to 3,401 ms, load 2,195 to 1,058 ms.
- `195096766`: the statement `s += v` on a local variable of compiled code appends in place; three large `Float`
  literals are named constants.

State: Test262 (6,301 files of `test/language`) 5,633 pass, 664 fail, 4 skip (stage B: 5,629 pass); the six library
workloads of `realworld.py` all give the reference answer; the four Lean gates exit 0; `lake build leanjs L4Factoidal.JS`
passes with `JS/RegressionTests.lean` (91 scripts). Not done on this tree: a native engine build and `test.sh`.

Open, in the order of measured cost: typed array element access through a string key (pako is about 31 times
QuickJS-NG); `s += v` on a global in a compiled top-level loop (still copies); allocation (16 to 26% of each profile);
defects 3 to 7 of the plan's section 7.3.
