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
