# The WebAssembly JS API on BubblePopJS: why `wasm/` scored 1.2%, and the repair

Date: 2026-11-13. Branch: `wip/wasm-jsapi`. Author: wasm-jsapi, a subagent of session depmap33.
Related: `2026-11-08-page-wasm.md` (the API itself), `2026-11-08-lean-js-engine.md` (BubblePopJS),
https://github.com/danbri/factoidal/issues/1244 (WasmVM).

## 1. Finding

BubblePopJS already had the WebAssembly JavaScript API: `tools/wasmvm/quickjs/webassembly.js`
(WebIDL glue) over `WasmVM/Hosts/PageWasm.lean` (decode, validate, link, run in WasmVM), loaded
on the first read of `WebAssembly` (`LeanJS.wasmGlue`). On the whole-WPT run of 2026-11-13
(main `78d9a6d05`) `wasm/jsapi` passed 1,882 of Chrome's 2,529 subtests and `wasm/webapi` 514 of
1,066. The 1.2% came from `wasm/core` (188,396 of the 192,191 subtests): 257 passed.

Every `wasm/core` page failed before it called WebAssembly, for three reasons in the script
engine and one in the page session:

1. Their harness (`wasm/core/js/harness/async_index.js`) runs
   `new Error().stack.toString()` for each assertion. BubblePopJS errors had no `stack`, so
   each page stopped with "Cannot read properties of undefined (reading 'toString')" (186 pages).
2. The generated tests write numbers with separators (`-2_147_483_648`, ES2021 §12.9.3). The
   lexer refused them ("identifier starts immediately after numeric literal"), so the test
   script did not parse and the pages reported only the harness's first test.
3. The harness turns each module's bytes from a string into an ArrayBuffer with
   `bytes.charCodeAt(i)`. On a string that is not ASCII, `charCodeAt` walked the string, and
   was charged for it, at each call: a 20 KB module took the 5 M steps of a run
   (`br_table.wast`), and every larger page paid the quadratic cost.
4. The page script session refused scripts over 4 MiB: the two `simd_*_pmin_pmax` pages
   (4.9 MiB each, 15,521 subtests each) never ran. And seven pages that chain 7,000 to 10,000
   tests through promises passed them all but never reported done: the whole chain runs in one
   microtask checkpoint, which stopped at one run's 5 M steps (the largest needed 13 M).

## 2. Repairs (all in Lean)

- `JS/Lexer.lean`, `scanSepNum`: a numeric literal with a `_` is scanned with the separators
  removed; each separator in the part that was read must stand between two digits of the
  literal's radix; `0_1` and `01_1` are errors. A literal with no `_` takes the old path.
- `JS/Interp.lean`: `Error.prototype.stack`, the accessor of the Error Stack Accessor
  proposal (test262 feature `error-stack-accessor`, `built-ins/Error/prototype/stack`): getter
  `get stack` (a string for an object with [[ErrorData]], `undefined` for others, TypeError on a
  primitive) and setter `set stack` (SetterThatIgnoresPrototypeProperties). Instances have no own
  `stack`, so an error costs nothing for it until a script reads it. The string lists call
  frames (the SpiderMonkey, JSC and QuickJS form); the engine records none, so it is `""`.
  Differences from V8 and QuickJS-NG that a page can see: the string is empty, an own `stack`
  made by assignment is enumerable, and assigning a non-string throws (as the proposal says).
- `JS/Interp.lean`, `cachedReceiverCost`: `charAt` and `charCodeAt` on a non-ASCII string index
  the units that `cachedChars` keeps for the last string (the cache the regular expression code
  already had); the check is one comparison with the cached string, charged a step per 4096
  bytes. Theorem `unitAt?_notAscii` (`JS/Theorems.lean`): the cached array's entry is
  `Str.unitAt?`'s answer. `charAt` is checked by `#guard`s, not proved. A string's `length`
  had the same cost (`Str.jsLength` walks a string that is not ASCII, at every `i < s.length`):
  `HeapOf.strLength` answers from the same cache (theorem `strLength_uncached`: without the cache
  it is `Str.jsLength`; the cached size is checked by `#guard`s, not proved). In the `#guard`
  interpreter a loop over 5,000 `é` took 13.2 s before this and is now quadratic no longer.
- `WasmVM/Hosts/LeanJS.lean`, `checkpointRuns = 8`: a microtask checkpoint has 8 run budgets
  (40 M steps for a page). An endless job or chain still stops.
- `labs/demos/foafnaut/WebScripts.lean`: a page script may be `WebRender.maxSourceBytes`
  (16 MiB), the bound HTML, stylesheets and resources already have.

Tests: `JS/RegressionTests.lean` (`#guard`s for separators, the accessor, `charAt` and
`charCodeAt` on supplementary characters, lone surrogates, two strings in turn, and a 24,000-unit
loop). `lake build L4Factoidal.JS.RegressionTests L4Factoidal.JS.Theorems` and
`lake build L4Factoidal.WasmVM.Hosts.LeanJS` pass on this branch.

## 3. Measured

Both runs on the owner's Mac on 2026-11-13, one after the other, same WPT checkout
(`~/working/wpt-full-run/wpt`), `wpt-score.py run --jobs 3 -- --script-engine bubblepop`, all 524
`/wasm/` names of `full.list`. Before: engine main `78d9a6d05` (the engine of the full run; this
run reproduces its `wasm/` numbers exactly). After: the cloud build of this branch, `07f2aea4e`
(danbri/factoidal-builds run 43472815646, artifact `foafnaut-darwin-arm64`; not published,
since the commit is not on main). Passes are capped at Chrome's count per test.

| | Chrome | before | after |
|---|---:|---:|---:|
| wasm/core | 188,396 | 257 | 185,117 |
| wasm/jsapi | 2,529 | 1,882 | 1,882 |
| wasm/webapi | 1,066 | 514 | 514 |
| wasm/serialization | 76 | 6 | 6 |
| wasm/proposals | 123 | 1 | 18 |
| create_multiple_memory | 1 | 1 | 1 |
| **wasm/ total** | **192,191** | **2,661 (1.4%)** | **187,538 (97.6%)** |

Time: 21.7 s wall before, 42.1 s after (the pages now run their tests: 31 s of page time before,
88 s after). The largest page, `simd_f32x4_pmin_pmax` (4.9 MiB of script, 15,521 subtests),
takes 5.0 s.

Regression check, the same two engines on 300 names of `full.list` outside `wasm/` (every 120th
name, no Test262, service or shared worker variants): 10,239 of 14,291 subtests before, 10,240
after; 121.7 s and 121.8 s wall, 169.1 s and 171.1 s of page time (within run-to-run noise).
A page with no WebAssembly and no long non-ASCII string loops does the same work as before:
the accessor costs nothing until read, and the lexer looks for a `_` only within a number.

Ten `wasm/core` pages (the seven of section 1 and the two `pmin_pmax` pages among them) report
every subtest, all passing, but no harness result ("CRASH" in the runner): a run after the last
test still stops at its 5 M steps. Which run (most likely testharness.js's completion over 10,000
tests in an event or timer task) has not been determined. The scores count their subtests.

## 4. Not done

- The remaining 3,279 `wasm/core` subtests, about 2,600 of them in `memory64/` (WasmVM has
  32-bit addresses only: "unsupported: 64-bit address type"; `validate` answers false for those
  valid modules, and the tests that use them fail after), some relaxed SIMD answers, and
  `names.wast` (480): an export whose name starts with U+10FFFE collides with
  BubblePopJS's encoding of private names (`isPrivKey`), so the exports object cannot hold it.
  That last one is a defect of the engine's property keys, not of WebAssembly.
- `wasm/jsapi` proposals: JSPI (`WebAssembly.Suspending`), `WebAssembly.Function`, shared
  memory, `toResizableBuffer`, GC objects as iterables, js-string builtins.
- The glue is still JavaScript (`webassembly.js`); moving it into Lean built-ins is the
  direction the rules give, and was not attempted here.
- `stack` lists no frames: the engine keeps no record of call sites.

## 5. Checks

Local (this branch, `lake build` inside the build lock): `L4Factoidal.JS` (with `Tests`,
`RegressionTests`, `Theorems`) and `L4Factoidal.WasmVM.Hosts.LeanJS`. Cloud build 43472815646:
every job passed, including the Linux tail-recursion gate, the engine build (with
`lab_ratchet`) and `test.sh --skip-build` in CI form (its `NOT RUN` lines are the usual CI ones).
Not run: the local `labs/demos/foafnaut/test.sh` and `sweeps.sh` (no local engine build: disk).
