# Foafnaut performance exploration: BubblePopJS and the native build of BubblePopKit (2026-11-09)

Owner, 2026-11-09, verbatim: "spend your first session working on a deep dive hands-on,
measurement driven exploration of our perf bottlenecks, especially around our native builds
(esp OSX) and ourJavascript engine. BubblePopJS."

This record holds the method, every number, what this branch changed, and what to do next.
The plan that follows from it: [2026-11-09-bubblepopjs-plan.md](2026-11-09-bubblepopjs-plan.md).
Skill: [skills/foafnaut/SKILL.md](../../skills/foafnaut/SKILL.md), section "Measure BubblePopKit
and BubblePopJS with no Mac". Lean rules that came out of it:
[skills/lean4-performance/SKILL.md](../../skills/lean4-performance/SKILL.md), sections
"Integers through GMP" and "A definition with no argument runs when the program starts".

## 1. Limits of this record

- Machine: a Linux x86_64 cloud VM (Ubuntu 24.04, 4 virtual CPUs, 15 GB), Lean 4.33.1, the
  engine built by `build-web-render.sh --native` (`leanc -O3 -DNDEBUG`). **Not a Mac.** Nothing
  here measures the macOS window, Cocoa, the GPU, Deno, the FFI boundary or the Hub. The CPU
  work of the engine is the same Lean code on both machines; the times are not.
- `perf` on this VM has no hardware counters (`-e cpu-clock` only). Exact figures are
  instruction counts from `valgrind --tool=callgrind`; times are CPU time, least of 3.
- Trees. `main` moved 4 times during the session. BubblePopJS (`L4Factoidal/JS/`) did not
  change from `036198f2` to `489d5cd3a`: the `leanjs` program built at both is the same file,
  byte for byte. "This branch" is `claude/foafnaut-perf-bottlenecks-7hpt38` at `f178e43c1`
  (base `489d5cd3a`). Stage A is `wip/bpperf` at `e8d2a3e6e`; stage B is `wip/bpperf-vm` at
  `167605f4c` (stage A and one commit: a register machine). Both belong to another session
  and are not on `main`. `wip/bootstack` (`2f923ecf1`, a third session) was read, not built.
- "Stage A with the conversions" and "stage B with the conversions" are those trees with this
  branch's `Prim/FloatOfNat.lean`, `JS/Number.lean` and `JS/Lexer.lean` copied in, at their
  first form (two `csimp` theorems for `Float.ofNat` and `Float.ofInt`, and the JavaScript
  twins). The four later theorems (section 7.2) are on this branch only.
- The engine phases of section 9.2 and 9.4 were measured at `036198f2`. The before and after
  figures of 9.5 are two builds of `489d5cd3a`: unchanged, and with this branch.
- Comparison engines, native on the same VM: QuickJS-NG `v0.18.0` (`d7215b0a`, `cc -O2`), and
  Node 22 (V8) with `--jitless` and with its JIT.
- Wording: "proved" is used only for a Lean theorem. For this branch's fast paths: the
  specification is the earlier definition or the Lean core function; the fast version is
  proved equal to it; the compiler is trusted. A `#guard` is a test.

## 2. Results

1. On `main`, BubblePopJS is 5 to 83 times slower than QuickJS-NG on the programs that scale
   linearly, six operations are quadratic, and each call keeps 330 to 500 bytes for good.
2. Stage A and stage B, measured here on another machine and with other programs than their
   own: stage A makes the six operations linear and is 1.2 to 3.5 times faster than `main` on
   the others; stage B's loop is 48 ns against 132 ns on stage A and 320 ns on `main`
   (QuickJS-NG 7 ns).
   One regression on stage B: `s += x` is quadratic again (section 5.3).
3. A cost that no tree had seen: numbers that fit a machine word went through the big number
   runtime (GMP). `Float.ofNat` and every `Float` literal left in a function body read 2^53
   from decimal text at each call, and each JavaScript bit operator ran three GMP remainders.
   This branch repairs it with fast versions proved equal to the specifications (section 7).
   On `main`: `i | 1` 8,356 to 3,667 instructions, `a[i & 7]` 10,126 to 4,783. On stage B:
   `i | 1` 394 to 92 ns, `a[i & 7]` 433 to 121 ns, and 4 to 26% off five real-world workloads. In the engine: the first compile of five pages takes 12 to 23% less time, and the font load and first
   compile of the status page 21% fewer instructions (361,853 decimal parses to 2,612). Outputs are the same, byte for byte.
4. The same fault in another form was found the same day by another session in
   `WebPaint.cullCurve` (a literal `1e300`, 85% of a frame, commit `57fe3531d`).
   `tools/lean-literal-parse-audit.py` now lists every such site from the generated C.
5. Real-world code (section 6): BubblePopJS gives the right answer on 5 of 6 library
   workloads, among them a 1.18 MB `js_of_ocaml` bundle extracted from F\*. Stage B is 5.5 to
   43 times slower than QuickJS-NG on them (geometric mean 13.4) and uses up to 10 times the
   memory. 43% of the F\* bundle's run is one function that finds a variable of an enclosing
   scope by its name.
6. Differential runs against two engines found 7 defects of BubblePopJS that the Test262
   part in the tree does not show (section 6.4). In BubblePopWASM the Lean-compiled module of
   this project runs (1.5 GB of memory for a 32.7 MB module); the `wasm_of_ocaml` modules do not
   decode, for lack of the garbage collection proposal (section 6.5).
7. For one loop iteration, stage B runs 972 instructions and stage A 2,475. A Lean model of
   a register machine on flat arrays of value words runs it in 153, and a call of `fib` in
   17 ns against 23 ns for QuickJS-NG (section 8 and the plan). The distance to QuickJS-NG is
   the data layout, not Lean.
8. The native engine ran 1,109 M instructions before `main` (0.11 s), 740 M of them one
   constant that only a build tool reads. `wip/bootstack` repairs it; it is not on `main`.
9. A frame of the status page on a kept layout is 249 M instructions: 39% writes the scene's
   floats one byte at a time, 32% builds the scene again, 19% writes layout text.
10. Added 2026-11-10 (section 6.6): this branch now has `main` and stage B merged, and five
    repairs on them. BubblePopJS gives the right answer on 6 of 6 library workloads. The
    `js_of_ocaml` bundle runs 2.4 times faster and loads 2.1 times faster (26 to 11 times
    QuickJS-NG): the name scan of item 5 is gone. Three defects more were found behind the
    first one in `marked` and repaired. `s += v` in a compiled function is linear again.
    Test262: 5,633 pass of 6,301 (5,629 before).

What to do next: section 12, and the plan.

## 3. Method

### 3.1 Benchmarks

- **Programs** (25 files, each reads a global `N`): one engine operation each, in a function
  unless the name says global. Run at N, 2N and 4N. Net time is wall time less the engine's
  start (4.6 ms BubblePopJS, 2.4 ms QuickJS-NG, 23 to 26 ms Node). The exponent `k` in
  time ~ N^k comes from the N and 4N points.
- **Single operations** (61): `labs/demos/foafnaut/bubblepop_perf/opcost.py`. Each is the body
  of one loop in a function that makes no closure, so that stage B's register machine runs
  it. The cost is the slope of the CPU time between N and 5N, less the slope of the empty
  loop. `--callgrind` gives instructions, heap allocations (`mi_malloc_small` calls) and calls
  into the big number runtime, each for one iteration.
- **Real-world code**: `labs/demos/foafnaut/bubblepop_perf/realworld.py` (section 6).
- Commands (engines as `NAME=CMD`):

      python3 labs/demos/foafnaut/bubblepop_perf/opcost.py \
        bubblepop='formal/lean4/.lake/build/bin/leanjs run' qjs=/path/qjs v8-jitless='node --jitless'
      python3 labs/demos/foafnaut/bubblepop_perf/opcost.py --callgrind \
        bubblepop='formal/lean4/.lake/build/bin/leanjs run'
      python3 labs/demos/foafnaut/bubblepop_perf/realworld.py \
        bubblepop='formal/lean4/.lake/build/bin/leanjs run' v8=node qjs=/path/qjs

### 3.2 The engine

`labs/demos/foafnaut/.build/web-render/web-render-native PAGE 1600 1000 --document-bin REQ FONT OUT COUNT`
loads Noto Sans, compiles the page once and then COUNT times more with a field `repeat` that
makes each call its own. `REQ` is
`{"op":"render","url":"https://example.invalid/","resources":[],"commands":[],"checks":false}`.
callgrind at COUNT 0, 1 and 4 separates: start, font load and first compile (COUNT 0); one frame
on a kept layout ((COUNT 4 - COUNT 1) / 3).

### 3.3 Before and after

A comparison is two builds of one base commit. The unchanged base was built in a second
worktree with a copy of the build caches (and the stale files of this branch's module
removed). `main` moved four times in three hours, and the first comparison of the session, on
`036198f2`, had to be repeated on `489d5cd3a`.

## 4. BubblePopJS by program: `main`, stage A, stage B

Net milliseconds at the largest size, and the exponent `k` on each tree (1.0 is linear).
`qjs` is QuickJS-NG, `v8jl` is `node --jitless`.

| Program | N | main | stage A | stage B | qjs | v8jl | main/qjs | A/qjs | B/qjs | k main | k A | k B |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| arith (`* / %` and bit operators) | 400,000 | 1,568 | 1,156 | 1,013 | 18.8 | 14.7 | 83 | 62 | 54 | 1.06 | 1.00 | 1.01 |
| string_concat | 400,000 | 2,361 | 313 | 2,031 | 46.5 | 60.4 | 51 | 6.7 | 44 | 1.64 | 0.99 | 1.77 |
| array_index_write | 800,000 | 1,616 | 1,091 | 836 | 32.1 | 45.1 | 50 | 34 | 26 | 0.99 | 0.98 | 1.00 |
| string_index (`charCodeAt`, `s[i]`) | 600,000 | 1,030 | 731 | 714 | 42.2 | 24.5 | 24 | 17 | 17 | 1.03 | 0.90 | 1.04 |
| loop_global_var | 800,000 | 908 | 429 | 226 | 13.5 | 12.2 | 67 | 32 | 17 | 1.02 | 1.00 | 1.00 |
| array_index_read | 1,200,000 | 913 | 558 | 352 | 21.4 | 24.5 | 43 | 26 | 16 | 0.99 | 1.00 | 0.99 |
| global_fn_call | 800,000 | 1,480 | 596 | 330 | 22.8 | 17.7 | 65 | 26 | 14 | 1.05 | 0.99 | 1.01 |
| try_catch | 800,000 | 909 | 617 | 622 | 54.5 | 38.7 | 17 | 11 | 11 | 1.01 | 1.00 | 0.99 |
| closure_call | 800,000 | 1,063 | 418 | 238 | 23.2 | 24.3 | 46 | 18 | 10 | 0.98 | 1.02 | 1.00 |
| deep_scope (8 scopes up) | 1,200,000 | 724 | 278 | 128 | 12.6 | 15.7 | 58 | 22 | 10 | 1.02 | 0.98 | 1.00 |
| array_push | 80,000 | 4,920 | 39.8 | 33.4 | 3.5 | 7.6 | 1406 | 11 | 9.5 | 2.07 | 0.92 | 1.00 |
| array_methods | 80,000 | 4,882 | 88.9 | 91.8 | 10.3 | 7.2 | 474 | 8.6 | 8.9 | 1.98 | 0.98 | 0.97 |
| class_new | 400,000 | 1,268 | 722 | 577 | 69.7 | 31.2 | 18 | 10 | 8.3 | 1.00 | 1.03 | 0.97 |
| call_args | 800,000 | 1,336 | 437 | 197 | 26.8 | 32.9 | 50 | 16 | 7.4 | 1.01 | 1.00 | 0.99 |
| empty_loop | 2,000,000 | 625 | 274 | 99.1 | 14.8 | 16.0 | 42 | 19 | 6.7 | 0.90 | 0.97 | 0.99 |
| method_call | 800,000 | 1,228 | 470 | 282 | 42.9 | 33.4 | 29 | 11 | 6.6 | 1.04 | 0.98 | 1.01 |
| prop_rw | 1,200,000 | 850 | 374 | 221 | 34.9 | 25.5 | 24 | 11 | 6.3 | 1.03 | 1.02 | 1.01 |
| obj_alloc | 800,000 | 829 | 518 | 350 | 57.0 | 20.4 | 15 | 9.1 | 6.1 | 0.97 | 0.98 | 1.00 |
| fib(20), 24 times | 24 | 404 | 132 | 76.9 | 12.7 | 15.2 | 32 | 10 | 6.1 | 1.01 | 0.94 | 0.99 |
| regex | 400,000 | 849 | 730 | 734 | 157 | 63.1 | 5.4 | 4.6 | 4.7 | 1.03 | 1.01 | 1.01 |
| loop_fn_var | 1,600,000 | 797 | 351 | 106 | 28.6 | 24.3 | 28 | 12 | 3.7 | 1.02 | 0.98 | 0.99 |
| dict_build (one object, N keys) | 40,000 | 9,639 | 56.1 | 46.7 | 12.9 | 35.5 | 747 | 4.3 | 3.6 | 2.09 | 0.95 | 1.06 |
| json | 40,000 | 2,775 | 232 | 230 | 69.3 | 27.7 | 40 | 3.4 | 3.3 | 2.09 | 1.01 | 1.06 |
| loop_fn_let | 1,200,000 | 926 | 267 | 80.8 | 25.8 | 17.1 | 36 | 10 | 3.1 | 1.00 | 1.00 | 1.01 |
| map_set | 80,000 | 12,749 | 139 | 129 | 111 | 15.2 | 115 | 1.3 | 1.2 | 2.53 | 1.04 | 1.09 |

**Quadratic on `main`**: `array_push`, `array_methods`, `dict_build`, `json`, `map_set`,
`string_concat`. At N = 100,000: `a.push(i)` 9.9 s, `o['k'+i] = i` 62.8 s, `m.set(i, i)` 23.3 s,
JSON of 100,000 objects 28.6 s. Causes, read in the source: `Array.prototype.push` builds
`es ++ args` from a copy of the elements that the object still holds; `collPut` reads `es.size`
after `es.push`, so the push copies; `Obj.putOwn` reads `o.props.contains` after
`o.props.insert`, so the insert copies the bucket array. Stage A repairs all six.

**Memory kept on `main`** (peak resident growth for each iteration; nothing frees it): a call
334 to 494 bytes (800,000 calls: 267 to 388 MB), a `for (let ...)` iteration 315 bytes, a small
object 458 bytes, `new` and one method call 897 bytes. QuickJS-NG and V8: 0. On stage A a call
keeps 0 bytes; an object keeps 328 bytes (`s = { k: i, v: i }`), a class instance 314. No tree
has a collector.

## 5. BubblePopJS by operation

### 5.1 Time

Nanoseconds for one operation, less the loop; the first two rows are the loops themselves.
Least CPU time of 3 runs, N = 200,000 and 1,000,000, one run of the script on a quiet machine.
A difference under 10 ns or 10% is not a result. "main + branch" is this branch.

| Operation | main | main + branch | stage A | stage B | stage B with the conversions | qjs | v8jl | stage B / qjs |
|---|---|---|---|---|---|---|---|---|
| the loop itself (`i < n; i++`) | 320 | 305 | 132 | 48 | 50 | 8 | 8 | 6 |
| the loop in a function that has an inner function | 339 | 330 | 140 | 136 | 147 | 7 | 7 | 19 |
| `s = function () { return i; }` | 1309 | 1314 | 1098 | 1049 | 968 | 119 | 11 | 9 |
| `s = () => i` | 773 | 764 | 655 | 641 | 534 | 94 | 15 | 7 |
| `s = a[i & 7]` | 687 | 339 | 538 | 433 | 121 | 7 | 8 | 60 |
| `s = t.charCodeAt(3)` | 556 | 474 | 483 | 416 | 362 | 25 | 12 | 17 |
| `s = { x: i, y: k }` | 735 | 804 | 597 | 411 | 386 | 66 | 13 | 6 |
| `s = i << 1` | 542 | 303 | 488 | 398 | 158 | 5 | 6 | 81 |
| `s = i \| 1` | 536 | 236 | 465 | 394 | 92 | 5 | 5 | 81 |
| `s = i ^ 5` | 529 | 243 | 517 | 373 | 94 | 5 | 4 | 75 |
| `s = i & 255` | 515 | 234 | 472 | 368 | 100 | 5 | 6 | 71 |
| `s = i >>> 1` | 486 | 306 | 427 | 332 | 148 | 5 | 6 | 68 |
| `s = String(i)` | 570 | 479 | 473 | 320 | 260 | 35 | 24 | 9 |
| `s = Math.floor(i)` | 485 | 493 | 404 | 298 | 270 | 20 | 7 | 15 |
| `s = i >> 1` | 440 | 277 | 376 | 298 | 152 | 5 | 2 | 56 |
| `s = h1(i)` (inner function) | 795 | 798 | 264 | 286 | 298 | 16 | 12 | 17 |
| `s = 'k' + i` | 404 | 320 | 310 | 249 | 179 | 45 | 28 | 6 |
| `try { s = i; } catch (e) {}` | 177 | 197 | 139 | 221 | 224 | 7 | 3 | 31 |
| `a[3] = i` | 400 | 368 | 243 | 195 | 175 | 6 | 6 | 35 |
| `s = t[3]` | 359 | 275 | 279 | 187 | 136 | 20 | 5 | 9 |
| `s = g1(i)` (top-level function) | 848 | 912 | 343 | 166 | 150 | 15 | 12 | 11 |
| `s = ~i` | 315 | 242 | 274 | 161 | 65 | 4 | 4 | 41 |
| `s = [i, k, 1]` | 361 | 386 | 302 | 160 | 167 | 39 | 26 | 4 |
| `s = i % 7` | 284 | 266 | 231 | 153 | 98 | 5 | 5 | 33 |
| `s = g0()` | 587 | 561 | 354 | 148 | 154 | 12 | 10 | 12 |
| `s = gf(i)` | 894 | 935 | 360 | 146 | 146 | 15 | 17 | 10 |
| `s = o.m(i)` | 822 | 757 | 269 | 142 | 136 | 18 | 14 | 8 |
| `s = []` | 214 | 233 | 206 | 99 | 102 | 23 | 6 | 4 |
| `G = i` | 434 | 422 | 228 | 90 | 83 | 3 | 6 | 33 |
| `o.x = i` | 258 | 340 | 114 | 86 | 81 | 6 | 2 | 15 |
| `s = a[3]` | 231 | 186 | 172 | 79 | 27 | 5 | 2 | 15 |
| `s = {}` | 184 | 191 | 175 | 75 | 76 | 22 | 4 | 3 |
| `s = a.length` | 258 | 202 | 178 | 59 | 19 | 6 | 5 | 10 |
| `s = t.length` | 228 | 178 | 163 | 58 | 18 | 6 | 5 | 9 |
| `s = i != k` | 189 | 234 | 140 | 54 | 51 | 5 | 4 | 11 |
| `s = i == k` | 200 | 189 | 116 | 50 | 46 | 4 | 3 | 11 |
| `s = typeof i` | 164 | 173 | 223 | 41 | 34 | 6 | 2 | 7 |
| `s = Math.PI` | 215 | 210 | 154 | 38 | 29 | 4 | 2 | 9 |
| `s = undefined` | 232 | 195 | 167 | 37 | 29 | 4 | -1 | 8 |
| `s = G` (global) | 184 | 194 | 175 | 36 | 29 | 3 | 3 | 14 |
| `s++` | 156 | 161 | 71 | 32 | 26 | 2 | 5 | 17 |
| `s = o.m` (on the prototype) | 218 | 219 | 138 | 31 | 35 | 9 | 2 | 3 |
| `++s` | 191 | 178 | 76 | 30 | 26 | 1 | 3 | - |
| `{ let q = i; s = q; }` | 637 | 700 | 363 | 27 | 31 | 8 | 6 | 3 |
| `s = o.x` | 179 | 192 | 113 | 27 | 20 | 7 | 5 | 4 |
| `s = i ? 1 : 2` | 154 | 195 | 100 | 26 | 20 | 7 | 1 | 4 |
| `s = i && k` | 172 | 164 | 115 | 25 | 27 | 9 | 4 | 3 |
| `s += k` | 181 | 176 | 84 | 23 | 22 | 2 | 6 | 9 |
| `s = s / k` | 224 | 208 | 104 | 21 | 21 | 5 | 4 | 4 |
| `s = i === k` | 189 | 200 | 107 | 20 | 13 | 5 | 4 | 4 |
| `s = s - k` | 178 | 196 | 110 | 18 | 16 | 4 | 4 | 5 |
| `s = s + k` | 204 | 214 | 113 | 18 | 15 | 2 | 2 | 9 |
| `s = i < k` | 175 | 185 | 108 | 17 | 13 | 5 | 4 | 3 |
| `s = i <= k` | 268 | 308 | 113 | 17 | 14 | 4 | 7 | 4 |
| `s = i !== k` | 227 | 215 | 111 | 16 | 10 | 5 | 6 | 3 |
| `s = -i` | 173 | 197 | 143 | 15 | 18 | 4 | 1 | 4 |
| `s = s * k` | 221 | 210 | 114 | 15 | 17 | 5 | 5 | 3 |
| `s = !i` | 172 | 168 | 112 | 14 | 15 | 3 | 3 | 4 |
| `s = k` | 124 | 129 | 95 | 12 | 13 | 3 | 2 | 4 |
| `s = 1` | 110 | 105 | 92 | 10 | 14 | 3 | -1 | 4 |
| `if (i < 0) s = 2` | 67 | 77 | 51 | 3 | 2 | 5 | 2 | 1 |

### 5.2 Instructions and allocations

callgrind, for one iteration, less the loop (instructions / allocations). The loop itself, as
the difference of N = 300,000 and N = 100,000: `main` with the first conversions 5,238
instructions and 25 allocations; stage A with them 2,475 and 10; stage B with them 972 and 0.

| Operation | stage A | stage B | stage B with the conversions (instructions) |
|---|---|---|---|
| `s = 1` | 1,265 / 4 | 238 / 0 | 238 |
| `s = s + k` | 1,776 / 5 | 331 / 0 | 331 |
| `s = i < k` | 1,778 / 5 | 381 / 1 | 381 |
| `s = o.x` | 1,652 / 4 | 477 / 0 | 477 |
| `o.x = i` | 1,660 / 4 | 1,456 / 4 | 1,457 |
| `s = a[3]` | 2,443 / 4 | 1,396 / 0 | 623 |
| `a[3] = i` | 3,524 / 6 | 2,955 / 5 | 2,955 |
| `s = a[i & 7]` | 8,289 / 10 | 7,362 / 8 | 2,002 |
| `s = a.length` | 2,516 / 5 | 1,217 / 0 | 444 |
| `s = G` (global) | 2,449 / 5 | 729 / 0 | 729 |
| `G = i` | 3,053 / 7 | 1,502 / 4 | 1,501 |
| `s = g1(i)` (top-level function) | 4,990 / 12 | 2,560 / 7 | 2,561 |
| `s = o.m(i)` | 3,738 / 9 | 2,438 / 6 | 2,438 |
| `s = h1(i)` (inner function) | 3,802 / 11 | 4,125 / 12 | 4,125 |
| `{ let q = i; s = q; }` | 5,206 / 19 | 652 / 0 | 652 |
| `s = i \| 1` | 7,060 / 9 | 6,306 / 8 | 1,617 |
| `s = i << 1` | 7,191 / 8 | 6,433 / 7 | 2,474 |
| `s = i % 7` | 3,132 / 8 | 2,373 / 7 | 1,599 |
| `s = Math.floor(i)` | 5,060 / 15 | 3,885 / 10 | 3,885 |
| `s = t.charCodeAt(3)` | 6,179 / 20 | 5,705 / 17 | 4,932 |
| `s = String(i)` | 6,218 / 13 | 4,413 / 8 | 3,614 |
| `s = {}` | 1,846 / 8 | 871 / 4 | 871 |
| `s = { x: i, y: k }` | 5,300 / 20 | 3,430 / 13 | 3,430 |
| `s = [i, k, 1]` | 2,677 / 9 | 1,846 / 8 | 1,847 |
| `s = function () { return i; }` | 8,238 / 31 | 8,217 / 29 | 7,444 |
| `s = () => i` | 5,193 / 18 | 5,209 / 17 | 4,436 |
| `try { s = i; } catch (e) {}` | 2,091 / 8 | 3,641 / 18 | 3,642 |
| `s = typeof i` | 3,425 / 10 | 702 / 3 | 703 |

Where one iteration of the empty loop goes on stage A (2,475 instructions): `evalExpr` 615
for 2 calls, `forLoop` 296, `assignLocal` 274, `mi_free` 260, `lean_dec_ref_cold` 153,
`lookupLocal` 144, `mi_malloc_small` 120, `lean_alloc_ctor` 119. Allocate, free and reference
counts are about 30%. The 10 allocations are one result object for each evaluator function
that returns (`EStateM.Result`) and one box for the number.

On stage B the whole iteration is in `vmLoop` (972 instructions, no allocation), `s = s + k`
adds 329 and a call of a compiled function 2,558. A register is a Lean value in an
`Array Value`, an instruction is a Lean object whose read changes two reference counts, and
operands are `Nat`s. Section 8 measures the same operations with none of the three.

### 5.3 What stage B does not cover, and one regression

- A function that makes a closure, or uses `try`, `switch`, `for-in`, `for-of`, spread or a
  class with `super`, stays in the evaluator (its own record). A `try` with nothing thrown is
  221 ns on stage B against 139 ns on stage A.
- `leanjs compile-stats FILE`: functions compiled, of functions seen: lodash 540 of 691,
  acorn 301 of 340, pako 76 of 100, immutable 504 of 701, the F\* bundle 3,353 of 4,457.
- **Regression** (repaired for a local variable on 2026-11-10, section 6.6). `s += 'x'`, 100,000, 200,000 and 400,000 times, CPU seconds: stage A 0.05,
  0.07, 0.13; stage B 0.14, 0.50, 1.86 (in a function and at the top level). On stage B a
  loop is compiled, and `vmLoop`'s `.add` (`JS/Interp.lean` line 4793 at `167605f4c`) reads
  the string from its register and appends while the register still holds it, so the append
  copies. The evaluator lets the slot go first (`dropSlotStr`). `s = s + 'x'` is quadratic on
  every tree.
- `a[3] = i` does not gain from the conversions on stage A or B: the indexed write has the
  literal `4294967295.0` in `evalExpr` and in `vmLoop`, read from text at each write.

## 6. Real-world code

### 6.1 Method

`realworld.py` builds one script for each workload and size: `var N = n;`, a prelude with
`module` and `exports` (no language feature), the library's single-file build, and a driver
that prints `RESULT <checksum>`. A library comes from the npm registry by exact version
(`npm pack --ignore-scripts`), its tarball's sha256 is checked against
`realworld/manifest.json`, and no library code is in this repository. A run counts only when
its line equals the reference engine's. Every run is under a watchdog (resident memory and
time). Sizes: 0 (load only), N and 4N.

### 6.2 Results

CPU milliseconds at 4N less the load, the ratio to QuickJS-NG, and peak resident memory.
Quiet machine, least of 3.

| Workload (N) | main | main + branch | stage A | stage B | stage B with the conversions | QuickJS-NG | V8 no JIT | V8 |
|---|---|---|---|---|---|---|---|---|
| lodash 4.17.21 (1000) | 1,709 ms, x22.7, 412 MB | 1,660 ms, x22.0, 412 MB | 733 ms, x9.7, 42 MB | 417 ms, x5.5, 42 MB | 359 ms, x4.8, 42 MB | 75 ms, 17 MB | 34 ms, x0.4, 51 MB | 42 ms, x0.6, 58 MB |
| acorn 8.11.3 (1) | 1,609 ms, x12.6, 254 MB | 1,522 ms, x12.0, 254 MB | 1,007 ms, x7.9, 32 MB | 935 ms, x7.3, 34 MB | 895 ms, x7.0, 32 MB | 127 ms, 17 MB | 57 ms, x0.4, 46 MB | 94 ms, x0.7, 55 MB |
| pako 2.1.0 (32) | 3,648 ms, x57.2, 100 MB | 3,152 ms, x49.4, 100 MB | 2,910 ms, x45.7, 21 MB | 2,744 ms, x43.0, 20 MB | 2,019 ms, x31.7, 20 MB | 64 ms, 17 MB | 51 ms, x0.8, 44 MB | 61 ms, x1.0, 51 MB |
| marked 4.3.0 (6) | does not load | does not load | does not load | does not load | does not load | 32 ms, 17 MB | 14 ms, x0.5, 45 MB | 14 ms, x0.4, 50 MB |
| immutable 4.3.5 (1000) | 2,682 ms, x22.2, 412 MB | 2,611 ms, x21.6, 411 MB | 1,569 ms, x13.0, 77 MB | 1,176 ms, x9.7, 80 MB | 992 ms, x8.2, 80 MB | 121 ms, 17 MB | 65 ms, x0.5, 50 MB | 138 ms, x1.1, 59 MB |
| the F\* bundle (`js_of_ocaml` 6.4.1) (40) | 6,585 ms, x27.5, 1,636 MB | 5,811 ms, x24.3, 1,636 MB | 5,754 ms, x24.0, 207 MB | 5,990 ms, x25.0, 213 MB | 4,983 ms, x20.8, 214 MB | 239 ms, 21 MB | 149 ms, x0.6, 61 MB | 95 ms, x0.4, 71 MB |
| geometric mean of x (workloads that run) | 25.1 (of 5) | 23.3 (of 5) | 16.1 (of 5) | 13.4 (of 5) | 11.3 (of 5) | 1 | 0.5 (of 6) | 0.7 (of 6) |

Load only (parse and top-level evaluation), CPU ms:

| Library (size) | main | main + branch | stage A | stage B | stage B with the conversions | QuickJS-NG | V8 no JIT | V8 |
|---|---|---|---|---|---|---|---|---|
| lodash 4.17.21 (544 kB) | 47 | 50 | 47 | 52 | 57 | 24 | 35 | 31 |
| acorn 8.11.3 (231 kB) | 85 | 85 | 37 | 42 | 37 | 19 | 28 | 26 |
| pako 2.1.0 (238 kB) | 30 | 28 | 32 | 30 | 28 | 13 | 26 | 22 |
| marked 4.3.0 (49 kB) | does not load | does not load | does not load | does not load | does not load | 9 | 26 | 24 |
| immutable 4.3.5 (171 kB) | 25 | 24 | 30 | 33 | 32 | 17 | 34 | 30 |
| the F\* bundle (`js_of_ocaml` 6.4.1) (1178 kB) | 1,838 | 1,678 | 1,712 | 1,633 | 1,587 | 272 | 98 | 107 |

- BubblePopJS gives the reference answer on 5 of 6 workloads, on every tree. `marked` does not
  load (6.4, item 1).
- This branch's conversions on `main`: 3 to 14% less run time. On stage B (first form): 4 to
  26% less; the geometric mean of the ratio to QuickJS-NG goes from 13.4 to 11.3.
- V8's CPU time includes its compiler threads, so on runs this short V8 with its JIT can show
  more CPU time than V8 without it.

### 6.3 Where the time goes (stage B with the conversions, `perf` samples, self time)

| Workload | Largest shares |
|---|---|
| the F\* bundle | `Env.scan` 42.9%, `vmLoop` 12.1%, `memcmp` 6.2%, allocate and free 7.4%, `lean_dec_ref_cold` 2.8%, `List.filterTR` in `parseBlock` 2.0% |
| pako | `vmLoop` 9.6%, allocate and free 25.8% (of it the C library's `malloc`, `free`: 9.1%), `evalExpr` 4.0%, `arrayIndex?` and its helpers 5.6%, `Obj.getOwn` 2.9%, `findProp` 2.7%, `PropMap.scan` 1.7%, `__gmpz_n_pow_ui` 1.3% |
| acorn | `vmLoop` 20.8%, allocate and free 21.0%, `fastGet` 4.9%, `evalExpr` 4.0%, hash map lookups of `PropMap` and `hash_str` 5.2%, `Re.matchNode` 1.6% |
| immutable | `vmLoop` 31.5%, allocate and free 12.4%, `Env.scan` 6.6%, `fastGet` 3.6%, `__gmpz_set_str` and its helper 3.2% |

- `Env.scan` finds a name in an environment by comparing strings. A bundle is one function
  with thousands of names, and an inner function's use of one of them scans that list.
- `arrayIndex?` parses an array index from a string: an element of a typed array is read
  through a string key.
- The `__gmpz_set_str` in immutable is a `Float` literal in a function body: the first form of
  the conversions did not reach those; section 7.2 does.

### 6.4 Defects found

By `realworld.py` and by a differential script of 1,671 lines of output (index, length, bit
operator and number-to-string cases at the edges of 2^31, 2^32 and 2^53), run on BubblePopJS,
QuickJS-NG and V8. QuickJS-NG and V8 agree on every line. BubblePopJS differs on 23 lines, the
same on `main`, stage A and stage B. The defects are a checklist in
https://github.com/danbri/factoidal-core/issues/378 (the plan and its key results). Items 1, 2,
9 and 10 are repaired on this branch (2026-11-10), with tests in
`formal/lean4/L4Factoidal/JS/RegressionTests.lean` (section 6.6); items 3 to 7 have no test yet.

1. `if (s) /y/.test(s);`, `for (...) /re/.test(x)`, `if (1) {} /re/.test(x)`: SyntaxError
   "regular expression literals are not supported". The lexer takes `/` after `)` and after `}`
   as a division. `marked.min.js` has `for(...)/^ *-+: *$/.test(...)`.
2. `var b = a.x++ / 2;`: SyntaxError "missing ';'". The lexer takes `/` after `++` as the
   start of a regular expression.
3. `[10,11,12,13,14].lastIndexOf(13, 0)` gives 3 (17 of 34 start indices differ). Answer: -1.
4. `(0.5).toString(16)` gives `0.5`. Answer: `0.8`.
5. `var b = [1,2,3]; b[1000000] = 7; b.length` gives 3. Answer: 1000001. (A gap of 100,000
   gives the right length.)
6. `var b = []; b.length = 5; 0 in b` gives true. Answer: false.
7. `new Array(4294967295)` and `b.length = 4294967295` take memory until the process is
   killed (1.5 GB in 1 s). `b.length = 10000000` takes 295 MB. Strings and typed arrays have a
   limit (`Invalid string length`); arrays have none. During the session this killed a
   running build on the same machine.
8. On stage B only: `s += x` copies the string at each append (section 5.3). Repaired on this
   branch (section 6.6).
9. Found 2026-11-10, behind item 1 in `marked`: `function f() { f = 1 }` threw "Assignment to
   constant variable". A function declaration got the private scope that only a function
   expression has for its name, so the name inside the body was a read-only copy; a read of it
   did not see a later assignment from outside. Helpers that Babel writes replace themselves
   this way (`function _extends() { _extends = Object.assign ...`). On `main`, stage A and
   stage B. Also: an assignment to a function expression's own name from code that is not
   strict threw; ECMA-262 §9.1.1.1.5 says it does nothing.
10. Found 2026-11-10, behind item 9: `encodeURI` and `decodeURI` did not exist. `marked` catches
    the ReferenceError and writes a link as plain text: a wrong answer with no error.

### 6.5 WebAssembly from verified-language toolchains, in BubblePopWASM

`lake exe wasmvm-bench` (native, this VM), with the modules of the project's own release
`build-730684b2a754` as inputs (`tools/fetch-builds.sh --set web` and `--set foafnaut-web`;
they are test inputs here, not the build of this tree).

| Module | Made by | Result |
|---|---|---|
| `l4factoidal.wasm`, 32.7 MB, 23,747 functions, 12.9 M operations | Lean 4, to C, to WebAssembly by Emscripten | decode 3.7 s; validate and compile 3.6 s; instantiate; `l4_init` (the Lean runtime and every module) 3.7 s; `l4_version_c` gives the version text. Peak resident memory 1,489 MB. The process took 41.6 s; the 30 s outside the three steps were not attributed |
| `l4factoidal-core.wasm`, 9.3 MB | the same | validates and compiles in 0.9 s, 527 MB |
| `factoidal-npm-entry.wasm`, `factoidal.wasm`, `w3c-runner.wasm` code modules, 0.9 to 1.5 MB | F\*, to OCaml, to WebAssembly by `wasm_of_ocaml` | `decode: unsupported: GC type definition at byte 13`. BubblePopWASM has no garbage collection proposal, so no `wasm_of_ocaml` module runs |
| `qjs-wasmvm.wasm`, 1.25 MB, 377,234 operations | QuickJS-NG 0.18.0 (C), by Emscripten | validate and compile 65 ms. `fib(24)`: 148.5 M instructions in 720 ms (205 M a second). Loop and JSON: 331.5 M instructions in 1,629 ms. Its plain JavaScript checks: 23 pass, 2 fail (not looked at) |

- The engine's own benchmark here: `sum` 388 M instructions a second, `memsum` 283 M, `fib(30)`
  193 M; `engine --check` passes its floors. (Apple M1 in the WasmVM record: 359 to 381, 207 to
  228, 177.)
- `fib(24)` is 150,049 calls. QuickJS-NG as WebAssembly inside BubblePopWASM: 4,800 ns for one
  call. Native: QuickJS-NG 23 ns, BubblePopJS stage B 145 ns, `main` 752 ns.
- A 32.7 MB module needs 1.5 GB: each operation is a Lean object. The WasmVM record names code
  as bytes as a next step; this is its size on a real module.
- On `main` at `489d5cd3a`, `lake build wasmvm-bench` fails: `WasmVM/Bench/Page.lean` names
  `Hosts.LeanJS.prepare`, which is in `Hosts/LeanJSRealm.lean`, and does not import that
  module. This branch adds the import (one line).

### 6.6 Repairs of 2026-11-10 on this branch

Six commits on the merged tree (`main` at `0fee0a14f` with stage B at `167605f4c`, section 11).
Each has tests in `formal/lean4/L4Factoidal/JS/RegressionTests.lean` (91 scripts; the expected
lines are those of QuickJS-NG 0.18.0 and Node 22).

| Commit | Repair | Defect of 6.4 |
|---|---|---|
| `16577fc02` | The parser chooses between a division and a regular expression literal. The lexer makes a first choice from the tokens before the `/`; the parser asks for the other reading at the two places where the grammar decides (`P.relexAt`). | 1, 2 |
| `ff0ebeeef` | A function declaration has no private scope for its name. An assignment to a function expression's name from code that is not strict does nothing. | 9 |
| `5d6d0d10e` | `encodeURI`, `decodeURI`. | 10 |
| `0861f4b91` | A function environment with more than 24 names has an index, shared by its environments (`FunInfo.index`). The parser keeps its `var` names in a set too, and takes the names added in a block from the end of the list. | section 6.3, `Env.scan` |
| `195096766` | The statement `s += v` on a local variable of compiled code is one add on the variable's register, and the string is appended to in place. `4294967295.0`, `4294967296.0`, `9007199254740991.0` are named constants. | 8; section 5.3 |

The corpus, one run of `realworld.py` with three engines (CPU ms, least of 3; "before" is the
merged tree, "after" is `0861f4b91`). The session's machine was replaced during the night, and
the same binaries take about 1.5 times the times of section 6.2 on the new one: compare inside
this table only.

| Workload | before: load, run, x QuickJS-NG | after: load, run, x QuickJS-NG | QuickJS-NG: load, run |
|---|---|---|---|
| lodash | 70, 614, x5.4 | 68, 579, x5.1 | 35, 113 |
| acorn | 53, 1,320, x7.4 | 50, 1,268, x7.1 | 27, 179 |
| pako | 36, 3,061, x18.6 | 38, 2,995, x18.2 | 18, 165 |
| marked | does not load | 23, 232, x5.3 | 13, 44 |
| immutable | 37, 1,454, x9.5 | 38, 1,388, x9.1 | 32, 153 |
| the F\* bundle | 2,195, 8,031, x26.1 | 1,058, 3,401, x11.0 | 442, 308 |

- BubblePopJS gives the reference answer on 6 of 6 workloads (5 of 6 before).
- The F\* bundle: the run is 2.4 times faster and the load 2.1 times. Geometric mean of the
  ratio to QuickJS-NG over the five workloads that ran before: 11.3 to 9.2; over all six
  after: 8.4.
- QuickJS-NG's time for pako in this run (165 ms) is an outlier; two other runs of the same
  night gave 94 and 96 ms, which puts pako at about 31 times QuickJS-NG, as in section 6.2.
- Profile of the F\* bundle after (`perf`, self time, size 4N): `vmLoop` 24.8%, allocate and
  free 16.4%, page clearing in the kernel 5.3%, `lean_dec_ref_cold` 5.0%, `evalExpr` 3.2%.
  `Env.scan` is not in the first 40 lines. At size 0 (load): `vmLoop` 10.0%,
  `lean_dec_ref_cold` 8.9%, allocate and free 17.7%, `punctFrom` (the lexer's punctuator
  match) 7.8%, `memcmp` 3.8%. Before, `memcmp` and string equality were 44% of the load and
  the parser's per-block filter 7.9%.

Single causes, CPU seconds before and after:

| Script | before | after |
|---|---|---|
| 300,000 reads of `Math.abs` in an inner function of a function with 10,000 `var` names | 7.27 | 0.32 |
| the same with `typeof` of an absent name | 7.22 | 0.16 |
| 40,000 `var` declarations in one function | 3.13 | 0.25 |
| 40,000 function declarations in one function | 3.69 | 0.52 |
| `s += 'x'` 400,000 times in a function | 2.32 | 0.09 |
| `s += i` 400,000 times in a function | 27.6 | 0.10 |
| `s += 'x'` 400,000 times at the top level of a script (the variable is a global) | 2.50 | 2.57 |

- The last line is not repaired: at the top level the register machine reads the global into a
  register, adds and writes back, so the string has two holders at the add. The evaluator's
  `dropNameStr` has no counterpart in `vmLoop`.
- Test262 (6,301 files of `test/language`): 5,633 pass, 664 fail, 4 skip; before 5,629 pass,
  668 fail. Each verdict is equal or better (4 tests of a function expression's name pass now).
- Gates on the tree at `195096766`: `lean-tail-recursion-audit.py --gate`,
  `lean-hygiene-audit.py`, `lean-csimp-reach.py --gate`, `lean-unbuilt-modules.py --gate`: exit 0.
- Not done on this tree: a native build of the engine (`build-web-render.sh --native`) and
  `test.sh`. `lake build leanjs L4Factoidal.JS` passes, with the 91 scripts and the suite of
  `JS/Tests.lean`.

## 7. Integers through GMP

### 7.1 What was found

callgrind showed `__gmpz_set_str` (GMP reads a number from decimal text) under ordinary
JavaScript operations and under font loading. Mechanisms, on every tree:

1. **`Float.ofNat`, `Float.ofInt`, `Nat.toFloat`.** In Lean 4.33.1, `Float.ofNat n` is
   `Float.ofScientific n false 0` (`Init/Data/OfScientific.lean`), whose first test is
   `m < 2 ^ 53`. The compiler writes a `Nat` literal of 2^32 or more as
   `lean_cstr_to_nat("9007199254740992")`. So each call makes a GMP number from text and
   frees it. A JavaScript engine with `Float` numbers and `Nat` sizes converts all the time:
   the bounds test of `a[i]`, `.length`, `charCodeAt`, an index passed to a callback, every
   result of a bit operator.
2. **`Float` literals left in a function body.** `0.5` is a `Float.ofScientific` call, and
   `0` or `-1` typed `Float` is `Float.ofNat` through the `OfNat` instance. The compiler moves
   a literal to start-up code in some functions and leaves it in others (`k < 0` in the native
   functions of `JS/Interp.lean`, `19.2` in `Layout.inlineLayout`).
3. **`Int` above 31 bits.** A Lean `Int` is a machine scalar only from -2^31 to 2^31 - 1
   (`LEAN_MAX_SMALL_INT` in `lean.h`; a `Nat` is one up to 2^63 - 1). `ToInt32` and `ToUint32`
   were `(truncInt x) % 4294967296` on `Int`: the modulus is a GMP number, so each is
   `lean_int_big_emod`. One `i | 1` ran three of them and three text parses: about 4,500 of
   its 7,100 instructions on stage A.
4. **A literal in the slow case.** A `Float` literal with an exponent above 22 or a mantissa of
   2^53 or more takes the slow case of `Float.ofScientific`, big number arithmetic.
   `Number.isSafeInteger(x)` has `9007199254740991.0` in its body: 28,612 instructions a call
   against 11,796 for `Number.isInteger(x)`. `1e300` in `WebPaint.cullCurve` was 85% of a
   frame (commit `57fe3531d`, another session, the same day).

In compiled Lean alone (`bubblepop_perf/lean/IntConversions.lean`, `run.sh` beside it; three
runs of 3 M iterations): `Float.ofNat n` 52 to 55 ns; `n.toUInt64.toFloat` 10 to 15;
`Float.ofInt i` 55; `ToInt32` on `Int` 45 to 47; `x.toInt64.toInt32` 2.2; a test
`n < 9007199254740992` (the literal alone) 39 to 40.

Upstream: Lean issue 16007 and its pull request 16015, as recorded in
[2026-11-09-lean-upstream-wasm32.md](2026-11-09-lean-upstream-wasm32.md) (literals from 2^32 to
2^64 - 1 read from a string each time). With that repair in the toolchain, mechanisms 1 and 2
cost nothing; mechanism 3 stays.

### 7.2 The repair on this branch

- `formal/lean4/L4Factoidal/Prim/FloatOfNat.lean`: `natToFloat`, `intToFloat` and
  `ofScientificFast`, with `natToFloat_eq`, `intToFloat_eq` and `ofScientificFast_eq` for every
  argument, and six `@[csimp]` theorems: for `Float.ofNat`, `Nat.toFloat`, `Float.ofInt`,
  `Float.ofScientific`, and for the instances `instOfNatFloat` and `instOfScientificFloat`.
  For a number below 2^32 a twin is the fast case of the core function with a bound that is a
  small literal, so the proof only unfolds both sides: it uses no fact about `Float`
  arithmetic. Three mutants of the twins are each rejected by the proofs and by the guards.
- `JS/Number.lean`: `toInt32Fast` and `toUint32Fast` on `Float.toInt64` and `Int64.toInt32`,
  proved equal to `toInt32` and `toUint32` for every `Float` (`toInt32_eq_fast`,
  `toUint32_eq_fast`, through `Int64.toInt_toInt32` and `Int.bmod`), each a `csimp`. The `Int`
  definitions stay as the specification; `toInt32_range` and `toUint32_lt` are about them.
  Named constants `twoPow53F`, `tenPow21`, `posZero`, `negZero`.
- `JS/Lexer.lean`: `floatOfNatFast`, proved equal to `floatOfNat`, a `csimp`.
- Imports of `Prim.FloatOfNat` in `Rendering/FontProvider.lean`, `Rendering/SfntOutline.lean`,
  `Rendering/SfntProfile.lean` and `labs/demos/foafnaut/SVG.lean`. `JS/Interp.lean` and
  `JS/Value.lean` are not edited: the `csimp` theorems change their compiled code through the
  import of `Lexer`. So this branch touches no file that stage A or B changes.
- All 15 theorems: axioms `propext`, `Classical.choice`, `Quot.sound`.

**Why six theorems.** The compiler replaces a name where the source of an importing module
says it. A body that core compiled keeps the core conversion. With the theorems for
`Float.ofNat` and `Float.ofInt` only, the generated C of `JS/Interp.c` still had 29 core
conversions: `len.toFloat` (`Nat.toFloat` is a core `abbrev`) and integer-style `Float`
literals (`k < 0`, `.num (-1)`: the core `OfNat` instance). With all six: 0 in `Interp.c` and
`Lexer.c`; 16 in `Date.c`, which does not import the module.

**What it does not reach.** A literal in the slow case goes to core through the twin
(`Number.isSafeInteger`). A `Float` literal with a mantissa of 2^32 or more still reads it
from text (`4294967296.0` in `putV`). Modules that do not import the twins.

### 7.3 Tools

- `tools/lean-literal-parse-audit.py` reads the generated C. Default: `Nat` literals of 2^32
  or more outside start-up code. `--float-literals`: every `Float` literal converted outside
  start-up code, through core or through the twin, with what it costs (`no parse`, `parse`,
  `slow case`). `--conversions`: `Float.ofNat` and `Float.ofInt` calls that are still the core
  ones. It lists; it is not a gate.
- `tools/test_lean_literal_parse_audit.py`: 7 cases, one of which compiles a small Lean file
  with the pinned toolchain and checks that the tool finds the known sites. It fails when the
  compiler stops writing these literals as text: the sign that the twins can go.
- `tools/lean-csimp-reach.py`: a theorem whose left side is a Lean core definition has no C
  symbol in this tree; the gate prints it as `CORE` and does not audit its reach
  (`CORE_LEFT_SIDES`; 2 cases and 3 mutants in its self-test). `toInt32Fast`, `toUint32Fast`
  and `floatOfNatFast` call their specifications in the slow branch: three lines with the
  reason in `tools/lean-csimp-reach-allow.txt`. Without them the gate fails.

### 7.4 Checks

On `489d5cd3a` against this branch (`f178e43c1`), unless a line says otherwise:

- Test262 (the tree's 6,301 files of `test/language`): 5,627 pass, 670 fail, 4 skip on both;
  the verdict of every file is the same. On stage A and stage B with the first form of the
  conversions: 5,629 pass, 668 fail, 4 skip, every verdict the same as without.
- The differential script of 6.4: 1,671 lines, the same on both.
- The real-world workloads: the same `RESULT` lines on both (5 of 6 run).
- The engine: for ten pages, the packed bytes at 1600 by 1000 with Noto Sans and the text
  answer at 1280 by 800: 20 of 20 files the same, 20,965,877 bytes.
- Gates on this branch's build (the engine's module closure and `leanjs`, not the whole
  tree): `lean-csimp-reach.py --gate` exit 0; `lean-hygiene-audit.py` clean (`partial def`
  163, the baseline); `lean-unbuilt-modules.py --gate` exit 0 (1,662 modules reached);
  `lean-tail-recursion-audit.py --gate` exit 0. `test_lean_csimp_reach.py`: 31 synthetic cases
  pass, 20 of 20 mutants killed; its real-build cases were NOT RUN (they need the full build).

### 7.5 Effect on BubblePopJS

Instructions for one operation on `main` (callgrind, N = 20,000), unchanged and with this branch, and CPU ns
for the same operation on `main` and on stage B (stage B with the first form of the conversions):

| Operation | Instructions before | after | ratio | main ns | main + branch ns | stage B ns | stage B with the conversions ns |
|---|---|---|---|---|---|---|---|
| `s = i \| 1` | 8,356 | 3,667 | 2.28 | 536 | 236 | 394 | 92 |
| `s = i ^ 5` | 8,358 | 3,669 | 2.28 | 529 | 243 | 373 | 94 |
| `s = i & 255` | 8,355 | 3,669 | 2.28 | 515 | 234 | 368 | 100 |
| `s = a[i & 7]` | 10,126 | 4,783 | 2.12 | 687 | 339 | 433 | 121 |
| `s = i << 1` | 8,488 | 4,529 | 1.87 | 542 | 303 | 398 | 158 |
| `s = i >>> 1` | 7,500 | 4,399 | 1.70 | 486 | 306 | 332 | 148 |
| `s = i >> 1` | 6,813 | 4,442 | 1.53 | 440 | 277 | 298 | 152 |
| `s = ~i` | 4,676 | 3,087 | 1.51 | 315 | 242 | 161 | 65 |
| `s = t.length` | 3,497 | 2,724 | 1.28 | 228 | 178 | 58 | 18 |
| `s = a[3]` | 3,739 | 2,948 | 1.27 | 231 | 186 | 79 | 27 |
| `s = a.length` | 3,800 | 3,045 | 1.25 | 258 | 202 | 59 | 19 |
| `s = i % 7` | 4,428 | 3,653 | 1.21 | 284 | 266 | 153 | 98 |
| `s = t[3]` | 4,877 | 4,077 | 1.20 | 359 | 275 | 187 | 136 |
| `s = 'k' + i` | 5,562 | 4,762 | 1.17 | 404 | 320 | 249 | 179 |
| `a[3] = i` | 5,952 | 5,152 | 1.16 | 400 | 368 | 195 | 175 |
| `s = t.charCodeAt(3)` | 7,203 | 6,441 | 1.12 | 556 | 474 | 416 | 362 |
| `s = String(i)` | 7,762 | 6,976 | 1.11 | 570 | 479 | 320 | 260 |
| `s = function () { return i; }` | 10,464 | 9,690 | 1.08 | 1309 | 1314 | 1049 | 968 |
| `s = Math.floor(i)` | 6,803 | 6,794 | 1.00 | 485 | 493 | 298 | 270 |
| `s = [i, k, 1]` | 4,777 | 4,777 | 1.00 | 361 | 386 | 160 | 167 |
| `s = s * k` | 3,363 | 3,363 | 1.00 | 221 | 210 | 15 | 17 |
| `s = s + k` | 3,322 | 3,322 | 1.00 | 204 | 214 | 18 | 15 |
| `s = s - k` | 3,321 | 3,321 | 1.00 | 178 | 196 | 18 | 16 |
| `s = g1(i)` (top-level function) | 10,283 | 10,288 | 1.00 | 848 | 912 | 166 | 150 |

The number of allocations does not change for any operation. The ns columns are one run each;
a difference under 10% there is not a result (`s = g1(i)` shows 848 and 912 with the same instruction count).

## 8. The execution model: two measurements

**The first** (before stage B was read): is the distance to QuickJS-NG a cost of Lean, or of
walking a tree with a result object for each node? Three programs in Lean run
`var s = 0; for (var i = 0; i < n; i++) s = s + i`
(`bubblepop_perf/lean/VmFloor.lean`; 3 M iterations, five runs): a tree walk in `EStateM` with
boxed values 128 to 150 ns for one iteration; the same as pure functions 130 to 140; register
bytecode with numbers in a `FloatArray` 12.5 to 14.5. The monad is not the cost. Stage B is
that step, built by another session: its loop of the same shape is 66 ns.

**The second**: what remains between stage B and QuickJS-NG?
`bubblepop_perf/lean/CoreModel.lean` has values as 64-bit words in a `ByteArray`, code as
32-bit words, inline caches in the code, objects with a shape word, calls on the register
file. It is a model of fast paths, with their tag, shape and bounds tests, and no engine.
Quiet machine, 3 M iterations, three runs:

| | Core model, median of 5 [range] | Core model with Lean's own bit conversions, 3 runs | QuickJS-NG | V8 no JIT | Stage B |
|---|---|---|---|---|---|
| the loop `i < n; i++`, ns for one iteration | 7.6 [7.3 to 7.6] | 10.6 to 13.0 | 7 | 8 | 48 |
| `s = s + k`, less the loop | 1.9 [1.8 to 2.2] | 4.2 to 6.3 | 2 | 2 | 18 |
| `s = o.x` (inline cache) | 3.3 [2.9 to 9.4] | 3.0 to 4.9 | 7 | 5 | 27 |
| `o.x = i` (inline cache) | 3.4 [2.8 to 8.3] | -0.4 to 3.0 | 6 | 2 | 86 |
| `s = g1(i)` (call and return) | 7.1 [5.9 to 9.4] | 6.3 to 11.8 | 15 | 12 | 165 |
| `s = { x: i, y: k }` (no collector) | 4.4 [3.5 to 4.8] | 1.4 to 4.8 | 66 | 13 | 411 |
| `fib(30)`, ns for one call | 17.3 [16.3 to 18.8] | 23.8 to 25.7 | 23.4 | 23.0 | 145 |
| instructions: loop, add, property read, call | 153, 46, 78, 139 | 224, 83, 78, 145 | | | 972, 329, 475, 2,558 |

The first column casts between a number and its word with one inline C instruction. The second
uses `Float.toBits` and `Float.ofBits`, which in Lean 4.33.1 are calls into the runtime (5 in
one loop iteration). The second run of the five had other work on the machine (the two high
ends of the property rows).

`fib(30)`, CPU ns for one call of `fib`: `main` 752, stage A 293, stage B 145, QuickJS-NG
23.4, V8 with no JIT 23.0, V8 3.5.

The plan ([2026-11-09-bubblepopjs-plan.md](2026-11-09-bubblepopjs-plan.md)) is built on this.

## 9. The native build of BubblePopKit

### 9.1 Times on this VM (at `036198f2`)

Status page is `labs/demos/foafnaut/web-render/fixtures/status.html`. 1600 by 1000, Noto Sans,
milliseconds; the frame is the median of 8.

| Page | First compile | Frame, checks on | Frame, `"checks":false` |
|---|---|---|---|
| index | 130 | 43 | 18 |
| status | 145 | 71 | 26 |
| showcase | 136 | 69 | 25 |
| showcase-tables | 88 | 25 | not run |
| timers-and-clicks | 9.9 | 3.4 | not run |
| showcase-dataviz | 214 | 67 | not run |

### 9.2 Start: 1,109 M instructions before `main` (at `036198f2`)

`web-render-native` with no argument: 0.11 s, 60 MB. Every module's constants are computed at
start. By inclusive cost: `LeanJS.snapshotData` 740 M (it runs the BubblePopJS page prelude and
encodes the realm; only `bubblepop-realm`, a build tool, reads it); the scene shader text about
190 M; the XSLT 4 and XPath 4 tables 86 M (function signatures 74 M, an ixml grammar 35 M); the
IDNA table 60 M; Unicode normalisation 55 M and segmentation 28 M; a regular expression category
table 56 M.

`wip/bootstack` makes `snapshotData` a function of `Unit` (found there first, for the Hub). It
is not on `main` at `489d5cd3a`. With that one change this start is 369 M instructions, 0.03 s
and 44 MB (measured here on `036198f2`, then taken out of this branch as a duplicate).

### 9.3 Font load and first compile of the status page: 2,251 M instructions (at `036198f2`)

Start 1,109 M, then the compile 1,142 M:

| Phase | M instructions | Share of the compile |
|---|---|---|
| layout (`WebDocument.layOut`) | 889 | 78% |
| of which shaping 364 words (`SfntProfile.Font.word`) | 722 | 63% |
| of which GSUB and GPOS (`SfntShape.shape` 416, `SfntGpos.position` 289) | | |
| of which kerning coverage (`SfntKern.coverage`, 42,395 calls) | 144 | 13% |
| of which 1,852 glyph outlines (`SfntOutline.outline`) | 165 | 14% |
| block and inline layout (`Layout.layoutTask`) | 68 | 6% |
| the frame (`WebRender.artifactWith`) | 244 | 21% |

A word costs about 2 M instructions to shape. Decimal parses of 2^53 in the whole run: 360,928
(`Float.ofNat` 359,009: `FontProvider.fromInt` 128,592, `SfntOutline.ofInt` 96,808,
`SfntProfile` 93,490, the JavaScript lexer 18,786 at start, `writeFixed` 11,760), about 235 M
instructions, 10%. `wip/bootstack` has a binary search for `SfntKern.coverage`.

### 9.4 One frame on a kept layout: 249 M instructions (at `036198f2`)

Status page, 2,940 primitives, 401,060 floats, `"checks":false`:

| Phase (inclusive) | Share |
|---|---|
| `Scene.jsonWith`: the float32 bytes of the scene (`float32BytesFast`, `Primitive.writeRows`) | 39% |
| `WebRenderSVG.toScene`: the scene made again from the layout (`Scene.make`, `compilePrimitive`) | 32% |
| `WebRender.layoutJSON`: boxes and glyph runs as text | 19% |
| of which `lean_float_to_string` (14,287 calls, 2,342 instructions each, through `printf`) | 13% |
| `Scene.tiles` | 9.5% |

| Function (self) | Share | Calls in a frame |
|---|---|---|
| `lean_dec_ref_cold`, `mi_free`, `mi_malloc_small` and the rest of allocate and free | 27% | 781,721 allocations |
| `lean_byte_array_push` | 10.3% | 1,716,945 |
| `printf` float to text and its helpers | 9.7% | 14,287 |
| `NativeSVGCurves.flatten` | 5.1% | 4,146 |
| `List.lengthTR` | 3.1% | 66,015 |
| `lean_apply_2` | 3.0% | 175,952 |

With checks on (the default of a request) a frame is 2.6 times as long: the probe pixels are
sampled on the CPU (`NativeSVG.pathHitFast` 9.4% of that profile).

### 9.5 Before and after this branch (two builds of `489d5cd3a`)

Status page, callgrind, M instructions:

| | `main` (`489d5cd3a`) | this branch | change |
|---|---|---|---|
| start (no argument) | 1,115.7 | 1,096.5 | -1.7% |
| start, font load and first compile | 2,328.2 | 2,050.9 | -11.9% |
| of which the compile (less the start) | 1,212.6 | 954.4 | -21.3% |
| one frame on a kept layout | 286.0 | 277.0 | -3.1% |
| decimal parses of a literal (`lean_cstr_to_nat` calls), start to first compile | 361,853 | 2,612 | |
| the same after 4 more frames | 408,785 | 2,612 | |
| calls of the twin `natToFloat`, start to first compile | 0 | 358,945 | |

Wall milliseconds, 1600 by 1000, Noto Sans, `"checks":false`; six processes for each build,
interleaved; first compile is the least of the six, the frame is the least and the largest of
the six medians of 8 frames:

| Page | First compile, `main` | this branch | ratio | Frame, `main` | this branch |
|---|---|---|---|---|---|
| index | 89.3 | 74.0 | 1.21 | 21.4 to 29.2 | 20.9 to 27.2 |
| status | 105.9 | 91.6 | 1.16 | 29.9 to 41.5 | 29.7 to 39.3 |
| showcase | 92.1 | 80.6 | 1.14 | 27.6 to 35.8 | 27.0 to 36.2 |
| showcase-dataviz | 116.1 | 103.3 | 1.12 | 20.1 to 26.3 | 19.9 to 26.1 |
| showcase-tables | 48.6 | 39.4 | 1.23 | 11.5 to 16.1 | 10.8 to 14.3 |

The frame does not change within the spread between processes. The answers are the same,
byte for byte (section 7.4). The start does not change: its 740 M instructions are the constant
of 9.2.

## 10. Literals and conversions that the generated C still evaluates at each call

`python3 tools/lean-literal-parse-audit.py`, on the generated C of two builds of `489d5cd3a`
(the engine's module closure, 382 C files; and the 51 lab modules):

| | `main`, library | this branch, library | `main`, lab modules | this branch, lab modules |
|---|---|---|---|---|
| `Nat` literals of 2^32 or more read from text, sites outside start-up code | 54 (in 48 functions of 29 files) | 54 | 9 | 9 |
| `Float.ofNat` and `Float.ofInt` calls that are the core ones (`--conversions`) | 267 in 28 files | 61 in 16 files | 186 in 16 files | 53 in 7 files |
| `Float` literals converted outside start-up code (`--float-literals`) | 116, all through core | 111: 77 through core, 34 through the twin | 33, all through core | 33: 15 through core, 18 through the twin |

What stays on this branch is in modules that do not import `Prim.FloatOfNat`. Core conversions:
`JS/Date.c` 16, `Rendering/TableLayout.c` 10, `Rendering/Scene.c` 8, `Rendering/Style.c` 7,
`Rendering/MediaQuery.c` 4, and in the lab modules `WebSparql.c` 26, `ImageJPEG.c` 10,
`Graphics.c` 8, `SVGCurves.c` 5. `Float` literals through core: `XSLT4/Static.c` 17,
`WasmVM/Numerics.c` 16, `Rendering/Style.c` 10, `XPath4/Atomic.c` 7. One literal is in the slow
case: `9007199254740991.0` in `JS.callNative` (`Number.isSafeInteger`).

Sites of `Nat` literals in loops or on per-item paths, from the first run of the session (at
`036198f2`): `ImageJPEG` (`cosines`, a literal inside the loop), `SVG.transformFunction` (pi for
each `rotate` or `skew`), `SVGText.lowerSfnt` (pi inside a loop), `WasmVM.Num.inI32` and `inU32`
and the `trapUn` conversions (float to integer instructions), `WasmVM.step` (two sites).

An import is one line and costs nothing at run time. This branch adds it where a profile
showed the cost (fonts, the JavaScript engine, SVG). How often the other sites run was not
measured.

## 11. What this branch changed

- New: `formal/lean4/L4Factoidal/Prim/FloatOfNat.lean`;
  `labs/demos/foafnaut/bubblepop_perf/opcost.py`, `realworld.py`, `realworld/` (manifest,
  prelude, 6 drivers) and `lean/` (`IntConversions.lean`, `VmFloor.lean`, `CoreModel.lean`,
  `run.sh`); `tools/lean-literal-parse-audit.py` and its test; this record and the plan.
- Changed: `JS/Number.lean`, `JS/Lexer.lean` (twins, constants); three `Rendering` modules and
  `labs/demos/foafnaut/SVG.lean` (one import each); `WasmVM/Bench/Page.lean` (one import, so
  that `wasmvm-bench` builds); `tools/lean-csimp-reach.py`, its test and
  its allow list; the `foafnaut` and `lean4-performance` skills; `CLAUDE.md` (what Foafnaut
  is); the worknote index; the csimp reach record; the handoff records.
- Not changed up to `b46cfa7d5` (2026-11-09): `JS/Interp.lean`, `JS/Value.lean`, and every
  file that stage A, stage B or `wip/bootstack` changes.
- From `94906aebc` (2026-11-10): `main` at `0fee0a14f` and stage B (`wip/bpperf-vm` at
  `167605f4c`) are merged into this branch, and the repairs of section 6.6 change `JS/Lexer.lean`,
  `JS/Parser.lean`, `JS/Syntax.lean`, `JS/Resolve.lean`, `JS/Compile.lean`, `JS/Interp.lean`,
  `JS/Value.lean`, `JS/Number.lean`, `JS/Snapshot.lean`; new `JS/RegressionTests.lean`. The
  owner of stage A and B said that the work after their landing belongs to this session
  (`CLAUDE.md`, the Foafnaut section).
- Not on `main`: the owner's instruction for the night was to commit on branches only.

## 12. Next

BubblePopJS: the plan, section 8. Its first items come from this record: captured variables
by slot (6.3), the defects of 6.4, typed arrays with no key string, the regression of 5.3,
the literals of 5.3 and 7.1. Done on 2026-11-10 (section 6.6): defects 1, 2, 8, 9, 10, the
name scan, the literals of 5.3. Open: defects 3 to 7, typed arrays (pako is still about 31
times QuickJS-NG), `s += v` on a global in a compiled top-level loop, captured variables in
compiled code, allocation (16 to 26% of every profile).

For BubblePopKit, in order of measured share:

1. Write the scene's float32 values four bytes at a time into a buffer with its capacity set:
   `lean_byte_array_push` is 10.3% of a frame.
2. Keep the lowered scene and its bytes with the kept layout (named in
   [2026-11-07-foafnaut-frame-pipeline.md](2026-11-07-foafnaut-frame-pipeline.md)): `toScene`
   and `jsonWith` are 71% of a frame on a kept layout.
3. Float to text through `printf` is 13% of a frame: a binary form for the layout answer, or
   the cached formatter of `Rendering.FloatFormat`.
4. First compile is shaping, 2 M instructions for each word: `SfntGpos.posAt` (30,975 calls,
   243 M) after `wip/bootstack`'s `SfntKern.coverage`.
5. Start: land `wip/bootstack`; then the tables of 9.2 as `Thunk`s read where they are used.
6. The sites of section 10 that are in loops.

## 13. Not measured

- Anything on a Mac: the window, the GPU draw, Deno, FFI calls, input latency, the Hub.
- The Wasm build of BubblePopKit, and BubblePopJS in it. BubblePopWASM beyond section 6.5.
- Page scripts in real pages (DOM calls through the host), WPT run times.
- The engine's layout on real sites (see
  [2026-11-09-real-site-layout-speed.md](2026-11-09-real-site-layout-speed.md)).
- How often each site of section 10 runs.
- The whole Lean tree was not built here: the engine's closure (382 modules), the lab modules
  and `leanjs`. CI's full build decides the gates.
- Test262 beyond the 6,301 files in the tree; any `test/built-ins` file.
