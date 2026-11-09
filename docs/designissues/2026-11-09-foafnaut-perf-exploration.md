# Foafnaut performance exploration: BubblePopJS and the native engine (2026-11-09)

> DRAFT, 2026-11-09 23:05 UTC. This text is being rewritten on this branch. Sections 2, 9, 11
> and 12 were written before the branches `wip/bpperf-vm` and `wip/bootstack` were read: they
> have placeholders (`SEE-...`) and two statements that are wrong (the start-up constant is
> repaired on `wip/bootstack`, not here; the register machine of section 12 exists on
> `wip/bpperf-vm`). The next commit on this branch replaces them.

Owner, 2026-11-09, verbatim: "spend your first session working on a deep dive hands-on,
measurement driven exploration of our perf bottlenecks, especially around our native builds
(esp OSX) and ourJavascript engine. BubblePopJS."

This record holds the method, every number, what this session changed, and a ranked list of
what to do next. Skill: [skills/foafnaut/SKILL.md](../../skills/foafnaut/SKILL.md), section
"Measure the engine and BubblePopJS with no Mac". Lean rules that came out of it:
[skills/lean4-performance/SKILL.md](../../skills/lean4-performance/SKILL.md), sections
"Integers through GMP" and "A definition with no argument runs when the program starts".

## 1. Limits of this record

- Machine: a Linux x86_64 cloud VM (Ubuntu 24.04, 4 virtual CPUs, 15 GB), Lean 4.33.1, the
  engine built by `build-web-render.sh --native` (`leanc -O3 -DNDEBUG`). **Not a Mac.** Nothing
  here measures the macOS window, Cocoa, the GPU, Deno, the FFI boundary or the Hub. The CPU
  work of the engine is the same Lean code on both machines; the times are not.
- `perf` on this VM has no hardware counters (`-e cpu-clock` only). Exact figures are
  instruction counts from `valgrind --tool=callgrind`; times are wall or CPU time, least of 3.
- Sources: `main` at `036198f2`, and the branch `wip/bpperf` at `e8d2a3e6e`, both of
  2026-11-09. `wip/bpperf` is the BubblePopJS speed work of another session, of the same day,
  not on `main` (its own record is section 18 of
  [2026-11-08-lean-js-engine.md](2026-11-08-lean-js-engine.md) on that branch). Each
  BubblePopJS number below names its source.
- Comparison engines, all native on the same VM: QuickJS-NG `v0.18.0` (`d7215b0a`, built with
  `cc -O2`), and Node 22 (V8) with `--jitless` and with its JIT.

## 2. Results

1. On `main`, BubblePopJS is 15 to 83 times slower than QuickJS-NG on single operations, five
   common operations are quadratic, and each call keeps 330 to 500 bytes for good.
2. `wip/bpperf` repairs the five quadratic operations and the memory kept by calls, and is 1.4
   to 3.5 times faster than `main`. This session confirms those results on another machine with
   another benchmark set. It is 9 to 61 times slower than QuickJS-NG on single operations.
3. A cost that neither tree had seen: integers went through the big number runtime (GMP).
   Every `Float.ofNat` call in Lean 4.33.1 reads the number 2^53 from decimal text, and every
   JavaScript bit operator ran three GMP remainders. Repaired in this landing with proved
   twins. JavaScript `|`, `&`, `^`: 2.2 times fewer instructions; `a[i & 7]`: 2.0 times; the
   engine's font load and first compile of the status page: SEE-SECTION-9 fewer instructions.
4. The native engine ran 1,109 M instructions before `main` (0.11 s). 740 M were one constant
   that only a build tool reads. Repaired in this landing.
5. For one loop iteration, BubblePopJS on `wip/bpperf` runs 2,555 instructions and makes 10
   heap allocations. A register bytecode loop with unboxed numbers, written in Lean, runs the
   same loop in 13 ns against 133 ns for a tree walk of the present shape and 18 ns for
   QuickJS-NG. The gap to QuickJS-NG comes from the execution model, not from Lean.
6. Objects are never freed (no collector): 330 bytes for each small object on both trees.
7. A frame of the status page on a kept layout is 249 M instructions: 28% writes floats into
   a byte array one byte at a time, 28% builds the scene again, 19% writes layout text (13% is
   float to decimal text), 27% of all of it is allocate and free.

Ranked next steps: section 12.

## 3. Method

### 3.1 Benchmarks

- **Programs** (26 files, each reads a global `N`): one engine operation each, in a function
  unless the name says global. Run at N, 2N and 4N. Net time is wall time less the engine's
  start (4.6 ms BubblePopJS, 2.4 ms QuickJS-NG, 23 to 26 ms Node). The exponent `k` in
  time ~ N^k comes from the N and 4N points.
- **Single operations** (59): `labs/demos/foafnaut/bubblepop_perf/opcost.py`. Each is the body
  of one loop. The cost is the slope of the time between N and 5N, less the slope of the empty
  loop. `--callgrind` gives instructions, heap allocations (`mi_malloc_small` calls) and calls
  into the big number runtime, each for one iteration.
- Commands (engines as `NAME=CMD`):

      python3 labs/demos/foafnaut/bubblepop_perf/opcost.py \
        bubblepop='formal/lean4/.lake/build/bin/leanjs run' qjs=/path/qjs v8-jitless='node --jitless'
      python3 labs/demos/foafnaut/bubblepop_perf/opcost.py --callgrind \
        bubblepop='formal/lean4/.lake/build/bin/leanjs run'

### 3.2 The engine

`labs/demos/foafnaut/.build/web-render/web-render-native PAGE 1600 1000 --document-bin REQ FONT OUT COUNT`
loads Noto Sans, compiles the page once and then COUNT times more with a field `repeat` that
makes each call its own. `REQ` is
`{"op":"render","url":"https://example.invalid/","resources":[],"commands":[],"checks":false}`.
callgrind at COUNT 0, 1 and 4 separates: start, font load and first compile (COUNT 0); one frame
on a kept layout ((COUNT 4 - COUNT 1) / 3).

## 4. BubblePopJS on `main` (036198f2)

Net milliseconds at the largest size, and ratios. `qjs` is QuickJS-NG, `v8jl` is
`node --jitless`.

| Program | N | main | branch | qjs | v8jl | main/qjs | branch/qjs | main/branch |
|---|---|---|---|---|---|---|---|---|
| arith (`* / %` and bit operators) | 400,000 | 1,568 | 1,157 | 18.8 | 14.7 | 83 | 61 | 1.4 |
| array_index_write | 800,000 | 1,617 | 1,091 | 32.1 | 45.1 | 50 | 34 | 1.5 |
| loop_global_var | 800,000 | 908 | 429 | 13.5 | 12.2 | 67 | 32 | 2.1 |
| global_fn_call | 800,000 | 1,480 | 597 | 22.8 | 17.7 | 65 | 26 | 2.5 |
| array_index_read | 1,200,000 | 913 | 558 | 21.4 | 24.5 | 43 | 26 | 1.6 |
| deep_scope (8 scopes up) | 1,200,000 | 725 | 278 | 12.6 | 15.7 | 58 | 22 | 2.6 |
| empty_loop | 2,000,000 | 625 | 274 | 14.8 | 16.0 | 42 | 19 | 2.3 |
| closure_call | 800,000 | 1,063 | 418 | 23.2 | 24.3 | 46 | 18 | 2.5 |
| string_index (`charCodeAt`, `s[i]`) | 600,000 | 1,030 | 731 | 42.2 | 24.5 | 24 | 17 | 1.4 |
| call_args | 800,000 | 1,336 | 437 | 26.8 | 32.9 | 50 | 16 | 3.1 |
| loop_fn_var | 1,600,000 | 797 | 351 | 28.6 | 24.3 | 28 | 12 | 2.3 |
| try_catch | 800,000 | 909 | 617 | 54.5 | 38.7 | 17 | 11 | 1.5 |
| method_call | 800,000 | 1,228 | 470 | 42.9 | 33.4 | 29 | 11 | 2.6 |
| prop_rw | 1,200,000 | 850 | 374 | 34.9 | 25.5 | 24 | 11 | 2.3 |
| fib(20), 24 times | 24 | 404 | 132 | 12.7 | 15.2 | 32 | 10 | 3.1 |
| loop_fn_let | 1,200,000 | 926 | 267 | 25.8 | 17.1 | 36 | 10 | 3.5 |
| class_new | 400,000 | 1,268 | 722 | 69.7 | 31.2 | 18 | 10 | 1.8 |
| obj_alloc | 800,000 | 829 | 518 | 57.0 | 20.4 | 15 | 9.1 | 1.6 |
| string_concat | 400,000 | 2,361 | 313 | 46.5 | 60.4 | 51 | 6.7 | 7.6 |
| regex | 400,000 | 849 | 730 | 157 | 63.1 | 5.4 | 4.6 | 1.2 |
| array_push | 80,000 | 4,920 | 39.8 | 3.5 | 7.6 | 1,406 | 11 | 124 |
| array_methods | 80,000 | 4,883 | 88.9 | 10.3 | 7.2 | 474 | 8.6 | 55 |
| dict_build (one object, N keys) | 40,000 | 9,639 | 56.1 | 12.9 | 35.5 | 747 | 4.3 | 172 |
| json | 40,000 | 2,775 | 232 | 69.3 | 27.7 | 40 | 3.4 | 12 |
| map_set | 80,000 | 12,749 | 139 | 111 | 15.2 | 115 | 1.3 | 92 |

**Quadratic on `main`** (exponent `k`; 1.0 is linear): `array_push` 2.07, `array_methods`
1.98, `dict_build` 2.09, `json` 2.09, `map_set` 2.53, `string_concat` 1.64. At N = 100,000:
`a.push(i)` 9.9 s, `o['k'+i] = i` 62.8 s, `m.set(i, i)` 23.3 s, JSON of 100,000 objects 28.6 s.
Causes, read in the source: `Array.prototype.push` builds `es ++ args` from a copy of the
elements that the object still holds; `collPut` reads `es.size` after `es.push`, so the push
copies; `Obj.putOwn` reads `o.props.contains` after `o.props.insert`, so the insert copies the
bucket array. On `wip/bpperf` every exponent is 0.9 to 1.04.

**Memory kept on `main`** (peak RSS growth for each iteration; nothing frees it):
a call 334 to 494 bytes (800,000 calls: 267 to 388 MB), a `for (let ...)` iteration 315
bytes, a small object 458 bytes, `new` and one method call 897 bytes. QuickJS-NG and V8: 0.

## 5. The branch `wip/bpperf` (e8d2a3e6e)

Confirmed here, on another machine and with other programs than the branch's own
`scaling.py`: the six operations above are linear; calls, blocks and `for (let ...)` loops
keep no memory (0 bytes for each call in `call_args`, `closure_call`, `method_call`, `fib`,
`loop_fn_let`); Test262 language subset 5,629 pass, 668 fail, 4 skip (out of 6,301; `main`:
5,627 pass, 670 fail, 4 skip), whole run 0.9 to 1.0 s on both.

What stays, by single operation (ns, the empty loop subtracted; `main` for comparison):

| Operation | main | branch | qjs | v8jl | branch/qjs |
|---|---|---|---|---|---|
| the loop itself (`i < n; i++`) | 358 | 157 | 9 | 12 | 17 |
| `s = 1` | 129 | 80 | 3 | 0 | 27 |
| `s = k` (local) | 148 | 87 | 3 | 0 | 33 |
| `s = s + k` | 220 | 98 | 1 | 0 | 71 |
| `s = i < k` | 206 | 102 | 4 | 1 | 24 |
| `if (i < 0) s = 2` | 91 | 42 | 4 | 0 | 9 |
| `s = i \| 1` | 659 | 491 | 4 | 0 | 123 |
| `s = i << 1` | 589 | 480 | 4 | 0 | 116 |
| `s = i % 7` | 299 | 225 | 4 | 0 | 56 |
| `s = a[3]` | 249 | 152 | 4 | 0 | 36 |
| `a[3] = i` | 454 | 206 | 5 | 6 | 45 |
| `s = a.length` | 278 | 165 | 6 | 5 | 26 |
| `s = o.x` | 216 | 99 | 6 | 0 | 18 |
| `o.x = i` | 286 | 94 | 5 | 2 | 19 |
| `s = G` (global) | 227 | 220 | 2 | 0 | 88 |
| `G = i` | 484 | 211 | 3 | 0 | 74 |
| `{ let q = i; s = q; }` | 663 | 402 | 8 | 1 | 52 |
| `s = g1(i)` (local function) | 825 | 250 | 17 | 5 | 15 |
| `s = gf(i)` (global function) | 1,064 | 373 | 14 | 4 | 27 |
| `s = o.m(i)` | 933 | 273 | 20 | 9 | 13 |
| `s = Math.floor(i)` | 587 | 427 | 20 | 2 | 22 |
| `s = t.charCodeAt(3)` | 556 | 491 | 25 | 16 | 20 |
| `s = 'k' + i` | 427 | 306 | 47 | 23 | 6.5 |
| `s = {}` | 208 | 152 | 23 | 3 | 6.4 |
| `s = { x: i, y: k }` | 821 | 521 | 65 | 6 | 8.1 |
| `s = function () { return i; }` | 1,446 | 1,040 | 132 | 16 | 7.9 |
| `s = () => i` | 775 | 585 | 100 | 10 | 5.9 |

Each cost is one run of 3 on a quiet machine; a difference under 10 ns or 10% is not a result.

Memory that stays on the branch: an object. `s = { k: i, v: i }` keeps 328 bytes (`main`: 458),
`new V(i, 1)` 314 bytes. 800,000 small objects: 263 MB. The engine has no collector (section 8
of the engine record). A page that makes 1,000 short-lived objects in each frame at 60 frames
a second would keep about 20 MB more each second.

## 6. Where the instructions go (branch)

The empty loop `for (var i = 0; i < n; i++) {}` in a function, callgrind, the difference of
N = 300,000 and N = 100,000: **2,555 instructions and 10 heap allocations for each iteration.**

| Function | Instructions | Calls |
|---|---|---|
| `evalExpr` | 615 | 2 |
| `forLoop` | 296 | (loop) |
| `assignLocal` | 274 | 1 |
| `mi_free` | 260 | 10 |
| `HeapOf.envUp` | 180 | 4 |
| `lean_dec_ref_cold` | 153 | 4 |
| `lookupLocal` | 144 | 1 |
| `mi_malloc_small` | 120 | 10 |
| `lean_alloc_ctor` | 119 | 3 |
| `evalBlock`, `evalStmt`, `evalStmts`, `enterBlock` | 216 | 1 each |
| the rest | 178 | |

Allocate, free and reference counts are about 30% of the instructions (42% of the time in a
`perf` sample). The 10 allocations are one result object for each evaluator function that
returns (`EStateM.Result`; a pure function that returns a pair costs the same, section 8) and
one box for the number. `evalExpr` alone is 307 instructions a call.

Added instructions and allocations for one operation (branch, less the empty loop):

| Operation | Instructions | Allocations | Largest parts |
|---|---|---|---|
| `s = 1` | 1,286 | 4 | `evalExpr` 307, `assignLocal` 273 |
| `s = s + k` | 1,839 | 5 | `evalExpr` 618, `assignLocal` 274 |
| `s = o.x` | 1,693 | 4 | `evalExpr` 490, `fastGet` 112 |
| `s = a[3]` | 2,484 | 4 | `evalExpr` 590, GMP 480 (section 7) |
| `s = G` | 2,648 | 5 | `Env.scan` 380, `findEnv` 250 |
| `s = i % 7` | 3,172 | 8 | GMP 304 and more (section 7) |
| `a[3] = i` | 3,565 | 6 | GMP 850 (section 7), `lookupLocal` 288 |
| `s = g1(i)` | 3,775 | 11 | `evalExpr` 572, `callBody` 345, `callClosure` 317 |
| `s = typeof i` | 3,838 | 10 | `Env.scan` 792, `memcmp` 396 |
| `{ let q = i; s = q; }` | 5,246 | 19 | free and reference counts 1,040 |
| `s = Math.floor(i)` | 5,285 | 15 | `evalExpr` 611, `callNative` 355, `Env.scan` 348 |
| `s = gf(i)` | 5,688 | 12 | `Env.scan` 728, `findEnv` 500 |
| `s = { x: i, y: k }` | 5,359 | 20 | free 1,155, `evalProps` 557 |
| `s = t.charCodeAt(3)` | 6,221 | 20 | `evalExpr` 695, GMP 480 |
| `s = i \| 1` | 7,100 | 9 | GMP about 4,500 (section 7) |
| `s = function () { return i; }` | 8,232 | 31 | free and reference counts 2,140, `makeClosure` 463 |

What the table says about the branch:

- A name that is not in a function's own scopes (`G`, `gf`, `Math`, and `typeof` of any name)
  walks the scope chain and compares names (`Env.scan`, `findEnv`): 130 ns more than a local.
  Page scripts read globals all the time (`document`, `Math`, their own top-level functions).
- A block with `let` costs 400 ns and 19 allocations.
- A function expression costs 1,040 ns and 31 allocations: the function object, its
  `prototype` object and four property writes, made at each evaluation.

## 7. Integers through GMP

### 7.1 What was found

callgrind showed `__gmpz_set_str` (GMP reads a number from decimal text) under ordinary
JavaScript operations. Three mechanisms, all present on `main` and on the branch:

1. **`Float.ofNat` and `Float.ofInt`.** In Lean 4.33.1, `Float.ofNat n` is
   `Float.ofScientific n false 0` (`Init/Data/OfScientific.lean`), whose first test is
   `m < 2 ^ 53`. The compiler writes a `Nat` literal of 2^32 or more as
   `lean_cstr_to_nat("9007199254740992")`. So each call makes a GMP number from text and
   frees it. A JavaScript engine with `Float` numbers and `Nat` sizes converts all the time:
   the bounds test of `a[i]`, `.length`, `charCodeAt`, an index passed to a callback, a typed
   array read, every result of a bit operator.
2. **`Int` above 31 bits.** A Lean `Int` is a machine scalar only from -2^31 to 2^31 - 1
   (`LEAN_MAX_SMALL_INT` in `lean.h`; a `Nat` is one up to 2^63 - 1). `ToInt32` and `ToUint32`
   were `(truncInt x) % 4294967296` on `Int`: the modulus is a GMP number, so each is
   `lean_int_big_emod`. One `i | 1` ran three of them and three text parses: about 4,500 of
   its 7,100 instructions, with 9 `malloc` and `free` pairs of GMP.
3. **Literals in function bodies.** `floatOfNat` tested `n < 2 ^ 53` with the literal read at
   each call; `numToString` evaluated `1e21`, and `%` evaluated `-0.0` or `0.0`, each a
   `Float.ofScientific` call with that same internal test.

In compiled Lean alone (`labs/demos/foafnaut/bubblepop_perf/lean/IntConversions.lean`, run by
`run.sh` beside it; `leanc -O3`, 3 M iterations, three runs):

| Form | ns a call |
|---|---|
| `Float.ofNat n` | 52 to 55 |
| `n.toUInt64.toFloat` | 10 to 15 |
| `Float.ofInt i` | 55 |
| `ToInt32` on `Int`, as `JS/Number.lean` had it | 45 to 47 |
| `x.toInt64.toInt32` | 2.2 |
| a test `n < 9007199254740992` (the literal alone) | 39 to 40 |

### 7.2 The repair in this landing

- `formal/lean4/L4Factoidal/Prim/FloatOfNat.lean`: `natToFloat` and `intToFloat`, with
  `natToFloat_eq : natToFloat n = Float.ofNat n` and `intToFloat_eq` for every argument, and
  two `@[csimp]` theorems. For `n < 2^32` the twin is the fast case of `Float.ofScientific`
  itself with a bound that is a small literal, so the proof only unfolds both sides: it uses
  no fact about `Float` arithmetic. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
- `JS/Number.lean`: `toInt32Fast` and `toUint32Fast` on `Float.toInt64` and `Int64.toInt32`,
  proved equal to `toInt32` and `toUint32` for every `Float` (`toInt32_eq_fast`,
  `toUint32_eq_fast`, through `Int64.toInt_toInt32` and `Int.bmod`), each a `csimp`. The `Int`
  definitions stay as the specification; `toInt32_range` and `toUint32_lt` are about them.
  Named constants `twoPow53F`, `tenPow21`, `posZero`, `negZero` take the literals out of the
  bodies of `toInt32Fast`, `numToString` and `jsMod`.
- `JS/Lexer.lean`: `floatOfNatFast`, proved equal to `floatOfNat`, a `csimp`.
- Imports of `Prim.FloatOfNat` in `Rendering/FontProvider.lean`, `Rendering/SfntOutline.lean`,
  `Rendering/SfntProfile.lean` and `labs/demos/foafnaut/SVG.lean`. `JS/Interp.lean` and
  `JS/Value.lean` are not edited: the `csimp` theorems change their compiled code through the
  import of `Lexer`. So this landing touches no line that `wip/bpperf` touches.
- `tools/lean-csimp-reach.py`: a theorem whose left side is a Lean core function has no C
  symbol in this tree; the gate lists it as `CORE` and does not audit its reach
  (`CORE_LEFT_SIDES`). `tools/lean-literal-parse-audit.py --conversions` lists the C functions
  that still call the core functions: 262 calls in 27 files of the engine's library closure
  before this landing (151 in `JS/Interp.c`), and 177 in the lab modules.

Checks: Test262 language subset, verdict of every file the same before and after, on `main`
(5,627 pass, 670 fail, 4 skip, out of 6,301) and on the branch (5,629, 668, 4); the output of
six benchmark programs the same; the engine's answers for ten pages byte for byte the same
(section 9.4).

### 7.3 Effect on BubblePopJS

Instructions for one operation on `main`, before and after (callgrind, N = 20,000):

| Operation | Before | After | Ratio |
|---|---|---|---|
| `i \| 1`, `i & 255`, `i ^ 5` | 8,718 | 4,030 | 2.16 |
| `a[i & 7]` | 10,622 | 5,261 | 2.02 |
| `i << 1` | 8,850 | 4,891 | 1.81 |
| `i >>> 1` | 7,862 | 4,762 | 1.65 |
| `i >> 1` | 7,175 | 4,803 | 1.49 |
| `~i` | 5,039 | 3,449 | 1.46 |
| `t.length`, `a.length`, `a[3]` | 3,860 to 4,163 | 3,087 to 3,390 | 1.23 to 1.25 |
| `i % 7` | 4,790 | 4,015 | 1.19 |
| `t[3]` | 5,238 | 4,438 | 1.18 |
| `'k' + i` | 5,924 | 5,124 | 1.16 |
| `a[3] = i` | 6,202 | 5,438 | 1.14 |
| `t.charCodeAt(3)` | 7,565 | 6,792 | 1.11 |
| `String(i)` | 8,479 | 7,697 | 1.10 |
| a function expression | 10,568 | 9,795 | 1.08 |
| `+`, `-`, `*`, a call, `Math.floor`, an array literal | no change | | 1.00 |

The same twins on top of `wip/bpperf` (wall time for one operation, with a build running on
the machine, so read the ratios): `a[i & 7]` 556 to 208 ns (2.7), `|` and `&` 465 to 176 ns
(2.6), `^` 2.2, `<<` 1.9, `>>>` 1.8, `>>` and `~` 1.7, `a.length` 195 to 116 ns (1.7),
`t.length` 1.5, `a[3]` 1.4, `%` 1.3, `charCodeAt` 1.2; `+`, calls and `a[3] = i` unchanged.
`a[3] = i` does not change there because the branch's own fast path for indexed writes has the
literal `4294967295.0` in `evalExpr`, read from text at each write: one line for that branch
(section 12, item 2).

## 8. The execution model: a measurement

Question: is the distance to QuickJS-NG a cost of Lean, or of walking a tree with a result
object for each node? Three programs in Lean run `var s = 0; for (var i = 0; i < n; i++) s = s + i`
(`labs/demos/foafnaut/bubblepop_perf/lean/VmFloor.lean`, run by `run.sh` beside it; compiled
with `leanc -O3`, 3 M iterations, five runs):

| Program | ns for one iteration |
|---|---|
| A: tree walk in `EStateM`, boxed values, fuel, a step budget (the shape of `JS/Interp.lean`, locals in slots) | 128 to 150 |
| B: the same tree walk as pure functions that return a value and the slots | 130 to 140 |
| C: register bytecode in an `Array UInt32`, numbers unboxed in a `FloatArray`, one tail-recursive function | 12.5 to 14.5 |
| BubblePopJS on the branch, the same loop (`loop_fn_var`) | 219 |
| QuickJS-NG | 18 |
| V8 with no JIT | 15 |

- The monad is not the cost: A and B are the same.
- C makes no allocation in the loop and is in the class of QuickJS-NG. It has no type test and
  no property access; a real engine pays for both. It was not tuned (`Nat` program counter,
  bounds tests on each register).
- So the "fast form" of section 13 of the engine record can reach that class in Lean, and it
  needs: code as a flat array, registers as an array that one loop owns, numbers unboxed, and
  no result object for each step. The cost of each further step of the tree walk (resolved
  slots, caches) is bounded by the 10 allocations and 2,555 instructions that remain.

## 9. The native engine (main)

### 9.1 Times on this VM

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

### 9.2 Start: 1,109 M instructions before `main`

`web-render-native` with no argument: 0.11 s, 60 MB. Every module's constants are computed at
start. By inclusive cost: `LeanJS.snapshotData` 740 M (it runs the BubblePopJS page prelude and
encodes the realm; only `bubblepop-realm`, a build tool, reads it); the scene shader text about
190 M; the XSLT 4 and XPath 4 tables 86 M (function signatures 74 M, an ixml grammar 35 M); the
IDNA table 60 M; Unicode normalisation 55 M and segmentation 28 M; a regular expression category
table 56 M.

Repair in this landing: `snapshotData` is a function of `Unit`. After: SEE-START.

The same start runs in the engine library of the macOS app and in the Wasm module of the Hub.
On `main` the Hub's Wasm build carries no realm data, so there the prelude ran once at module
start for nothing and once more at the first page.

### 9.3 Font load and first compile of the status page: 2,251 M instructions

Start 1,109 M, then the compile 1,141 M:

| Phase | M instructions | Share of the compile |
|---|---|---|
| layout (`WebDocument.layOut`) | 889 | 78% |
| of which shaping 364 words (`SfntProfile.Font.word`) | 722 | 63% |
| of which GSUB and GPOS (`SfntShape.shape` 416, `SfntGpos.position` 289) | | |
| of which kerning coverage (`SfntKern.coverage`, 42,395 calls) | 144 | 13% |
| of which 1,852 glyph outlines (`SfntOutline.outline`) | 165 | 14% |
| block and inline layout (`Layout.layoutTask`) | 68 | 6% |
| the frame (`WebRender.artifactWith`) | 244 | 21% |

A word costs about 2 M instructions to shape. In the whole run, decimal parses of 2^53 were
360,928 calls (`Float.ofNat` 359,009: `FontProvider.fromInt` 128,592, `SfntOutline.ofInt`
96,808, `SfntProfile` 93,490, the JavaScript lexer 18,786 at start, `writeFixed` 11,760):
`__gmpz_set_str` and its helpers, `malloc` and `free` were about 235 M instructions, 10%.
After this landing: SEE-FIRST.

### 9.4 One frame on a kept layout: 249 M instructions

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
| GMP text parse (`Float.ofNat` in `writeFixed`) | about 3% | 11,763 |

With checks on (the default of a request) a frame is 2.6 times as long: the probe pixels are
sampled on the CPU (`NativeSVG.pathHitFast` 9.4% of that profile).

After this landing: SEE-FRAME. Output bytes: SEE-BYTES.

## 10. Literals read from text at each call: the audit

`python3 tools/lean-literal-parse-audit.py` reads the generated C. Engine closure at
`036198f2`: 54 sites in 48 functions of 29 library files (WasmVM 13, XPath 4 9, Crypto 7,
XSLT 4 6, JS 6) and 9 in the lab modules. Sites in loops or per-item paths that are worth a
look: `ImageJPEG` (`cosines`, a literal inside the loop), `SVG.transformFunction` (pi for each
`rotate` or `skew`), `SVGText.lowerSfnt` (pi inside a loop), `WasmVM.Num.inI32` and `inU32` and
the `trapUn` conversions (float to integer instructions), `WasmVM.step` (two sites; not on the
path of every instruction, since WasmVM runs 360 M instructions a second). Not measured: how
often each runs.

## 11. What this landing changed

- New: `formal/lean4/L4Factoidal/Prim/FloatOfNat.lean`,
  `labs/demos/foafnaut/bubblepop_perf/opcost.py`, `tools/lean-literal-parse-audit.py`, this
  record.
- Changed: `JS/Number.lean`, `JS/Lexer.lean` (twins, constants), three `Rendering` modules and
  `labs/demos/foafnaut/SVG.lean` (one import each), `WasmVM/Hosts/LeanJS.lean` and
  `LeanJSRealmGen.lean` (`snapshotData` is a function), `tools/lean-csimp-reach.py` (core left
  sides), the `foafnaut` and `lean4-performance` skills, the worknote index.
- Not changed: `JS/Interp.lean`, `JS/Value.lean`, and every file that `wip/bpperf` changes
  except `LeanJS.lean` and `LeanJSRealmGen.lean`, where the changed lines are apart.

## 12. Ranked next steps

For BubblePopJS (the session that owns `wip/bpperf`; each item has its measurement above):

1. Land `wip/bpperf`. It is 1.4 to 3.5 times faster than `main` and removes six quadratic
   operations and the memory kept by calls. Until then `main` is what the app and the Hub run.
2. On that branch, `evalExpr` has the literal `4294967295.0` in the indexed write path, read
   from text at each `a[i] = v` (about 1,500 of 3,565 instructions). Make it a named constant
   (as `twoPow53F`), or test the index as an integer. `python3 tools/lean-literal-parse-audit.py
   --under L4Factoidal/JS/` shows it.
3. Bit operators and `%` on machine integers in `binop` (no `Int`, no `Nat.pow` for a shift):
   after this landing `i | 1` is still 176 ns against 98 ns for `+`.
4. Globals: `s = G` 220 ns against 87 ns for a local; `gf(i)` 373 ns against 250 ns. Resolve
   a global name to the global object's slot once, with a check, as the branch does for locals.
5. A collector, or at least reuse of dead objects between tasks: 328 bytes kept for each
   object is the limit for a page that animates.
6. Function expressions (1,040 ns, 31 allocations): make the `prototype` object when it is
   first read. Blocks with `let` (402 ns, 19 allocations).
7. The fast form of section 8: a register bytecode loop. It is the only step that removes
   the result object for each node. Decide it with section 8 in hand.

For the engine:

8. Write the scene's float32 values four bytes at a time into a buffer with its capacity set
   (a `pushU32LE` beside `Prim.Bytes.pushU64LE`): `lean_byte_array_push` is 10.3% of a frame.
9. Keep the lowered scene and its bytes with the kept layout (already named in
   [2026-11-07-foafnaut-frame-pipeline.md](2026-11-07-foafnaut-frame-pipeline.md)): `toScene`
   and `jsonWith` are 71% of a frame on a kept layout.
10. Float to text through `printf` is 13% of a frame: a binary form for the layout answer, or
    the cached formatter of `Rendering.FloatFormat`.
11. First compile is shaping: 2 M instructions for each word. `SfntKern.coverage` (42,395
    calls, 144 M) and `SfntGpos.posAt` (30,975 calls, 243 M) are the first functions to read.
12. Start: the tables of section 9.2 as `Thunk`s, read where they are used (about 370 M
    instructions remain after this landing).
13. Import `Prim.FloatOfNat` in the other modules that `--conversions` lists, by profile.

## 13. Not measured

- Anything on a Mac: the window, the GPU draw, Deno, FFI calls, input latency, the Hub.
- The Wasm build of the engine and BubblePopJS in it.
- Page scripts in real pages (DOM calls through the host), WPT run times.
- The engine's layout on real sites (see
  [2026-11-09-real-site-layout-speed.md](2026-11-09-real-site-layout-speed.md)).
- How often each site of section 10 runs.
- The whole Lean tree was not built here: only the engine closure (372 modules) and the lab
  modules. The gates `lean-tail-recursion-audit.py --gate` and `lean-unbuilt-modules.py --gate`
  need the full build of `danbri/factoidal-builds`.
