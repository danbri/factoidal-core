# BubblePopJS: what a page's script time is spent on, and the call path (issue 471, 2026-11-27)

Owner, 2026-11-27, goal: "performant JIT JS improving our ux". Tracking:
https://github.com/danbri/factoidal-core/issues/471. Order of work: CLAUDE.md, "BubblePopJS JIT: order
after tier 2". Rule: page code runs on our own engines only (CLAUDE.md, "No V8, no engine of another
browser").

## Particle Rex on the Linux rig

Rig: `tools/foafnaut-linux-rig` (Xvfb, llvmpipe, Deno 2.9.4), engines built from this tree with
`build-web-render.sh --native`; options `--watch-sweep 8 --perf-summary --engine-mode tasks`.
Profile: `perf record -e cpu-clock -F 499 --call-graph dwarf,16384`, 7,251 samples.

- 41% of the samples have a BubblePopJS frame; 74% of those are inside `callHost` (the canvas
  calls). BubblePopJS's own work is about 10% of all samples.
- In that own work: `%` on fractions (`jsMod`, `dyadic`) about 12%, the register machine 12%, the
  evaluator (functions the register machine does not take) 11%, property reads 6%.
- The start turn (about 440 to 540 ms): canvas calls 88 of 266 script samples, host script
  machinery 48, realm snapshot decode about 20, parse 12, register compiler 7.
- Outside BubblePopJS: the canvas raster and Web Audio converted float literals through text in
  their loops (fixed in `9690023d2`).

`leanjs compile-stats` (`38238d732`): 223 functions in Particle Rex, 172 compiled. Not compiled:
26 make a closure, 18 `for-of`, 3 `try`, 1 regular expression literal, 1 `for-in`, 1 parameters,
1 other.

## Cost of one operation

`bubblepop_perf/opcost.py --callgrind`, instructions for one operation less the empty loop:

| Operation | main `9ff7f976b` | after the built-in call changes |
|---|---|---|
| `Math.floor(i)` | 4,124 (13 allocations) | 3,193 (4) |
| `s.charCodeAt(3)` | 4,797 (18) | 4,289 (13) |
| number to string | 3,979 (12) | 3,262 (5) |
| `g()` (compiled function) | 2,263 (7) | 2,259 (7) |
| `a + b` | 332 | 332 |

What a built-in call paid for: the step charge read the heap through four monadic helpers that are
not inlined, each making a result cell; `Math`'s one-argument functions took the operation as a
closure, which boxed the argument and the answer.

## Changes, in order, each measured

callgrind instructions; corpus of `realworld.py` at size N; every answer the same and the Test262
`test/language` verdict lists identical (5,986 pass, 314 fail, 1 skip) at each step; `JSFuelMono`
builds at each step with no `sorryAx`.

1. Global names through cached scope chains, `9ff7f976b` (record
   `2026-11-27-global-name-scope-chains.md`).
2. Canvas raster and Web Audio literals, `9690023d2`.
3. `%` on fractions, `b36fcd0a1` (`JS/DyadicFast.lean`, `@[csimp] dyadic_eq_fast`): 30,000 `x % y`
   from 7,341,051,907 to 983,354,114 instructions.
4. Built-in calls, `8b350fa2d`: the step charge from one read of the heap; `Math` cases with no
   closure.
5. Calls to compiled code, `7e855fa9b`: no tuple for the callee. `g()` 2,259 to 2,072 instructions.
6. Method reads on strings: `fastGet` reads a primitive wrapper's property map for keys that cannot
   be an index or `length` (`Obj.getOwn` has no other own keys there). `s.charCodeAt(3)` 4,289 to
   3,318 instructions, 13 to 9 allocations.

| Library | main `9ff7f976b` | after 4 | after 5 | after 6 | 4 to 6 together |
|---|---|---|---|---|---|
| acorn (N=1) | 2,322,523,227 | 2,293,823,178 | 2,276,422,261 | 2,250,491,198 | −3.10% |
| immutable (N=1000) | 2,215,668,098 | 2,182,204,468 | 2,159,826,937 | 2,132,641,068 | −3.75% |
| lodash (N=1000) | 1,550,205,051 | 1,540,892,297 | 1,514,505,402 | 1,514,523,206 | −2.30% |
| marked (N=6) | 492,386,721 | 487,640,553 | 487,400,430 | 485,422,654 | −1.42% |
| pako (N=32) | 4,058,033,895 | 4,045,592,939 | 4,041,142,434 | 4,041,704,690 | −0.40% |

## Particle Rex, after steps 1 to 3

Three interleaved rig runs each; engines built from main `a0b86f170` (before) and `e56d8bdc1`:

| | before | after |
|---|---|---|
| Timer turn p50, ms | 26.0, 25.6, 27.1 | 23.7, 24.1, 24.9 |
| Timer turn p95, ms | 42.2, 34.0, 39.2 | 36.0, 26.8, 34.5 |
| Timer turns in the window | 237, 260, 246 | 279, 289, 267 |
| Start turn, ms | 472, 507, 501 | 477, 459, 441 |

The spread between runs of one engine is about 10%; read the direction. Steps 4 to 6 are not in
these engines.

## What is next, and why

- A step of the register machine costs about 260 machine instructions (a numeric loop of five
  instructions: 1,298 an iteration), most of it in `vmLoop` itself: boxed `Nat` operands, the
  register arrays' checks, the heap record. That is step 2 of the order.
- A global read still hashes the name once (`PropMap.liveAt` in the global object's big map).
- 51 of Particle Rex's functions run in the evaluator (closures, `for-of`, `try`). PR 476 measured
  that moving such functions to the register machine with their variables in environment slots
  gives little, while the step cost stays as it is.
