# BubblePopJS: global names read through cached scope chains (issue 471, step 1)

Owner, 2026-11-27, verbatim: "next: 1. then 2 then3 then 4." Step 1 is the global-name cache
(CLAUDE.md, "BubblePopJS JIT: order after tier 2"). Tracking:
https://github.com/danbri/factoidal-core/issues/471.

## What a global read cost

`vmGlobalHit` (the register machine's read of a global name) first walked the environments from
the site's environment to environment 0 by name (`HeapOf.findEnv`: `Env.has` on each, a scan or a
hash lookup), then read the cached slot of the global object (`PropMap.liveAt`, a hash lookup).
callgrind, `leanjs` of main `b629c2b71`:

- `props.js` (top-level loop, one environment): a read 428 instructions (`findEnv` 129, `liveAt`
  71, the rest 205); reads 29.7% and writes 13.5% of the script.
- A read of `Math` from a function nested three deep in a wrapper function (`nest.js`, against
  `nest0.js`, the same code with `Math` in a local): 1,087 instructions, `findEnv` about 860.
- Library corpus: at most 1.7% (immutable); 0 in lodash, marked and pako.

Page code is the nested case: Particle Rex and foaf-explorer put their code in one wrapper function
(about 127 and 49 names, so indexed environments), and read `Math`, `document` and `window` from
inside it.

## What changed

- `Compile.globalSite`: a site's slot is from the name and the position in the code (it was the
  name's hash alone, so every read of `Math` in every function shared one slot). 4,096 slots.
- `GHop` (an environment's names array and index), `GHopOk x` (a hop with the proof that `x` is
  absent), `GEntry.chain x hops`: the scope chain a read walked, learned on a miss
  (`HeapOf.mkChain`, in `HeapOf.globalLearn`, called where the slot was already learned).
- `HeapOf.chainOk`: at each hop, no `with` object, the same names array and the same index as the
  entry (`sameKeys`, `sameIdx`: the same object in memory first, then by value). No name is
  hashed or scanned. `vmGlobalHit` and `vmGlobalSet` use `chainHit` in place of `findEnv`; on a
  miss the general path runs and learns the chain again.
- `globalChain` is in `ColdHeap`, not in the hot record (below).

Proved (`JS/Theorems.lean`; axioms `propext`, `Classical.choice`, `Quot.sound`):

- `Env.slotN_of_hop`: an environment that passes a hop's check has the hop's `slotN`.
- `chainOk_findEnv`: a passing chain means `findEnv` answers `none`, for any fuel at least the
  chain's length.
- `vmGlobalHit_sound` holds as before (no environment binds the name, and the global object has
  the data property), now from `chainHit_findEnv`.
- The fuel and refinement chain (`JSFuelMono`, `IH_all`, `tier1_*_refines`) builds unchanged.

Regression tests (`JS/RegressionTests.lean`): a direct `eval` that adds a binding after the site
learned its chain, a `with` around a read, two closures of one function.

## Measurements

callgrind instructions, Linux x86-64 cloud VM; main `b629c2b71` against the change. Every output
identical; Test262 `test/language` (6,301 files) verdict lists byte-identical (5,986 pass, 314
fail, 1 skip).

| Script | main | after | change |
|---|---|---|---|
| `nest.js` | 633,910,556 | 601,689,224 | −5.1% |
| `props.js` | 3,890,312,418 | 3,814,284,738 | −2.0% |
| `method.js` | 4,689,488,985 | 4,597,134,555 | −2.0% |
| acorn (N=1) | 2,320,313,234 | 2,322,688,741 | +0.10% |
| immutable (N=1000) | 2,217,261,506 | 2,215,522,412 | −0.08% |
| lodash (N=1000) | 1,549,883,296 | 1,550,255,664 | +0.02% |
| marked (N=6) | 491,975,168 | 492,315,892 | +0.07% |
| pako (N=32) | 4,059,586,029 | 4,057,713,510 | −0.05% |

One global read in nested code: 1,087 to 540 instructions (2.0 times). The remaining cost is the
slot check (`liveAt` hashes the name in the global object's big map) and the function's own
reference counts.

## Trap: a field of the hot heap record costs at every change of the heap

The first version put `globalChain` in `HeapOf` beside `globalCache`. All five libraries then ran
0.16 to 0.41% more instructions, pako +15 M in its run although pako reads no global name in its
loop. Lean rebuilds the hot record at every change of the heap (the step count at every loop
head), so one more field is one more copy each time. In `ColdHeap` the libraries are within
±0.1% of main. Cost: one build and one corpus run. Tier 2's `HeapOf.icache`
(`2026-11-25-tier2-property-reads.md`) was a hot field too; part of its corpus regression may be
this. Rule: a new heap field that changes rarely goes in `ColdHeap`.

## Not done

- The page measurement (first script run of two pages, Particle Rex turn time): the native engine
  build of this change is still to do on this machine.
- `liveAt`'s hash in the slot check, and writes (`vmGlobalSet` allocates once through
  `updateObj`: 877 instructions a write in `props.js`).
