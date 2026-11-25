# BubblePopJS tier 2: where property reads spend their time, and what a cache can check (issue 471)

Owner decision, 2026-11-25: start tier 2, inline caches for property reads (target: at least 3 times
faster on sites that see one shape). Tracking: https://github.com/danbri/factoidal-core/issues/471.
This branch (`wip/471-tier2`) is tier 1 of [PR 557](https://github.com/danbri/factoidal-core/pull/557)
merged with main.

## Measurement first

Instructions by function (`valgrind --tool=callgrind`, `leanjs` of main `100307076`, Lake build, Linux
x86-64). Start of the program (`empty.js`): 125.7 million instructions; the shares below are of the
rest. "Property read" is `HeapOf.fastGet` with what it calls (inclusive).

| Script | instructions after start | property read | global name read (`vmGlobalHit`) |
|---|---|---|---|
| `props.js` at 30,000 iterations | 326 M | 16.0 M (4.9%) | 82.4 M (25%) |
| `method.js` at 30,000 iterations | 429 M | 40.3 M (9.4%) | 58.9 M (14%) |
| 120,000 reads of `o.a`..`o.d` inside a function | 99 M | 24.8 M (25%), about 206 a read | 0 |

Findings:

- **These reads run in the register machine**, in its `getMember` instruction (`vmLoop`), not in the
  evaluator's `.member` arm: top-level loops and function bodies are compiled to it. A fast path in
  the evaluator's arm under `Tier1.withFast` changes none of the benchmark scripts while the machine
  is on (the default). With `BUBBLEPOP_VM=off` the arm runs.
- **A read is already short**: `getMember` calls `HeapOf.fastGetV`, a pure lookup (object array,
  kind test, scan of at most 8 keys compared by pointer first, then the prototype). Removing all of
  it would make `props.js` 5% and `method.js` 9% faster; a 3 times faster read gives two thirds of
  that.
- **Global names cost more than properties** in `props.js` and `method.js`: every read of a `var`
  at the top level walks the environments (`findEnv`) before the cache is used.

## What a cache can check today

The heap has no shape identity (stage C of `docs/bubblepopjs-heap.md` is not on main), so a cache can
only remember a slot number and check, at each use, that the slot still holds the key. Proved here
(`JS/PropMap.lean`):

- `PropMap.get?_of_slot`: if slot `i` holds `k`, `PropMap.liveAt i k` holds, and in a small map no
  earlier slot holds `k`, then `get? k` is the value of slot `i`. A big map keeps an erased key in its
  slot as a tombstone; `liveAt` asks the hash map whether the slot is still the key's.

That condition was missing from the register machine's global name cache: after `delete` of a global
property (the global object always has a big map), the machine read the old value where the evaluator
throws a ReferenceError, and an assignment wrote to the dead slot. Repaired with `liveAt` in
`vmGlobalHit` and `vmGlobalSet`; two `#guard`s in `JS/RegressionTests.lean`; `vmGlobalHit_sound`
(`JS/Theorems.lean`) states that an answer of `vmGlobalHit` is the global object's data property.

## What tier 2 needs, in order

1. A cache for `getMember` that is faster than `fastGetV` needs a guard that does not scan: a shape
   identity on the object (stage C), or a proved invariant that every small map's keys are distinct
   (then the guard is one comparison and `get?_of_slot` applies with no scan before `i`).
2. Where the cache lives. `tier_refines` compares whole heaps, so a cache in the heap must be filled
   the same way with the tier on and off (as `globalCache` is: the machine fills it in both modes);
   only its use can depend on `Mode`. The alternative, a relation that ignores cache fields, changes
   `Le` and every step lemma.
3. The machine, not the evaluator's arm, is where the reads are: the site lemma is about the
   `getMember` step of `vmLoop`, which today is the same code in both modes.
4. Before property caches: the global name path (`findEnv` before every cached global read) is the
   larger cost on the micro set.
