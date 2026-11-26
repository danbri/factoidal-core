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

## Result of 2026-11-26: a proved inline cache, measured, not landed

Branch: `wip/471-tier2-ic` (https://github.com/danbri/factoidal-core/tree/wip/471-tier2-ic), on
main `ba7a04275`. Not merged into `main`, because it makes every library of the corpus slower
(table below). Tracking: https://github.com/danbri/factoidal-core/issues/471.

### Prior work that this step checked first

- https://github.com/danbri/factoidal-core/pull/486 (open, stage C spike): no-go for inline caches on
  the present heap, because a cached slot saves only a short scan and a sound guard seemed to need
  shapes. This step tested a guard that needs no shapes (below). The result agrees with PR 486.
- https://github.com/danbri/factoidal-core/pull/538 (merged): `docs/bubblepopjs-heap.md`, shapes with
  transition tables and the `ValidIC` cases (own, proto with epoch, absent, write, add). Design only.
- https://github.com/danbri/factoidal-core/issues/532 (open): execution hints need shapes and per-site
  caches first.
- No branch implements shapes.

### What the branch has

- `Mode.tier2` (`BUBBLEPOP_TIER2=off` turns it off). `Mode.Sub t1 t2` replaces the condition
  `t1.tier1 → t2.tier1` of `IH_all` and of every step lemma (`tools/fuelmono-gen.py`).
- `Instr.getMember dst o key site`: the compiler gives each read a slot of `HeapOf.icache` (4,096
  entries, from the key and the position in the code).
- `IC`, an entry with its proofs as fields: `own key ks slot` with `PropMap.scan ks key 0 = slot`,
  and `proto key ks pks slot` with the own miss, the prototype's slot and `isPrivKey key = false`.
  The guard compares the object's key array with `ks` (`sameKeys`: the same array in memory first,
  then element by element). It needs no shape table and no invariant over the heap: every entry in
  every heap carries its proof.
- The register machine fills the entry in every mode (`Tier2.memberGen`); only tier 2 reads it
  (`Tier2.getMember?` through `Tier1.withFast`). So `tier_refines` still compares whole heaps.
- Proved (`JS/Tier2Proofs.lean`, axioms `propext`, `Classical.choice`, `Quot.sound`):
  `icGet_sound` (a cache answer is the answer of `fastGetV`), `icSet_hit` (on a hit the fill writes
  the entry already there, so the heap is unchanged), `getMember_site` (the site lemma in the form
  `Le.withFast` leaves). `Le.memberGen` lets the walk pass the arm.

### Measurements

`valgrind --tool=callgrind`, instructions, Linux x86-64 cloud VM. "base" is `leanjs` of main
`e33848e6` (its engine differs from `ba7a04275` only in generators and regular expressions). "on"
and "off" are one binary of the branch with `BUBBLEPOP_TIER2` unset and `off`. Every run printed the
reference answer.

One property read (`own.js` against `loc4.js`: the same loop with 4 property reads of a 4-key object
against 4 register reads, 120,000 reads):

| | base | on | off |
|---|---|---|---|
| instructions per read | 397 | 361 | 941 |

The target was at least 3 times faster on sites that see one shape: 397 to 361 is 1.10 times. Not met.

Library corpus of `realworld.py`, size N:

| Library | base | on | off | on/base |
|---|---|---|---|---|
| acorn (N=1) | 2,320,755,314 | 2,499,863,459 | 2,515,133,097 | 1.077 |
| immutable (N=1000) | 2,217,284,205 | 2,285,382,088 | 2,315,438,333 | 1.031 |
| lodash (N=1000) | 1,549,864,259 | 1,587,985,783 | 1,608,739,510 | 1.025 |
| marked (N=6) | 491,911,722 | 495,184,574 | 496,462,115 | 1.007 |
| pako (N=32) | 4,059,814,528 | 4,136,005,103 | 4,133,043,145 | 1.019 |

Test262 (`third_party/testing/test262`, `test/language`, 6,301 files), branch binary: 5,986 pass,
314 fail, 1 skip with tier 2 on and with it off; the two verdict lists are byte-identical.

### Why

1. A hit is not cheap in this machine. With `Tier2.getMember?` built as its own function, it is 155
   instructions per hit (pointer compares, then about eight reference count increments and
   decrements: the heap, the object, its map, the values array, the entry, the value). The lookup it
   replaces (`fastGet`, `PropMap.scan`, `memcmp`, `lean_string_eq_cold`) is 206.
2. The rest of a `getMember` step is about 190 instructions (dispatch, registers, the Number box),
   and a register add is about 120. No cache changes that part.
3. The fill runs on every read that `fastGetV` answers and the cache does not: `icMake` scans the keys
   again and allocates an entry. On polymorphic sites (acorn's parser nodes) this is most reads.
   "on" against "off" shows what the hits save on the libraries: 0 to 1.3%.

### What this says for the next step

- A property cache pays only after the cost of a register machine step falls (word values and
  registers without boxes, heap plan section 4 rule 1) and with a fill that runs once per site, not
  on every miss. Both are larger changes than tier 2.
- The proof method carries over: entries that hold their own proofs, a fill that is the same in
  every mode, and a site lemma for `Le.withFast`. A shape-based cache can reuse `getMember_site`
  with `icGet` and `icMake` replaced.
- The global-name path (`vmGlobalHit` with `findEnv` first, 25% of `props.js`) is still the larger
  target, as this record said on 2026-11-25.
