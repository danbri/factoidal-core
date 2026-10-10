# JSON-LD node map generation: from quadratic to n log n

2026-10-10. Branch `claude/wt-perf-jsonld`. Code: `formal/lean4/L4Factoidal/JSONLD/{OrderedMap,Flatten,Frame,NodeMapTheorems}.lean`,
`formal/lean4/Harness/JsonLdScale.lean`. Gate: `tests/stack/jsonld_scaling.sh`.

## 1. Result

Node map generation (JSON-LD 1.1 API 7.1 and 7.2) now costs `O(n log n)` in
the number of nodes. The output is byte-identical to the output before the
change, on every W3C flatten and framing fixture and on the generated
documents (section 5).

One node that holds 1,600 node references, 1 run, milliseconds:

| phase | before | after |
| --- | --- | --- |
| node map generation | 3895.7 | 8.2 |
| flatten (node map and emission) | 4723.7 | 7.6 |
| frame (expand, frame, compact) | 8481.9 | 91.5 |

Conformance is unchanged: `l4jsonld-api` TOTAL 791 pass, 0 fail, 2
local-override, 0 unsupported (out of 793); `l4jsonld-probe` toRdf 467 pass,
0 fail, 0 skip (out of 467); `l4jsonld-frame` 91 pass, 0 fail, 1
local-override, 0 unsupported (out of 92).

## 2. What was slow

Measured 2026-10-10 on the tree before the change. The measurement
that started this work: flat nodes plus one shared node, framing, 100, 200,
400, 800 and 3,200 nodes took 84, 225, 564, 1,581 and 25,324 ms. At 1,600
nodes expansion took 0.57 s and node map generation 5.3 s of 7.1 s.

`Flatten.lean` kept four levels as association lists: the node map (state to
graph), each graph (node identifier to node), each node (property to value)
and the blank node relabelling map. Every lookup and update scanned. Four
costs, in order of size on the fan-out shape of section 4:

1. **The duplicate test.** Appending a value to a property array first asked
   "is an equal value already in the array" (`flArrContains`). That called
   `expandedEqual` on every item already present, and `expandedEqual`
   serialises both of its arguments with `jcsDocument` (RFC 8785). A node
   with 1,600 references made about 1.3 million such calls, each serialising
   two values. The count is from the code; it was not profiled on the old
   binary.
2. **The list appends.** `items ++ [v]` per value, and `xs ++ [item]` per
   output item in framing, copy the list each time.
3. **The lookups.** `flLookup`, `flUpd`, `flRemove` on the graph, on the
   graph list and on the relabelling map are scans, and `flUpd` rebuilds the
   list.
4. **The sorts.** `flSortByKey` is an insertion sort, and `strLt` converted
   both strings to `List Char` at every comparison.

Framing had its own list-shaped state (`FState.embeds`, `FState.bnodes`, the
member lists of output objects, `Frame.cleanupPreserve` testing membership in
a list of blank node identifiers). It also copied its whole output arena on
every allocation: `allocM` read the state with `get` and wrote it with
`set`, which keeps the old state alive during the write. A `callgrind` profile
of one framing run of the fan-out shape at n = 1,000, taken after the node map
repair, attributed 18.5% of the instructions (inclusive) to `FState.setEmbed`,
a `flUpd` over the embeds list. After reference counting, the largest self
costs were `List.reverseAux` (the list appends) and `flUpd`.

## 3. The representation

Four levels, each a persistent map keyed by `String`:

| level | type | order that is observed |
| --- | --- | --- |
| state to graph | `Std.TreeMap String NmGraph` | graph names in code-point order |
| graph | `NmGraph := Std.TreeMap String NmNode` | node identifiers in code-point order ("ordered by id") |
| node | `NmNode := OMap NmVal` | entries in first-creation order |
| blank node map | `Std.TreeMap String String` | none |

`compare` on `String` is the order of every tree. `strLt_iff_compare_lt`
proves it is the `strLt` order the earlier port sorted with, so the sorts
`flSortByKey` performed are the traversal of the tree.

`OMap` (`OrderedMap.lean`) is a `Std.TreeMap` plus the keys in reverse order
of first insertion. A node must list its entries in first-creation order
because the flattened output shows that order as the order of the object's
members. Both parts are persistent. The alternative, an `Array` of entries
and a `Std.HashMap` of positions, updates in place only through a unique
reference; through a shared reference it copies the whole array on every
update. The node map is read while it is written (the graph is bound to a
local name, then updated), so references are shared. A persistent tree
copies one path of `O(log n)` nodes in either case.

`DedupArr` holds the values of one property. `rev` is the list newest first,
so appending is a `cons`. `seen` is a `Std.TreeSet` of the `jcsDocument`
form of every item, so "already in the array" is one set lookup. The `@list`
accumulator of `nmg` is also newest first and is reversed once, when the list
is complete.

`NmVal` is `one` (a scalar entry: `@id`, `@index`) or `many` (an array entry:
`@type` and every property). `NmNode.toFields` and `NmNode.toSortedFields`
give the entries as JSON members, in first-creation order and in key order.

Framing: `FState.embeds` is a `TreeMap` of `OMap`, `FState.bnodes` a
`TreeMap`, the clear-set of `cleanupPreserve` a `TreeSet`, output objects an
`OMap`, output arrays are stored newest first (`OCont.arr`), and `allocM` is
one `modifyGet`. `Frame.frameResults` is the part of `frameDocumentWith`
between expansion and compaction, split out so the harness can time it.

`strLt` now has a `@[csimp]` replacement, `strLtFast a b = decide (a < b)`,
which uses the runtime's string comparison. `strLt_eq_strLtFast` proves them
equal for all arguments, so the specification of every sort that uses `strLt`
is unchanged. This does not change an asymptotic cost. It lowers the cost of
each comparison wherever an insertion sort is left (the member lists of single
input objects): expansion of the `wide` shape at n = 8,000 went from 5.2 s to
1.4 s.

One behaviour differs in a case that cannot occur. `flFoldNamed` appended a
second `@graph` entry to a name node that already had one. `OMap.upsert`
replaces it. A node built by node map generation never has an `@graph`
entry, because `@graph` is consumed before the properties are visited.

## 4. Measurements

Method: `formal/lean4/.lake/build/bin/l4jsonld-api --scale [base [runs]]`,
run from the repository root. Five document shapes, each generated at n, 2n,
4n, 8n and 16n:

* `hub`: n flat typed nodes, each linking to one shared node;
* `fanout`: one node with n distinct node references under one property;
* `bnode`: a chain of n blank nodes;
* `graphs`: n named graphs of one node each;
* `wide`: one node with n distinct properties.

Phases: `expand`, `node map` (`generateNodeMap` on the expanded form),
`flatten` (`flattenExpanded`), `frame core` (`frameResults`), `flatten+ctx`
(`flattenDocument` with a context) and `frame` (`frameDocument`). Times are
wall-clock milliseconds; the minimum of the runs is kept. Host: 4 CPUs shared
with other processes (load average 3 to 7 during the runs), so single runs
carry noise of about 2x below 20 ms.

Before and after, base 100, 1 run per point. The 16x column is
time(1600)/time(100): 16 for a linear phase, about 26 for `n log n` at these
sizes, 256 for a quadratic phase.

| shape | phase | n=100 before | n=1600 before | 16x before | n=100 after | n=1600 after | 16x after |
| --- | --- | --- | --- | --- | --- | --- | --- |
| hub | node map | 1.3 | 267.9 | 206 | 1.1 | 34.3 | 31 |
| hub | flatten | 5.8 | 805.0 | 139 | 5.2 | 35.3 | 7 |
| fanout | node map | 14.0 | 3895.7 | 278 | 0.4 | 8.2 | 21 |
| fanout | flatten | 14.5 | 4723.7 | 326 | 0.3 | 7.6 | 25 |
| bnode | node map | 1.2 | 293.9 | 245 | 1.3 | 17.3 | 13 |
| bnode | flatten | 1.3 | 509.1 | 392 | 1.2 | 18.9 | 16 |
| graphs | node map | 0.6 | 132.1 | 220 | 0.4 | 9.4 | 24 |
| graphs | flatten | 1.5 | 1175.9 | 784 | 0.5 | 11.5 | 23 |
| wide | node map | 0.4 | 78.9 | 197 | 0.3 | 6.3 | 21 |
| wide | flatten | 0.4 | 79.9 | 200 | 0.2 | 6.4 | 32 |

Scaling assertion on the same ladder, size pairs (x, 4x) with time(4x) at
most 9.0 times max(time(x), 20 ms): before, 11 of the 30 pairs of the node
map and flatten phases failed (the `frame core` phase did not exist); after,
0 of the 45 pairs of the node map, flatten and frame core phases fail.

After, default ladder (`--scale`: base 250, minimum of 3 runs, sizes 250 to
4,000), milliseconds:

| shape | n | expand | node map | flatten | frame core | flatten+ctx | frame |
| --- | --- | --- | --- | --- | --- | --- | --- |
| hub | 250 | 23.2 | 2.8 | 3.1 | 6.0 | 30.7 | 32.0 |
| hub | 4000 | 441.9 | 57.8 | 60.0 | 126.2 | 613.8 | 663.5 |
| fanout | 250 | 2.2 | 1.0 | 1.0 | 2.7 | 6.4 | 6.6 |
| fanout | 4000 | 98.1 | 19.4 | 19.3 | 48.4 | 293.8 | 317.0 |
| bnode | 250 | 17.0 | 1.9 | 2.0 | 4.0 | 23.1 | 23.4 |
| bnode | 4000 | 379.6 | 48.4 | 51.8 | 85.1 | 469.3 | 502.1 |
| graphs | 250 | 11.3 | 1.2 | 1.4 | 2.9 | 17.2 | 17.1 |
| graphs | 4000 | 294.7 | 26.1 | 28.4 | 64.4 | 451.5 | 373.7 |
| wide | 250 | 6.6 | 0.6 | 0.7 | 1.3 | 9.5 | 9.6 |
| wide | 4000 | 413.5 | 15.7 | 16.5 | 37.6 | 736.4 | 740.2 |

Result: scaling 45 pass, 0 fail (out of 45) size pairs.

The default ladder is the gate. `tests/stack/jsonld_scaling.sh` runs it with
a 600 s cap.

Larger ladder (`--scale 1000 1`, sizes 1,000 to 16,000, 1 run per point),
the node map, flatten and frame core phases at n = 1,000 and n = 16,000, in
milliseconds. Linear growth gives a factor of 16, `n log n` about 21:

| shape | node map 1,000 | node map 16,000 | flatten 1,000 | flatten 16,000 | frame core 1,000 | frame core 16,000 |
| --- | --- | --- | --- | --- | --- | --- |
| hub | 12.9 | 389.7 | 13.0 | 257.6 | 27.3 | 707.9 |
| fanout | 4.5 | 96.9 | 4.5 | 105.1 | 11.4 | 228.1 |
| bnode | 9.0 | 228.0 | 9.1 | 208.2 | 18.5 | 407.1 |
| graphs | 7.2 | 176.3 | 7.5 | 139.7 | 16.8 | 299.1 |
| wide | 3.7 | 75.9 | 3.7 | 94.9 | 6.9 | 164.4 |

Scaling 45 pass, 0 fail (out of 45) size pairs on that ladder as well.

Phases the assertion does not cover. `expand`, `flatten+ctx` and `frame`
contain expansion and compaction, which this change did not touch. Measured
2026-10-10 on the current tree, same ladder (`--scale 1000 1`):

* expansion of the `wide` shape (one object with n members): 47.0, 128.1,
  458.3, 1,473.5 and 8,260.0 ms at n = 1,000, 2,000, 4,000, 8,000 and 16,000.
  `Expand.sortMapEntries`, an insertion sort over the members, is the likely
  cause. It was not profiled.
* expansion of the `fanout` shape: 10.9, 29.8, 129.1, 429.9 and 1,514.4 ms.
  The factor per doubling is about 3.5 at the large sizes.
* compaction of an array of n values, from the `fanout` shape: `flatten+ctx`
  minus `expand` minus `flatten` is about 0.76 s at n = 8,000 and about 3.4 s
  at n = 16,000. `Compact.cmpAddValue` appends with `xs ++ [v]` and is the
  likely cause. It was not profiled.

`fromRdf` (API 8.5, `FromRdf.lean`) does not use this node map. It builds
its own `List FrNode`, and the same kind of scan remains in it (`findNode`,
`ensureNode`, `nodeUpdateProp` maps over every node, `referencedOnce` filters
the list of all references, `sortNodes` is an insertion sort). Measured
2026-10-10 with `l4jsonld-api --once SHAPE fromRdf N` minus the same run for
`toRdf` (which builds the dataset), one run each: `hub` shape 0.039 s, 0.166 s
and 0.653 s at n = 1,000, 2,000 and 4,000 (a factor of about 4 per doubling);
`fanout` shape 0.028 s, 0.125 s and 0.537 s. This change did not touch it.

## 5. Why the output is the same

Two kinds of evidence.

**Proofs** (`NodeMapTheorems.lean`; no `sorry`, no `axiom`, no
`native_decide`; `#print axioms` shows only `propext`, `Classical.choice`,
`Quot.sound`). The list definitions that were replaced stay in namespace
`Spec` as the specification.

* `strLt_iff_compare_lt`: `strLt a b = true` iff `compare a b = .lt`.
* `OMap.find?_eq`, `OMap.toList_upsert`, `OMap.WF_upsert`: on a well-formed
  map, lookup is `flLookup` and update is `flUpd` on the entries in
  insertion order.
* `DedupArr.contains_iff`: the canonical-form set answers exactly what
  `flArrContains` answered. `DedupArr.foldl_pushDedup`: merging `@type` items
  one at a time is `flMergeTypeItems`. `DedupArr.pushDedup_twice`: appending
  the same value twice with the duplicate test is appending it once.
* `toFields_nodeAppendProp`, `toFields_nodeEnsureProp`,
  `toFields_nodeMergeTypes`, `nodeSetIndex_toFields`, `nodeHasOnlyId_eq`:
  each node operation, read through `NmNode.toFields`, equals the `Spec`
  definition.
* `stNodeUpdate_get_same`, `stNodeUpdate_get_other_node`,
  `stNodeUpdate_other_graph`, `stEnsureNode_get`, `stEnsureNode_other_node`:
  lookup after update on the graph map.
* `issueKeyed_repeat`, `issueKeyed_new`, `issueKeyed_known`,
  `issueKeyed_fresh_label`: relabelling the same blank node twice gives the
  same label and does not advance the counter.
* `ApiTests.addOutput_array` was restated for the newest-first array
  (`item :: xs`). It was about the list representation.

What the proofs do not cover: the traversal order of a graph (a `Std.TreeMap`
yields keys in `compare` order, which `strLt_iff_compare_lt` ties to `strLt`,
but the equality of a tree traversal with `flSortByKey` of the old list is
not proved), the framing state changes, and the reversal of the `@list`
accumulator. Byte comparison covers them.

**Byte comparison.** The suites compare with RFC 8785 canonical forms, which
ignore the order of object members. The harness can write the raw output
(`toStringCompact`, member order included) of every case:
`L4_JSONLD_DUMP=<file> l4jsonld-api` and `l4jsonld-frame` append one line per
manifest entry, and `l4jsonld-api --dump-shapes` appends the output of the
five document shapes at n = 1, 2, 5, 40 and 150. The build before the change
and the build after it wrote 932 lines (63 flatten, 92 frame, 250 compact,
398 expand, 54 fromRdf and 75 shape lines), and `cmp` reports the two files
identical. The comparison was repeated after each of the three steps (node
map, framing state, `strLt`).

**What "byte-identical" covers, and what it does not** (owner note,
2026-10-10: "be aware that the @context syntax can bring out of band state
into a test, making results depend on more than testcase formal inputs").
A JSON-LD result is a function of more than the test's input and frame
files. Through `@context` (a remote context IRI, `@import`, a scoped
context), the result also depends on what the document loader returns for
each IRI, on the base IRI, and on the processing options the manifest
states (`base`, `processingMode`, `specVersion`, `expandContext`,
`omitGraph`, ...). Both builds ran with the same out-of-band state:
- the document loader built by the runners (`buildLoader`): the vendored
  test tree under its manifest `baseIri`, then
  `third_party/jsonld-context-cache` (index.json sha256
  `7d921676d913c3fe1cfeb198ef344c8d525a4bf7d361d7f937488803faecf3a5`, last
  changed in commit 9e3ad4a3); no network; an IRI in neither fails the case;
- the options each manifest entry states, and no others.
So the 932 identical lines show that the new code gives the same bytes as
the old code for the same documents AND the same loaded contexts. They do
not show that a result depends only on the test files: a different cache
snapshot, a live loader, or a different base IRI can change the output of
both builds. A result quoted from this harness names the cache digest above.

`ApiTests.lean` has `#guard` cases, each with a negative case beside it, for
the new structures and for node map generation end to end: insertion order
and replacement in place, canonical-form duplicates, list order, value
order, node order, blank node relabelling order, named graph order, the
conflicting-indexes error.

## 6. Running it

    formal/lean4/.lake/build/bin/l4jsonld-api --scale [base [runs]]   # from the repository root
    tests/stack/jsonld_scaling.sh [base [runs]]                        # same, with a time cap
    formal/lean4/.lake/build/bin/l4jsonld-api --once SHAPE PHASE N     # one run, for valgrind
    L4_JSONLD_DUMP=/tmp/out.txt formal/lean4/.lake/build/bin/l4jsonld-api   # raw output of every case

Timing is wall-clock. Raise the number of runs per point before reading a
failure as a regression on a loaded host.
