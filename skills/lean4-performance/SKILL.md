---
name: lean4-performance
description: Improve performance-sensitive Lean 4 code in Factoidal while preserving total semantics, observable order, and executable proof boundaries. Use for large parser, RDF/block ingestion, data-structure, recursion, or hot-path work; not for unmeasured micro-optimisation.
---

# Lean 4 performance in Factoidal

Start with a concrete phase and an observable baseline: text read, parse,
bucket/index build, block encode/decode, range I/O, query evaluation, or result
formatting. A green semantic test is not a throughput result, and a fast host
shim is not a semantic replacement.

## Recursion and collection rules

- In a repeatedly invoked path, treat `xs.length`, `List.reverse`, `++`, and
  `String.toList` as costs to account for. `remaining.length` used to choose
  fuel inside every parser step is often an accidental quadratic scan.
- Build ordered lists with a reverse accumulator and restore order exactly once
  at a named boundary. State the preserved order in the doc comment and test
  it where it affects RDF/SPARQL results.
- Make a scanner tail-recursive when it consumes a flat stream and only needs
  a token/result accumulator. A reverse accumulator is normally the right
  representation.
- Keep structurally recursive or fuelled recursion for grammar nesting and
  semantic tree traversal when it supports totality or proofs. Do not replace
  it with `partial` merely to obtain a loop-like shape.
- A recursive map over a small, bounded metadata list may be appropriate. Do
  not generalise that exception to data-sized lists, graph rows, or tokens.

## Keyed collections: association lists, shared maps, appends at the end

A collection keyed by a set the caller sizes (node identifiers, blank node
labels, graph names, the values of one property) is a map, not a
`List (String × _)`. Paid for 2026-10-10 in JSON-LD node map generation
(`JSONLD/Flatten.lean`, record:
[`docs/designissues/2026-10-10-jsonld-node-map-scaling.md`](../../docs/designissues/2026-10-10-jsonld-node-map-scaling.md)):
the node map, each graph, the graph list and the blank node map were
association lists, and a document with one node that holds 1,600 node
references took 3.9 s to build its node map (4.7 s to flatten, 8.5 s to
frame). After the repair the same input takes 8.2 ms, 7.6 ms and 91 ms.
Rules from that repair:

- **Use `Std.TreeMap` (or `Std.HashMap`) for a collection that grows with
  the input.** Keep an association list only for the members of one input
  object.
- **Prefer a persistent map where a value can be referenced twice.** An
  `Array` or a `Std.HashMap` updates in place only when the reference is
  unique; through a second reference the update copies the bucket array,
  and the code stays correct and becomes quadratic. `Std.TreeMap` copies a
  path of `O(log n)` nodes whatever the reference count.
- **`let st ← get; set { st with a := st.a.push x }` keeps the old state
  alive, so it copies `a`.** `Frame.allocM` did this and copied the whole
  output arena on every allocation. Use `modifyGet` or `modify`, which use
  the state once.
- **When insertion order is observable, use `OMap`** (`JSONLD/OrderedMap.lean`:
  a `Std.TreeMap` plus the keys newest first). Lookup and update agree with
  `flLookup` and `flUpd` on the entries in insertion order
  (`OMap.find?_eq`, `OMap.toList_upsert`).
- **Appending at the end is a reverse accumulation.** `xs ++ [v]` once per
  value is quadratic in the number of values; cons onto the front and
  reverse once at the boundary (`DedupArr.rev`, `OCont.arr`, the `@list`
  accumulator of `nmg`).
- **A "not already in the array" test over a growing array compares keys in
  a set, not by scanning.** The scan called `expandedEqual` (two JCS
  serialisations) on every item already present, which was most of the 3.9 s
  above. `DedupArr` keeps the canonical form of each item in a
  `Std.TreeSet`; `DedupArr.contains_iff` proves the set answers the scan's
  question.
- **Prove the new operations against the old definitions, and compare raw
  output.** The old list definitions stay as `Spec.*` in
  `JSONLD/NodeMapTheorems.lean`. For a change that must not alter output,
  run both builds with `L4_JSONLD_DUMP=<file>` on every manifest and on
  `l4jsonld-api --dump-shapes`, then `cmp` the files: the suites compare
  with RFC 8785 canonical forms, which ignore member order, and the raw
  dump does not.
- **Measure first, with a ladder.** `l4jsonld-api --scale` prints the time
  of each phase at n, 2n, 4n, 8n and 16n for five document shapes and
  asserts time(4x) at most 9.0 times max(time(x), 20 ms) for the node map,
  flatten and frame core phases (`tests/stack/jsonld_scaling.sh`). One
  shape is not enough: at 1,600 nodes the hub shape (every node links to
  one hub) cost 0.27 s to build its node map and the fan-out shape (one node
  holds all the references) cost 3.9 s, so a ladder over the hub shape alone
  would have under-reported the cost 14-fold.

## Input-proportional recursion is a stack bug, and the scanner is the gate

A function that recurses once per element of an input the CALLER sizes -- a
list, a string, a byte stream, a declared entry count -- costs one C stack
frame per element. On the host that is a slow path; in the wasm module it is a
crash, because the stack we ship there is far smaller. The rule:

> **Recursion over an input-proportional structure is tail-recursive or
> worklist-driven. Never rely on a bigger stack.**

### How to tell, by tool and not by reading

Lean compiles a DIRECT TAIL self-call into a jump: the emitted C function opens
with `_start:` and the call becomes `goto _start;`. Any self-call that survives
as a real C call is a real stack frame. Read that from the compiled output:

    lake build                                   # in formal/lean4/
    python3 tools/lean-tail-recursion-audit.py   # counts, areas, ranked table
    python3 tools/lean-tail-recursion-audit.py --json /tmp/t.json
    python3 tools/lean-tail-recursion-audit.py --gate   # CI form

`--gate` fails when a NEW input-proportional recursion appears that is not in
`tools/lean-tail-recursion-allow.txt`. Removing a line from that file is the
goal; adding one needs a reason in the commit message. Read the script's
docstring for what the method cannot see -- inlining, specialisation, and
recursion that runs through an unspecialised core combinator.

The first measurement, 2026-09-07: 833 self-recursions without a loop, 268
mutual cycles; 598 input-length, 42 input-depth. Per area (length): JSON-LD 71,
Shardborough 66, SPARQL 65, SHACL/ShEx 36, OWL 33, RDF parsers 18, XPath/XSLT
18, XML 11.

### The repair: `csimp`, not a rewrite of the specification

Keep the specification's shape -- every theorem is stated about it -- and add a
tail-recursive twin plus a proved `@[csimp]` replacement. The code generator
then emits the twin and the proofs are untouched. `csimp` replaces one CONSTANT
by another, so the accumulator's empty start needs its own `def`:

```lean
def decodeEntriesTR (version : Nat) : Nat -> List UInt8 -> List Entry ->
    Option (List Entry × List UInt8)
  | 0, bytes, acc => some (acc.reverse, bytes)
  | n + 1, bytes, acc =>
      match decodeEntry version bytes with
      | none => none
      | some (entry, after) => decodeEntriesTR version n after (entry :: acc)

theorem decodeEntriesTR_eq (version : Nat) : ∀ n bytes acc,
    decodeEntriesTR version n bytes acc =
      (decodeEntries version n bytes).map (fun p => (acc.reverse ++ p.1, p.2)) := ...

def decodeEntriesImpl (version n : Nat) (bytes : List UInt8) := decodeEntriesTR version n bytes []

@[csimp] theorem decodeEntries_eq_decodeEntriesImpl :
    @decodeEntries = @decodeEntriesImpl := ...
```

`@[implemented_by]` reaches the same runtime effect with no proof. It is an
unchecked assumption about the two functions agreeing, and this tree does not
take those. Use `csimp`.

### What it cost

* <https://github.com/danbri/factoidal/issues/670>. `ShardManifest.decodeEntries`
  recursed once per manifest entry. The published SKOS manifest declares 36,106,
  so a browser tab answered "Maximum call stack size exceeded", and
  `storeQueryPlan` never returned.
* <https://github.com/danbri/factoidal/issues/673>. Recorded as "XML entity
  expansion is not tail-recursive, near 2,000 sequential entities". The scanner
  plus a bisection said otherwise: `expandEntityValue` was already loop-compiled
  except for its nested-entity dive, and the ceiling tracked DOCUMENT LENGTH,
  not entity count. 500 plain sibling elements and 12,000 characters of ordinary
  text both died, with no entity present. The recursion was
  `normalizeLineEndings`, the section 2.11 line-ending pre-pass, which walks
  every character of the document before parsing starts. The wasm RDF/XML
  parser's ceiling was about 7,000 characters of any input.
* The 36,106-entry manifest took 322 s natively. That number did NOT come from
  the recursion: `/usr/bin/sample` put every sampled frame in
  `ShardManifest.valid` -> `uniqueArtifactKeys` -> `List.eraseDupsBy`, a
  quadratic duplicate scan over about 150,000 artifact keys. Measure before
  attributing a cost to the defect you happen to be holding.

`tests/stack/run.sh` is the behavioural half of this: deep inputs on two
routes, the wasm module in Node (installed by `tools/fetch-builds.sh` or
built by `Wasm/build-wasm.sh`; not committed since 2026-10-09) and the
native CLI. Add a case there
whenever you repair one of these.

## Factoidal RDF/block ingestion

The parsing layers and their entry points are recorded in
[`docs/designissues/2026-09-03-rdf-parsing-strategy.md`](../../docs/designissues/2026-09-03-rdf-parsing-strategy.md);
read it before changing a parser path.

`L4Factoidal/Syntax/Turtle.lean` preserves source triple order. Its statement
parser and flat name/whitespace scanners use append-free/tail-recursive paths;
retain that order contract when changing them. `parseTurtleFold` lets a packer
consume completed statements without materialising a second source `Graph`,
but it still starts from a complete `String` and character list. Treat genuine
byte-chunk input as the next separate design step: it must carry Turtle prefix,
base-IRI, RDF-mode and blank-node state across chunks. Never split Turtle on
newlines.

`Storage/PredicateBlocks.lean` keeps per-predicate rows in reverse buckets
while ingesting, then restores source order before creating an `IndexedBlock`.
The packer may avoid a duplicate graph, but the current one-block-per-predicate
format still retains each predicate's rows until its immutable block is built.
Do not claim streaming-scale memory until bounded block publication exists.

`Syntax/TurtleStatementScan.lean` is the chunk-stable candidate scanner the
packer runs per character. Any per-character or per-line decision in it must
read O(1) state, never the accumulated candidate. Paid for 2026-09-02: the
no-dot directive test reversed the whole current candidate at every line end
(`dropWs currentRev.reverse`), O(lines × characters) per statement group,
which turned a 134 MB polygon group (4,211 lines) into 334 s of packing and
the UK Parliament dump into 6,134 s. The fix keeps a seven-character `head`
maintained by `pushHead` and proves it equal to the old form
(`TurtleStatementScanTheorems.head_eq_spec`). How it was found: a size
ladder of slices without large literals was linear (34 µs per triple), so
the cost was isolated to the large-literal region and that region packed
alone; do that before reading code for a superlinear ingest.

## Verification and measurement

After a semantic hot-path change, run the closest Lean guards and targeted
executable path, then the persistent block smoke when ingestion or block bytes
are affected:

```text
cd formal/lean4 && lake build L4Factoidal.Syntax.TurtleTests l4block-shard-pack
cd ../.. && tools/blockengine-shard-merkle-scan-smoke.sh
```

Use a bounded real corpus in addition to fixtures. Record input identity,
triple count, elapsed time, output bytes, host and what is *not* measured in a
dated worknote. Stop or cap long experiments deliberately; do not leave
duplicate background packers competing for the same temporary output.

For the current KGX scale observations and the required future byte-streaming
ingest boundary, read [`docs/20260830-ibk2-ingest-scale.md`](../../docs/20260830-ibk2-ingest-scale.md).
