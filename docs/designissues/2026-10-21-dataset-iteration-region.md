# Dataset iteration: a byte region in place of a JSON string

Issue: https://github.com/danbri/factoidal/issues/900 (follows
https://github.com/danbri/factoidal/issues/894).

Owner, 2026-10-21, verbatim: "we went to trouble of having a single wasm so
data is in same memory space. How the heck have we managed to make it SLOWER
to leave it in pure Lean(wasm'd) than serializijg it in and out of wasm in
TEXT??? Some FP horror? Debug!"

## 1. Result

Iteration of 60,000 quads (`for (const q of ds)`, node, wasm, median of 5,
the dataset of `npm/factoidal/test/dataset-iterate-speed.test.mjs`):

| path | iteration | engine op | JS side |
|---|---|---|---|
| before issue 894: N-Quads text, JS tokeniser | 214–280 ms | 173 ms (`datasetSerialize`) | 40–100 ms |
| issue 894: `datasetQuadsJson` compact | 317 ms | 255 ms | 25 ms `JSON.parse` + 37 ms objects |
| this record: `datasetQuadsBin` region | 178–205 ms | 126–140 ms | 36 ms strings + objects |

The machine had a load average of 16 to 26 on 4 CPUs during the "after"
runs (two other agents built Lean), against about 1 during the "before" runs;
the same-run ratio is the reliable number: iteration over the N-Quads writer
op was 1.84 before and 0.96 to 1.10 after. `has` (0.1 ms), `size` (0 ms) and
`toString('nquads')` (142 ms before, 175 ms after at the higher load; same op,
no code change) did not change; `match` includes the first index build of a
fresh clone (260 ms before, 335 ms after, same op, no code change).

## 2. Where the time went (measured, before)

Native build of the same Lean op (`lake exe l4iter-phases N`,
`formal/lean4/Harness/IterPhases.lean`), median of 5, ms:

| phase | 15,000 | 30,000 | 60,000 |
|---|---|---|---|
| `Dataset.quadList` | 0.1 | 0.3 | 0.7 |
| `compactFast` (hash map term table) | 14.8 | 37.1 | 60.3 |
| `checkCompact` (the run-time certification) | 13.9 | 29.5 | 59.1 |
| JSON text of the terms (`termText`) | 8.0 | 13.9 | 29.4 |
| JSON text of the index lists | 3.8 | 7.5 | 14.5 |
| whole op `datasetQuadsJson` compact | 39.1 | 98.9 | 214.6 |
| whole op `datasetSerialize nquads` | 18.7 | 38.1 | 91.4 |

JS side (wasm, node, 60,000): op 255 ms, copy out and `JSON.parse` 25 ms,
RDF/JS objects 37 ms.

Causes, checked:

1. The run-time certification re-walked every quad: `checkCompact` decodes
   each index list and compares it with the quad by structural equality of
   terms (string compares), as much time as building the table. It did not
   re-sort. CONFIRMED, 28 % of the op.
2. The table builder allocated per quad: a term list (`quadTerms`), an index
   array, a list, and a tuple per lookup. CONFIRMED (callgrind: `mi_free`,
   `lean_dec_ref_cold` and `mi_malloc_small` together above the hashing).
3. JSON text: the answer was built as one string by appends, then copied out
   and parsed by `JSON.parse`. CONFIRMED, about 45 ms in Lean plus 25 ms in
   JS. The `Json` tree was not used on the compact path (the `termText`
   writer already wrote text directly), so tree building was not a cost.
4. The term table did not use lists or String-keyed lists: it is a
   `Std.HashMap String Nat`. NOT a cause.
5. The quad list was materialised before paging (`quadList`, then
   `drop`/`take`): 0.7 ms at 60,000. NOT a cause.

## 3. Repair

* `L4Factoidal/RDF/QuadsBin.lean`: op `datasetQuadsBin(handle, optsJson)`
  answers ONE byte region through `l4_call_blob_io` (the out region of
  `Wasm/Dispatch.lean`). Layout `binSpec`: `"FQB1"`, the term count, the
  quad count, the distinct terms in the term codec of DLOG version 2
  (`Storage.serializeDeltaTerm?`: kind tag, u32 byte lengths, UTF-8 bytes,
  datatype IRI, language tag and direction byte written explicitly), then
  four u32 per quad (graph 0 = default graph, else 1 + index).
* The writer is one pass over the quads (`binLoop`): a term is looked up,
  written when it is first seen, and its index is written; no list per quad,
  no JSON, no run-time check.
* `npm/factoidal/lib/dataset.mjs` `quadsFromRegion` reads the region with a
  `DataView` and a `TextDecoder` (a short ASCII run is copied without a
  decoder call). It copies fields only; the purity lint, group 3, passes 34
  of 34. Iteration asks for the first 4,096 quads, then the rest in one more
  call, so an iteration that stops early reads one small region.
* `datasetQuadsJson` stays for the string entry.

## 4. Theorems (no `sorry`, no new axiom)

In `L4Factoidal/RDF/QuadsBinTheorems.lean`:

* `putTerm_some`, `putTerm_none`: the `ByteArray` term writer writes exactly
  the bytes of `serializeDeltaTerm?` and refuses what it refuses.
* `index_inv`, `quad_inv`, `binLoop_inv`: the writer state invariant (each
  map entry names its term in the table, the table is below 2^32 entries, the
  term bytes are the bytes of the table).
* `quadsBin_binSpec`: the region is `binSpec tbl ixs` for a table and index
  lists with `TermJson.decodeCompactArr tbl ixs = some qs`.
* `decodeBin_binSpec`: the reader `decodeBin` inverts `binSpec` (it uses
  `TermCodecTheorems.parseDeltaTerm_serializeDeltaTerm?`).
* `decodeBin_quadsBin`: the region of `quadsBin qs` reads back as exactly
  `qs`. This is proved once; the run-time certification of the JSON form is
  not needed on this path.

`#guard` cases: a round trip on a two-quad dataset with shared terms; a
wrong magic number and a truncated region are refused; an index list of the
wrong shape has no bytes. npm: `test/dataset-iterate-region.test.mjs`
compares iteration with the engine's term objects for every term kind
(directional literal, nested triple terms, blank-node graph, non-ASCII text)
and checks the paging; `test/dataset-iterate-speed.test.mjs` is now an
assertion (it was the expected failure of issue 900).

## 5. Costs left

* The engine op is still about 0.8 times the N-Quads writer op: hashing each
  IRI string per occurrence, and one `ByteArray.push` per byte of the index
  fields. A term id held in the dataset itself would remove the hashing.
* The DLOG version 2 codec writes the datatype IRI of every language-tagged
  literal (`rdf:langString`), 64 bytes each. A codec change needs a new wire
  version (skills/shardborough-storage), so it was not changed here.
