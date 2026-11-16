# Incremental equals full: inventory, statement and first proofs

Date: 2026-11-16. Author: incr, a subagent of the coordinator session.
Related: https://github.com/danbri/factoidal-core/issues/513 (theorem pipeline, item 2).
Earlier record: [cost theorems](2026-11-08-cost-theorems.md).

Item 2 of the pipeline: incremental style, layout and paint give exactly what a full
recompute gives. This record lists every cached or incremental path in the engine with
what is proved and what is only tested, states the end-to-end theorem, and says what
landed with it.

Paths: `L/` is `labs/demos/foafnaut/`, `F/` is `formal/lean4/L4Factoidal/`. Line numbers
are of main at 0ccd896a0.

## 1. The end-to-end statement

The engine already has both sides as functions of the same request
(`L/WebDocument.lean`): `run` answers from the kept engine state (`answerIn`, `keptFrame`),
`runUncached` answers from an empty one (`answerUncached`, `freshLayOut`).

> **Incremental equals full.** For every sequence of requests `r₁ … rₙ` to one document,
> the answer of `run` to `rₙ` after `r₁ … rₙ₋₁` (JSON and byte sections) is the answer of
> `runUncached` to `rₙ`. The damage rectangles are extra: every pixel outside them is the
> same in the two frames' rasters (`Scene.rasterSpec`).

It splits into these lemmas, one per row of section 2. Each has the same shape: a validity
invariant of the kept state (`Valid`), a step lemma (a hit returns what the full function
returns, given `Valid`), and a preservation lemma (every engine step keeps `Valid`).
Most rows have the step lemma. Almost none has preservation. That is the main gap.

1. **Tables** (parse, sheets, image store, links, words): step lemmas exist; prove that
   `Kept.add` and the store updates preserve `Valid`.
2. **Layout memo**: `frameWith_eq` exists for a valid memo and a sound restyle; prove that
   `Engine.frame` keeps `e.layouts` valid for `e.holds`, and discharge `RestyleSound`.
3. **Restyle**: `restyleWith` equals `computeAllWith` after the change; the bucket premise
   of `computeAll_eq_linear` (`RuleIndex.matched = matchedRules`).
4. **Paint-only frame**: the kept scene is `WebPaint.patch laid.paint values laid.scene`.
5. **Retained compile**: `compileRetained reuse prev … leaves` gives the items of
   `compileRetained (fun _ _ => .different) none … leaves`, when the reuse rule implies
   equal leaves (`reuseByValue_eq`) and `prev` came from this function. Then
   `Retained.dataBytes` and `Retained.tileWords` equal `Scene.float32Bytes` and
   `Scene.tiles`. `Reuse.moved` needs: flattening depends only on the linear part.
6. **Tile, band and cell lists**: `rasterTiles = rasterAll` for every scene. This is where
   Float geometry enters (section 3).
7. **Band and scroll**: `composite_correct` exists over abstract images; `nearNodes`
   filtering equals the frame inside the band.
8. **Unsafe caches** (`pageArtifactImpl`, `shapeKeptImpl`): outside what Lean can state
   while they are `implemented_by`. They are in the hygiene ratchet's count; the
   theorem is about the reference bodies, and the kept implementations stay tested
   (`partial_frame_test.ts`) until issue 390 removes them.

## 2. Inventory

| # | Path | Full version | Proved equal | Tested only |
|---|---|---|---|---|
| 1 | Layout memo: `FrameCost.Lru`, `Engine.frame` (`L/WebDocument.lean:2810`) | `layOut` | `Lru.lookup_eq`, `lookupLayout_eq`, `frameWith_eq`, each given a valid memo; validity of `e.layouts` across frames not proved | `keptAgree` guards (`WebDocumentTests.lean`), `frame_work_test.ts` |
| 2 | Hover and `:active` repaint: `restyle`, `WebRepaint.recolor` | layout with the pointer in the key | nothing: `RestyleSound` is an assumed proposition | `keptAgree stateFrames` |
| 3 | Paint-only frame: `WebPaint.patch`, `Engine.paint` slot | layout with the new values | nothing | `frame_work_test.ts` |
| 4 | Parse, sheet, image store tables: `parseIn`, `sheetIn`, `storeIn` | `parseFresh`, `CSS.parseRaw`, `pageStore` | `parseIn_eq`, `sheetIn_eq`, `storeIn_eq` given `Valid`; preservation not proved | store hit: tested |
| 5 | SVG text words: `SVGText.wordIn` | `SfntProfile.wordIn` | `wordIn_eq` given `WordsValid`; preservation not proved | |
| 6 | Font word memo: `SfntProfile.Memo` (one record reused at every size) | `shapeFresh` | nothing | `memoWords` guards only |
| 7 | Shaped-word table: `shapeKept` (`implemented_by`, global) | `shapeFresh` | reference body only | no test that isolates it |
| 8 | Kept page band: `pageArtifactImpl` (`implemented_by`, global) | `artifactWith (cull …)` | `pageArtifact_eq` is about the reference body | `partial_frame_test.ts` |
| 9 | Retained compile: `compileRetained`, `retainItem`, `LeafKey.movedOf` | `compilePrimitives`, `Scene.artifactWith` | reuse implies equal keys (`reuseByValue_eq`); **new: `retainItem_same_fresh`** (one item); the loop and `moved` not proved | `partial_frame_test.ts` byte comparison |
| 10 | Damage rectangles: `damageRects` | full redraw | nothing | row count only |
| 11 | Retained tile words: `tilesOfListingsRows` | `tilesOfListingsRef` | nothing | one raster guard |
| 12 | Tile listing: `paintBox`, `edgeBands`, `edgesMeeting`, `binPieces`, `tileCells` | every record at every pixel (`rasterAll`) | `pathHitList_eq`, `any_filter_of_keeps` given that the filter keeps what matters; **new: `edgesMeeting_fill_eq`** discharges that for the edge filter, given IEEE comparison laws and the sample row inside the band interval; **new: `Cull.bin_holds`, `Cull.overlap_of_common_point`** for cells | raster guards (`rasterTiles == rasterSpec == rasterAll`), `cpu_render_diff_check.mjs` |
| 13 | Row spans: `pathSpansAt`, `pathHitSpans` | `pathHitFast` | nothing direct | `rasterFast == rasterSpec` guards |
| 14 | Prepared coverage and samples | `coverageAt`, `sampleStep` | proved, no hypothesis | |
| 15 | Culled coverage: `prepareCoverageCulled`, `prepareCoverageTile` | `prepareCoverage` | nothing | raster guards |
| 16 | `WebPaint.cull` | uncut curves | nothing | `cullPixels` guards |
| 17 | Band and scroll: `FrameCost.band`, `composite`, `nearNodes` | frame at the scroll | `composite_eq_frame`, `composite_correct` over abstract images | `sameAsFrame` guards, `scroll_layers_check.ts` |
| 18 | Link decode slot | `Links.decode` | `decodeKept_eq`, `decodeKept_valid` | |
| 19 | Rule buckets: `RuleIndex` | `matchedRules` | `computeAll_eq_linear` given the bucket premise; the premise is tested | `CascadeTests.lean` |
| 20 | Partial restyle: `CSS.restyleWith` | `computeAllWith` | `restyleWith_nil` only | `script_turn_cost_test.ts` |
| 21 | Cached layout reads from scripts: `Reads.kept`, `Host.measured` | `measureNow` | freshness properties only | `script_reads_holds_test.ts` |
| 22 | Float decimal cache; other `csimp` fast forms | reference definitions | proved | |

Found while listing:

- `runUncached` goes through the same global kept band and shaped-word table as `run`, so
  the `keptAgree` guards are not differential for rows 7 and 8.
- `keptAgree` runs with `bytes=false`; the retained compile runs only for byte sections, so
  only `partial_frame_test.ts` covers row 9.
- A comment in `F/Rendering/Style.lean` cites `RuleIndex.matched_eq`; no such theorem exists.
- `F/FrameCost/Band.lean` cites `scroll_layers_test.ts`; the file is `scroll_layers_check.ts`.

## 3. Float geometry

Lean's `Float` is opaque: no theorem about `<=` on it can be proved without an axiom, and
the repository bans user axioms. That is why rows 12, 13, 15 and 16 are byte-checked.

The route taken here:

1. **Order reasoning, generic.** `F/FrameCost/Cull.lean` proves the culling facts for any
   type whose comparisons obey `Cull.Laws` (six laws, each true of IEEE 754 comparison with
   NaN and infinities). `intLaws` shows `Int` obeys them, so the laws are consistent and
   the facts hold with no hypothesis for integer or fixed-point geometry.
2. **Float, by hypothesis.** `L/IncrementalProofs.lean` applies them to the engine's own
   `edgeMeets`, `edgesMeeting`, `pathEdgeSpans` and `pathHitList`, with `Cull.Laws Float` as
   a named hypothesis. No axiom is added.
3. **What stays byte-checked: rounding.** That the margin of `Primitive.edgeBands` and
   `localRows` puts every sample row of a band inside the band's interval, and that
   `pieceScreenBox` and `paintBox` hold every point a piece or primitive covers, are
   bounds on rounding error of the inverse transform. They need a Float model.
4. **Margins.** The proofs show the order step needs no margin at all: a spanning edge is
   kept for any interval that holds the sample row. So the whole of each margin
   (`(hi-lo)/16+(|lo|+|hi|)/4096+1/4096` for rows, 2 px for boxes, `1.001·width+1e-6` for
   pieces) is spent on rounding. A proved bound on that error would let the margins shrink.

To close item 3 of this section, in order of cost:

- **Exact comparison for binning** (cheapest): compute band and cell membership on integer
  sub-pixel coordinates (floor and ceiling of the Float box, taken once). Then
  `bin_holds_int` and `meets_of_spans_int` apply with no hypothesis, and the only Float
  step left is one outward rounding per box.
- **A Float model in a bridge library**: IEEE binary64 as a Lean structure with proved
  rounding bounds, and the engine's geometry stated over a type class that both it and
  `Float` implement. Core must still build without Mathlib; the model goes in a separate
  library.
- **Interval arithmetic** in the listing code: more work per primitive, so only with timings.

## 4. What landed with this record

- `formal/lean4/L4Factoidal/FrameCost/Cull.lean` (only Lean core; in library `FrameCost`):
  `Laws`, `intLaws`, `meets_of_spans`, `overlap_of_common_point`, `bin_holds`,
  `bin_holds_int`, `meets_of_spans_int`.
- `labs/demos/foafnaut/IncrementalProofs.lean` (checked in `build-web-render.sh`, no runtime
  code): `edgeMeets_eq_meets`, `edgesMeeting_fill_eq`, `retainItem_same_fresh`.

Proved: the theorems named above, axioms `propext`, `Classical.choice`, `Quot.sound` at most.
Assumed and named: `Cull.Laws Float`; that the edge list was made from the record's end
values (`recorded`); no NaN end value (`finite`); the sample row inside the interval.
Tested only: everything in the right-hand column of section 2.
Bounds: no new loop or recursion on page input; no runtime code changes, so no timing changes.

## 5. Next steps, by value

1. Preservation of `Valid` for the tables and the layout memo (rows 1, 4, 5): plain
   structural proofs, no Float, and they make `frameWith_eq` usable end to end.
2. The loop of `compileRetained` equals the plain compile for `Reuse.same` and
   `Reuse.different` (row 9), from `retainItem_same_fresh` and `reuseByValue_eq`.
3. `tilesOfListingsRows = tilesOfListingsRef` (row 11): no Float.
4. A differential guard for rows 7 and 8 that does not share the global tables.
5. Integer binning (section 3), measured on Spinal Tap before and after.
6. `RuleIndex.matched = matchedRules` (row 19) and `restyleWith` (row 20).
