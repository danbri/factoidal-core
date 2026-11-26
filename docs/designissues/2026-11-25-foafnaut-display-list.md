# Foafnaut: kept frame answers, binary layout sections, and the band change

Date: 2026-11-25. Tracking: https://github.com/danbri/factoidal-core/issues/1124 (retained display
list and binary frame answer). Goal: item 1 of section 6 of
`docs/designissues/2026-11-25-foafnaut-architecture-briefing.md`. Related:
https://github.com/danbri/factoidal-core/issues/1031 (threads, tabs, gestures, frame latency),
`docs/designissues/2026-11-07-foafnaut-frame-pipeline.md`, `docs/designissues/2026-11-09-partial-frames.md`.

## 1. The two frame paths

A render request goes to `WebDocument.answerWith`. After the layout (kept by `LayoutKey`, numbered
by `Laid.serial`), it takes one of two paths:

- No layers (`plainArtifact`): the page near the scroll, with the marks, under the chrome when the
  request has a shell. One scene, one answer. Neither host uses this path for frames. The
  `--document-bin` benchmark of the briefing (249 M instructions) measures this path.
- Layers (`layers:true`, the desktop host and the Hub): `layersJSON` gives a page layer
  (`pageArtifact`: the band of the page around the scroll) and a chrome layer (`chromeArtifact`).
  The host scrolls inside the band with no Lean call (the composite shader), and asks for the next
  band ahead of time (scroll prefetch).

`pageArtifact` keeps its last two answers (`keptPageRef`) and gives one again when its inputs are
the same objects (`ptrEq`); since aa23d058f (2026-11-08). A changed pointer state goes through the
retained compile (`WebPaint.retainedAnswer`, `NativeSVG.compileRetained`): a primitive whose key is
unchanged keeps its records and its tile listing, and the answer has damage rectangles.

## 2. Measured before this work (base 9fa1d855)

Machine: 4-vCPU Linux cloud VM. 1600 by 1000, checks off, font Noto Sans. Instructions are
callgrind totals of all threads, (COUNT 4 - COUNT 1) / 3 of `web-render-native --document-bin`
or `--document-bin-seq`.

| Frame | status.html | index.html |
|---|---|---|
| no layers, kept layout | 612.3 M instructions, 64-86 ms | 474.7 M, 49-53 ms |
| layers, nothing changed | 14.6 M, 1.8-2.3 ms | 12.3 M, 1.4-2.8 ms |
| layers, new scroll band | not measured (scroll limit 521 is inside the first band) | 654.0 M, 62-89 ms |

The layers frame with nothing changed spent its time in the chrome layer (made again each frame)
and in copying the answer. On the host, a layers answer of index.html had a 365,788-byte JSON
head (glyph runs 175 KB, boxes 42 KB, links 21 KB, two scene shaders); Deno took 1.4-1.9 ms to
decode and parse it on every frame.

A new band (index.html, per frame, all threads, 654 M):

| Part (inclusive) | Instructions | Share |
|---|---|---|
| `Primitive.tileListing` of every primitive (in four tasks) | 314 M | 48% |
| `compileRetained`: `compilePrimitive` 81 M, records (`writeRows`) 83 M | 234 M | 36% |
| `leavesGo` (the layer's leaves) | 52 M | 8% |
| allocation and free (`lean_dec_ref_cold`, `mi_free`, `mi_malloc_small`), self | 193 M | 30% |

The band change does not use the retained compile: `previous` must have the same band, and a new
band has other primitives at other indices.

## 3. Stage A: answers kept in the engine state (74d4c4f5)

`Engine` keeps the last chrome answer with a `ChromeKey`, and the last answer with no layers with
a `PlainKey`. A request whose key is equal to the kept key gets the kept answer.

- `ChromeKey`: the shell (derived `BEq`), the window width, the page width and mapping (bit for
  bit), the held fonts (`Holds.fontNames`; the address font is made from the held monospace face),
  the fields of the face that the layout header writes, and the flags (live, data form, checks,
  tree). `chromeLayer` reads nothing else of the page.
- `PlainKey`: the layout's number (`Laid.serial`), the shell, the sizes, the held fonts and the
  flags. Used only when the scene is the layout's own (`laid.paint.empty`), there are no marks, and
  the serial is not 0 (a layout from `freshLayOut` has serial 0). The engine gives each layout and
  each painted pointer state its own serial, so the serial names the scene, the boxes and the face.

Refinement: the specification is the function the key stands for (`chromeArtifact`,
`plainArtifact`, both `WebRender.artifactWith` of a scene). The kept answer was made by that
function from inputs whose key is equal to this request's key, and every input the function reads
is in the key or is named by the serial. The keys are plain values of the engine state; the memo
adds no `unsafe` and no `implemented_by` (the lab hygiene ratchet stays at 3 and 3). Not proved
in Lean: that two layouts with one serial are equal (it holds because `Engine.layOutKept` and
`Engine.frameKept` give each new layout `serial+1` and the state is threaded). Tested: answers
byte-equal to base over 3 pages and 17 request prefixes (chrome change, scroll, press, hover, no
layers with and without shell).

| Frame | before | after |
|---|---|---|
| no layers, status.html | 612.3 M, 64-86 ms | 4.2 M, 0.39-0.71 ms |
| no layers, index.html | 474.7 M, 49-53 ms | 1.4 M, 0.25-0.34 ms |
| layers, nothing changed, status.html | 14.6 M, 1.8-2.3 ms | 5.7 M, 0.43-0.65 ms |
| layers, nothing changed, index.html | 12.3 M, 1.4-2.8 ms | 3.0 M, 0.37-0.54 ms |

The Spinal Tap probe frame (no layers, checks on): second frame 713.5 ms before, 13.2 ms after.
Its known failure of https://github.com/danbri/factoidal-core/issues/450
(`probe.second_over_first`) now passes and is a budget.

## 4. Stage B: boxes, glyph runs and links as sections (6c229fe6, 0b367bc0)

Request field `layoutSections:true`, with a section answer. The page's `webRender` then has the
layout header and `"layoutSections":true`, and the answer has `"layout":{"section":i,"strings":j}`.
Section `i` is float64 little-endian (`WebRender.layoutSections`):

- the counts of boxes, runs, glyphs and links;
- each box: source, x, y, width, height;
- each run: source, fontSize, fontStart, fontBytes, textStart, textBytes, glyphCount;
- the glyphs of every run in run order, each: index, x, y, advance, clusterStart, clusterEnd;
- each link: sourceNode, hrefStart, hrefBytes, x, y, width, height (moved for the band).

Section `j` is UTF-8: the fonts, texts and link targets that the starts and byte counts name. The
engine keeps the two sections by the layout's serial and the band's top. Without the field the
answer is the JSON of before. Float64, not float32: the host sends link regions back to Lean for
hit tests, and float64 gives Lean's values exactly. The JSON text has Lean's `toString`, which
keeps 6 decimals (373.685313 for 373.68531253425044), so the section values are more exact than
the JSON values.

The desktop host asks for it on the bytes path (`native_html_engine.ts`) and decodes the sections
on first read into the arrays a JSON answer has (`native_html_layout.ts`, `attachLayout`). The
getters are not enumerable, so the engine worker posts the bytes, and the main thread makes the
getters again (`native_html_compile.ts`). The Hub does not ask for it.

| Measure | before | after |
|---|---|---|
| answer head, index.html | 365,788 bytes | 44,992 bytes |
| answer head, status.html | 275,624 bytes | 45,012 bytes |
| Deno decode and parse of the head, index.html | 1.93 ms | 0.03 ms |
| Deno decode and parse of the head, status.html | 0.97 ms | 0.04 ms |

Tests: `layout_sections_test.ts` (decoded values equal the JSON values, directly and through the
worker; pixel data and tile words equal); `native_html_bytes_test.ts` (all demo pages, numbers
within the rounding of Lean's decimal text).

## 5. Stage C: page answers kept or patched against the one the host holds

Request field `have:{page:id}`: the `damage.id` of the page layer answer the host holds. The
engine keeps its last three page answers whole (`Engine.pagesSent`: id, storage bytes, tile
bytes). `pageForHost`:

- this frame's page answer is the held one (`pageAnswerId` of its text): the page is
  `{"kept":id}` and its sections are empty (the chrome's section numbers stay);
- the storage and tile sections have the held sizes and at most half of their bytes changed: the
  page text gets `"dataPatch"` and `"tilesPatch"` (`base`, `[offset, length]` ranges, `size`), and
  its sections hold only the changed bytes (`changedRanges`, `rangeBytes`);
- else the answer as it is.

Refinement: the specification is the whole answer. The patch is computed from the held bytes and
this frame's bytes, so `applyRanges held patch ranges` gives this frame's bytes when
`changedRanges` gives every differing word. `changedRanges` is `changedRangesWith wordsDiffer`;
`wordsDiffer_eq` proves the fast word test (one 8-byte load, `Prim.Bytes.ldU64LEIn`) equal to the
reference (`ldU64LE`). Not proved: that `changedRangesWith` covers every differing byte; checked
by `#guard` lines on test arrays and by the differential check below.

Differential check: `web-render-native PAGE W H --document-bin-check SEQ.json FONT COUNT` sends
each request of the sequence from one engine state twice, with `have` and without, makes the
first whole from the held bytes, and fails at the first difference. Results:

| Page, sequence | kept | patched | whole | equal |
|---|---|---|---|---|
| index.html, 22 steps (chrome changes, hover, scroll bands) | 15 | 0 | 7 | yes |
| status.html, same | 15 | 0 | 7 | yes |
| 120 links, `a:hover` colour, 11 steps | 0 | 10 | 1 | yes |
| 120 links, `a:hover` colour and background, 11 steps | 0 | 7 | 4 | yes |
| small page, hover and `:active`, 12 steps | 1 | 10 | 1 | yes |

A hover that adds a primitive (the background) moves every later record, so the patch is larger
than half and the answer is whole. `layout_sections_test.ts` checks the same through the host.

The desktop host sends `have` for the page on screen (`run_html.ts`) and makes the page whole
(`native_html_layout.ts`, `resolvePage`: kept gives the held page object; a patch writes the ranges
into a copy of the held floats and tile words, and checks the changed floats are finite). The
layer compositor writes only the patched ranges to the GPU buffers when they hold the base answer
(`slot.uploaded`, `queue.writeBuffer` with offsets).

| Measure | without `have` | with `have` |
|---|---|---|
| host `compileLayers` of a frame whose only change is the chrome, index.html, p50 | 4.64 ms | 1.84 ms |
| same, status.html, p50 | 5.20 ms | 1.81 ms |
| hover frame, 120 links, answer bytes | 4,297,900 | 782,064 (of which layout sections 704,622) |
| hover frame, 120 links, callgrind per frame | 119.9 M | 128.8 M (`changedRanges` 7.5 M) |
| hover frame, 120 links, host p50 | 24.4-25.4 ms | 21.6-25.8 ms |

The hover frame is dominated by a whole layout per hover state (`frameWork`: 11 layouts in 11
frames on these pages); that is style invalidation and incremental layout, item 2 of the
briefing, not the display list. Each new layout also has a new serial, so its layout sections are
sent again (704,622 of the 782,064 bytes).

## 6. Band change: first step

`edgesMeeting` (the fill edges of a row band of a tile) made `Array.range` of all edges for each
band. `edgesMeetingLoop` pushes the indices in one tail-recursive loop (`filterRangeGo`,
specialised on the test); `filterRangeGo_range` proves it is `(Array.range n).filter p`, and
`@[csimp] edgesMeeting_eq_loop` makes the compiler use it. Also: the page text is read for its
`damage.id` (`pageAnswerId`) only for a request with layout sections, and `pageForHost` reads it
only when the host holds a page (a match on a pair evaluated both). Band change on index.html,
callgrind per frame: 691.6 M before, 606.6 M after; answers byte-equal over 4 pages and 3
sequences.

## 7. What remains

- Scroll-band change: 607 M instructions on index.html after section 6 (654 M at the base of
  section 2, 692 M at main b8dca504). The retained compile does not
  serve it, and a translation of the band changes every record and tile listing by floating-point
  arithmetic, so equal bytes need the work again. Measured parts to make cheaper with the same
  output: tile listing (48%; `edgesMeeting` allocates `Array.range` per band, `NativeSVGPath.edges`
  builds lists with `zip`), records (`writeRows`, one `push` per byte), and frees of objects marked
  for threads by the parallel listing (`lean_mark_mt`, then atomic reference counts).
- Lean still builds the whole storage section of a changed page (`Retained.dataBytes`) before the
  patch is taken; the retained compile knows the changed items and could give their byte ranges
  directly. That needs the ranges out of `pageArtifactImpl`, whose `implemented_by` must stay
  equal to the reference; not done.
- Layout sections of a new layout with the same boxes and runs are sent again (the key is the
  serial).
- The Hub does not send `layoutSections` or `have`.

## 8. How to measure

```sh
# from labs/demos/foafnaut, after bash build-web-render.sh --native
REQ=... # {"op":"render","url":"https://example.invalid/","resources":[],"commands":[],"checks":false}
.build/web-render/web-render-native pages/index.html 1600 1000 --document-bin REQ FONT OUT.bin 8
# a sequence of requests (JSON array), element i mod n for call i: hover, press, scroll bands
# --document-bin-check SEQ.json FONT COUNT: the stage C equality check
.build/web-render/web-render-native pages/index.html 1600 1000 --document-bin-seq SEQ.json FONT OUT.bin 8
# instructions per frame: callgrind at COUNT 1 and 4, (I4 - I1) / 3
valgrind --tool=callgrind --callgrind-out-file=cg.4 .build/web-render/web-render-native ... 4
```

A layers request needs `"layers":true,"binary":true` and a `shell` object (see `spinal_perf.ts`).
`frameWork` (op) counts `chromesKept` and `framesKept`.
