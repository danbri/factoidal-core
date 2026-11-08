# Cost theorems: how much work a frame takes

Date: 2026-11-08. Author: perf-theorems, a subagent of session depmap-0e.
Related: https://github.com/danbri/factoidal/issues/1268 (responsiveness).

The owner, 2026-11-08: "Can we start introducing theorems establishing such
things don't happen?" (that every scroll step makes the engine lay the whole
page out again), and "They can ratchet us into more performant design space."

## 1. What landed

- `formal/lean4/L4Factoidal/FrameCost/` (library `FrameCost`, only Lean core):
  - `Model.lean`: the host session (layout key, scroll, band on screen, kept
    layout, prefetched band), the events (scroll by `d`, resize, zoom, hover or
    other element state, navigation, font load, prefetch, timer tick), the
    decision for each event (`decideFrame`: `shift`, `swap`, `render`,
    `layout`) and its cost (`Cost`: Lean layouts, Lean band renders, bytes of
    page layer uploaded).
  - `Theorems.lean`: lemmas, then the section `Ratchet` (section 2), then the
    costs of today that a later ratchet is to lower.
  - `Cases.lean`: `lake exe frame-cost-cases` prints 80 event sequences of 40
    events with Lean's decision, cost and band for each event.
  - `Tests.lean`: `#guard` scenarios and the `#print axioms` audit.
- `labs/demos/foafnaut/fixtures/frame_cost_cases.json`: that output.
- `labs/demos/foafnaut/frame_cost_test.ts` (in `test.sh` with the other
  `*_test.ts`): replays every event through the host functions that decide in
  `run_html.ts` (`layer_compositor.keeps`, `scroll_prefetch.stateKey`,
  `sameState`, `canSwap`), taking each band from Lean's answer as the host
  does, and fails on any decision or cost that differs from Lean's: 3,200
  events. It then checks the bounds of section 2 on every case.
- `test.sh` runs `frame-cost-cases --check` on the fixture when the executable
  is built, so the fixture cannot drift from the model.
- `run_html.ts --scroll-sweep`: counts Lean frames, prefetches and rows
  scrolled after the first frame, prints them in the perf summary
  (`frameCost`), and exits with code 1 when the counts pass the bound of
  section 3.

The decision has one source, `decideFrame`. The hosts already take the keep
range of each band from Lean (`keepFrom`, `keepTo` in the `layers` answer); the
rest of the host's decision is the four lines of `run_html.ts` that the
differential test replays.

## 2. The ratchet

The section `Ratchet` of `Theorems.lean` says, under its doc comment, that
these are performance contracts: a change that breaks one keeps the cost bound
or changes the theorem on purpose, and says so in its commit message.

| Theorem | Statement |
|---|---|
| `scroll_in_band_free` | A scroll whose view stays in the band on screen costs 0 layouts, 0 renders, 0 bytes. |
| `scroll_never_layouts` | From a warm session (the kept layout is the layout of the key), no scroll of any size lays out. `apply_scroll_key` is `rfl`: the key has no scroll, as `WebDocument.LayoutKey` has none. |
| `run_scrolls_never_layout` | The same over any sequence of scrolls. |
| `layout_once_per_key` | From a warm session, layouts over any event sequence are at most the events that changed the key. |
| `layout_once_per_key_from_start` | From any session, the first frame included: at most one more. |
| `band_render_bound` | A scroll-only sequence that starts on a band made at its own scroll, with no band drawn ahead, draws at most `travelled / (reach view + 1)` bands, all from the kept layout. `reach` is 384 rows for a view of up to 3,072 rows. |
| `composite_correct` | For every scroll the band keeps, the composite equals the frame of a full render at that scroll (`composite_eq_frame`). |
| `tick_free` | A timer tick with no DOM change costs nothing. |
| `prefetch_never_layouts` | A prefetch draws one band from the kept layout, or nothing. |

Axioms: only `propext`, `Classical.choice` and `Quot.sound` (the audit in
`Tests.lean`). No `sorry`, `native_decide` or `bv_decide`.

Two of the requested statements are stated differently, because the code does
something else:

- **Distinct keys.** The kept layout is one entry (`WebDocument.layoutRef`). A
  hover on and off lays out twice for two distinct keys
  (`one_entry_relayouts`). So the bound is by key changes. A memo of more
  entries would make the bound by distinct keys true; that is a ratchet to
  take (section 4).
- **Band height.** The requested bound was distance divided by (band height
  less view height), plus 1: 1,024 rows per band. A band made on demand is
  centred on the scroll and is replaced when the view comes within 128 rows of
  its edge, so the true spacing is `reach + 1` = 385 rows. The prefetch, which
  makes the next band start where this one's keep range ends, gives 768 rows
  per band on a steady scroll. The model does not yet have the prefetch rule
  (`scroll_prefetch.prefetchTarget`) in it, so the 768-row bound is not
  proved.

## 3. The bounds the hosts check at run time

- `frame_cost_test.ts`, in every `test.sh` run: no scroll after the first frame
  lays out; every shift costs nothing; layouts per case at most key events
  plus 1; band renders in each run of scrolls at most rows / 385.
- `run_html.ts --scroll-sweep` (macOS, a window): Lean frames after the first
  at most `rows / (reach + 1) + 1`, and prefetches at most the same. A
  prefetch that comes late (`missed`) costs a frame as well, which the `+ 1`
  and the separate prefetch count allow; anything more fails the sweep.
- The Hub: hub-perf is porting band scrolling to `browser-worker.mjs`. The
  same counters go into its test once that lands (coordination log).

## 4. The next ratchets

Each is a theorem to state in the model first, at today's cost where the code
is slower, and then to lower:

1. **Pinch zoom lays out only on whole 5% steps.** Between steps the
   composite scales the layers. The key would hold the zoom rounded to 5%.
2. **Hover and `:active` repaint only.** Today `hover`, `active` and `visited`
   are in `WebDocument.layoutFields`, so each change is a layout
   (`element_change_lays_out` states it). The target: a change of element
   state that no rule with a layout property depends on costs one render from
   the kept layout and no layout. Needs the cascade to say which properties a
   `:hover` rule sets.
3. **Typing in the address bar never lays out the page.** The chrome is its own
   layer; a key in the bar redraws the chrome layer only. State it as: an
   address-bar event costs 0 page renders.
4. **A font load lays out once.** Today each `fontLoad` gives a new key; a page
   whose fonts arrive one by one lays out once per font. Target: fonts that
   arrive within one frame are one layout.
5. **An image arriving lays out only its line or block.** Needs incremental
   layout: a layout that takes the old boxes and the changed node and gives
   the new boxes, with a theorem that it equals the full layout, and a cost in
   boxes visited.
6. **A timer tick with no DOM change costs 0.** `tick_free` states it for the
   model; the host side needs the event loop (`L4Factoidal/EventLoop`) to say
   "no DOM change" to the frame scheduler, so that a tick does not mark the
   page dirty.
7. **A memo of more than one layout.** Turns `layout_once_per_key` into a bound
   by distinct keys, so hover on and off costs one layout at most.
8. **Prefetch in the model.** Add `prefetchTarget` to the model and prove the
   768-row spacing for a steady scroll. The model shows a cost the hosts have
   today: a fast scroll that turns back and forth inside one band asks for a
   new prefetch at each turn (the host skips only a prefetch with the same
   target as the band already held). A two-slot prefetch would bound it.
9. **Image bytes cross the host boundary once per image, not per frame.**
   A known violation today: the `<img>` work (92e82d268) sends each image's
   bytes as Base64 inside every render request, so a page with large images
   pays their JSON size on every frame, a scroll that renders a band
   included. The fix is a held-image operation like `fontLoad`: the host sends
   an image once, Lean keeps it by SHA-256, and the render request names it.
   Issue https://github.com/danbri/factoidal/issues/1274. The model gets a
   cost field for bytes sent to Lean and a theorem that, for a fixed set of
   images, those bytes over any event sequence are at most the sum of the
   image sizes. Until then this is a target, not a passing bound.
10. **WasmVM instruction counts.** A cost model for the fused instructions of
   the WasmVM: each fused op does the work of the ops it replaces in fewer
   steps, proved per op over the step relation.

## 5. Follow-ups

- `WebDocument.lean` has its own `Band`, `band`, `keepFrom`, `keepTo`,
  `composite` and `composite_eq_frame`. The model repeats them with the same
  numbers and the same proof; the differential test checks the numbers against
  Lean's answers in the fixture, not against the engine. When `WebDocument`
  imports `L4Factoidal.FrameCost` and uses these definitions, the repetition
  goes and the theorems are about the engine's own definitions. That needs an
  engine build (`build-web-render.sh`), which this change did not do.
- The memo statement is proved over the model's one-entry kept layout. The
  engine's `lookupLayout_eq` and `stored_valid` say the same entry gives the
  layout of the key; an instance of one abstract memo for both would follow
  "Prove over an abstraction".

## 6. Round 2 (ratchet-2, 2026-11-08): the costs the theorems exposed, lowered

Related: https://github.com/danbri/factoidal/issues/1292.

### The model is the engine's code

- `FrameCost/Band.lean` holds `Band`, `band`, `keepFrom`, `keepTo`, `keeps`, `fits`,
  `composite` and `composite_eq_frame`. `WebDocument` imports it and exports these
  names; it no longer has its own copies (`build-web-render.sh` builds the two
  modules into the engine).
- `FrameCost/Lru.lean` is the layout memo: `find?`, `put` (least recently used out),
  `lookup`, with `lookup_eq` and `put_valid`. `WebDocument.layoutRef` is an
  `Lru LayoutKey Laid` of `layoutSlots` (4) entries of one document (`Lru.putIn`
  scoped by `LayoutKey.html`: a layout of another page drops them; with four pages kept,
  `native_html_bytes_test.ts`, two engines over every demo page, was killed at 2.6 GB);
  `lookupLayout_eq` and `stored_valid` are now instances of `Lru.lookup_eq` and
  `Lru.putIn_valid`. The model
  keeps the same memo with its values left out (`Session.kept : Lru Key Unit`), and
  `Lru.erase_putIn` and `Lru.find?_erase` (`WebDocument.model_put`, `model_hit`) prove that leaving
  out the values commutes with every operation: the model's cache hit is the engine's.
- The key: `WebDocument.pointer_not_layout_field` ("shell", "hover", "active" are not
  layout fields), `layoutRequest_congr` (requests that agree on the layout fields have
  one layout request) and `shell_height_scroll` (the chrome height does not read the
  scroll) are the engine lemmas behind the model's `apply_scroll_key` and
  `apply_hover_key`.

### Hover and `:active` repaint

`hover` and `active` left `layoutFields`. A page is laid out once with no pointer state;
a frame with one re-runs the cascade and `WebRepaint.recolor` maps the colours of the
paints of the nodes whose styles changed. When a changed style changes anything but
colours (`WebRepaint.sameShape`: a font size, a padding, an underline that comes or goes,
a background that comes or goes, a table, SVG or a replaced element), `restyle` answers
none and the frame lays out with the pointer in the key (`LayoutKey.pointer`).
`WebDocument.frameWith_eq`: with a valid memo and a sound restyle (`RestyleSound`, which
`WebDocumentTests.lean` checks on ten pointer-style pages and a button, `run` against
`runUncached`), a frame is the layout of its key.

### Held images

`imageLoad` (Base64) and `web_document_image_call_bin` (bytes) hold an image by key and
SHA-256 (at most 64 images, 32 MiB). A render names them in `heldImages`; the key holds
the names found. `imageInfo` answers the ops; the native host (`prepareHTML`,
`imageOptions`) and the Hub worker use held images only when it does, and send `images`
with the bytes to an older engine (issue 1274). The native dylib symbol is optional.

### The ratchet now states

| Theorem | Before | Now |
|---|---|---|
| `hover_never_layouts` | `element_change_lays_out`: 1 layout | 0 layouts for a colour-only pointer state |
| `hover_geometry_layouts` | (none) | at most 1, and 0 when that key is kept |
| `layout_once_per_distinct_key` | bound by key changes (`one_entry_relayouts`: hover on and off = 2) | in a window of at most 4 keys of one page, each key at most once; `hover_on_off_paint` = 0, `hover_on_off_geometry` = 1 |
| `prefetch_band_spacing`, `prefetch_chain` | 768 rows not proved | the rule's next band starts its keep range where this one ends and ends 768 rows on (view up to 3072) |
| image bytes per frame | the Base64 of every image in every request | the names only: `frame_work_test.ts` counts equal bytes per frame for a 272-byte and a 556 KB image |

The swap of a prefetched band now asks, as `canSwap` does, that the band on screen be of
the same state (`shownFor`); the fixture found the model swapping where the host would not.

### Not done

- The turn back and forth inside one band still asks for a new prefetch at each turn (one
  prefetch slot in `run_html.ts` and the Hub). Two slots would bound it; that touches
  `run_html.ts`, the Hub worker and the model's `prefetched`, and is left for the next round.
- An underline that comes on hover (`a:hover{text-decoration:underline}`) lays out: its
  rectangle is placed by the line layout.

## 7. Links to the foot of the page (link-theorems, 2026-11-08)

The bug of 0e4f29e01: `render` passed the viewport height to `linkRegions`, so a link
below the first screen had no region and a click on it in the Hub's band did nothing. The
owner: "Derive a theorem from this to protect us." `formal/lean4/L4Factoidal/Rendering/LinkTheorems.lean`:

| Theorem | Statement |
|---|---|
| `linkRegions_complete` | A box in an anchor, visible, not empty once clipped (`linkBox`), inside `[0,width) × [0,height)`, has a region with the anchor's source node and href, at the box's corner. |
| `linkRegions_complete_document` | At `linkHeight vh doc` (= `max vh doc`, what `render` passes), the only vertical condition is that the box ends at or above `doc`, for any `vh`. False with `vh` alone, which is the bug. |
| `render_links` | `render`'s links are `linkRegions` over the boxes it returns, at `linkHeight vh result.height`, where `result` is the layout (`block …`) those boxes come from. |
| `render_link_complete` | The two together: every such box of a rendered page that ends at or above the foot of its layout has a region in the scene. |
| `linkRegions_eq_before` | `linkRegions` (now `filterMap linkRegionOf`) equals the fold of 0e4f29e01 word for word: the change of shape changes no render. |
| `moveLinks_getElem`, `mem_moveLinks` | Moving the links of a band or of a page under the chrome keeps every link, same source, href, x, width, height; y moved only. `WebDocument.pageLayer_links` and `WebShell.compose_links` (both `rfl`) say those functions are such moves. |
| `hitLink_band` (with `hitLink_moveY`, `band_row`) | A hit at page-layer row `row` is the page's own hit at row `row + band.top`, moved; window row `y` of a band is page row `y - top + scroll`. Given that the move is exact in `Float` for each link at that point (hypothesis `exact`: true for whole numbers below 2^53, not proved). |

`Float` order: Lean 4.33 defines `<` and `≤` on `Float` through its IEEE model
(`Float.Model.UnpackedFloat`) but proves nothing about them.
`L4Factoidal/Rendering/FloatOrder.lean` proves `le_trans` and `lt_of_lt_of_le` (every
`Float`, `NaN` included) by a key in `Int × Int × Int` whose lexicographic order is the
model's comparison, and from them `lt_min_max`: `t < b ≤ H → t < min (max v H) b`.

Axioms of all of these: `propext`, `Classical.choice`, `Quot.sound` at most (audit in
`Rendering/Tests.lean`). No `sorry`, `native_decide` or `bv_decide`. A guard in
`Tests.lean` checks the hit through a band on the `lowLink` page.

Not proved: that every box of a layout ends at or above `result.height` (true of normal
flow, not stated); the `Float` exactness of a move by whole rows.
