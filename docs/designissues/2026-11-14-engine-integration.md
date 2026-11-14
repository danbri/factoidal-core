# How the engine's parts fit together, and where the hosts differ (2026-11-14)

Status: living record, started at main `eccbb6b7f`. It maps the components of BubblePopKit, the interface
between each pair, the path a page takes in each host, and every place found so far where the WPT runner
and the browser hosts do different things for the same page. Each difference is a place where the WPT
score says more than the browser shows. Sections 3 to 6 are ordered by how much they explain that gap.

Method: read from the source at the commit named; the two runs marked "measured" were made with the
release engine of `25c3a4510` (macOS arm64). Nothing here is from a sample.

## 1. The components and the data flow

```
                         HOST (TypeScript / .mjs / Objective-C): moves bytes, opens windows, runs GPU commands
  ┌──────────────────────────────────────────────────────────────────────────────────────────────────────────┐
  │ fetch(document)   fetch(sheets, classic src scripts, images, fonts, icon)    fetch(page requests)  input  │
  └─────┬───────────────────────────┬──────────────────────────────────────────────────┬──────────────┬──────┘
        │ bytes + Content-Type      │ text / bytes by node id or key                   │ answers      │ clicks, keys,
        ▼                           │                                                  │              │ time, resize
  decodeDocument                    │                                                  │              │
  (WHATWG/Encoding/Sniff)           │                                                  │              │
        │ text                      │                                                  │              │
        ▼                           │                                                  │              │
  parse ── HTML/Tokenizer, TreeBuilder, DOM/OfHtml; or DOM/OfXml when the URL path     │              │
        │  ends .xht/.xhtml/.svg (DOM.isXmlPath)                                       │              │
        ▼                           │                                                  │              │
  DOM arena (DOM/Arena) ◄───────────┼───────────────────────────┐                      │              │
        │                           │                           │ typed commands       │              │
        │   op `inspect`: what to fetch (scripts, stylesheets,  │ (Hosts/Dom.Command)  │              │
        │   images, icon), URLs resolved by Lean                │                      │              │
        │                           │                  ┌────────┴───────────────────┐  │              │
        │                           └─ resources ────► │ SCRIPT SESSION             │◄─┘              │
        │                                              │ WebScripts.lean            │◄────────────────┘
        │                                              │  BubblePopJS (L4Factoidal/JS, Hosts/LeanJS)
        │                                              │  or QuickJS-NG in WasmVM (Hosts/Page)
        │                                              │  prelude.js (page objects) ─ numbered ops ─►
        │                                              │   Hosts/Dom, DomOps (node_query, tree_op),
        │                                              │   Hosts/WebApi (web_api), Net/Xhr, Net/Storage,
        │                                              │   Net/Cookies, CssValues.styleOp, ...
        │                                              │  EventLoop (timers, frames, dispatch order)
        │                                              │  Net/PageFetch (CORS, redirects, addresses)
        │                                              │  layout reads ─► WebDocument.measure ─┐
        │                                              └────────┬───────────────────────────┘  │
        │        render request: html + `commands` (JSON)       │ turn: commands, logs,        │
        ▼                                                       │ netRequests, fetches,        │ the session's
  WebDocument.prepareDOM = parse(html) then applyCommands ◄─────┘ navigations, gpu             │ own arena
        │  (a second DOM, rebuilt for the render)                                              │
        ▼                                                                                      ▼
  STYLE   sheetsIn (style elements + supplied link sheets) ─► CSS.parseInRaw ─► CSS.computeFor (Rendering/Style.lean)
        │   media: Rendering/MediaQuery; the profile record `CSS.Computed`
        │   script reads of computed values: ComputedValues.text (the profile) and ComputedGeneric.valueAt
        │   (declared values from the property table, Rendering/CssValues) ── a second answer, section 4
        ▼
  LAYOUT  WebDocument.layOutDOM ─► Rendering/Layout.lean, TableLayout.lean, fonts (Sfnt*, FontPolicy)
        │   `Laid`: scene, boxes, glyph runs, link regions
        ▼
  PAINT   WebPaint, WebRepaint (hover/active), WebRender.artifactWith ─► GPU data + WGSL, or CPU pixels
        ▼
  HOST    runs the GPU commands, shows the frame; page canvases through PageGpu commands
```

Storage (`Net/Storage`, `Net/Cookies`, blob URLs) and the network state live in the script session's
`WebApi.State`. Fonts and images the host fetched live in the engine's `Holds`, by SHA-256.

Interfaces, and where each decision is made:

| From → to | Interface | Decided by |
|---|---|---|
| host → decode | `web_document_decode2_bin(bytes, contentType, fallback, locale)` | Lean (`WebDocument.decodeBinWith`) |
| decode → parse | text; HTML or XML syntax by the URL's path ending (`DOM.isXmlPath`) | Lean, but from the URL, not the Content-Type (section 3, item 13) |
| parse → host | op `inspect`: scripts (classic only), stylesheets, images, icon, base URL, title | Lean lists; the host then applies its own limits and origin rules (section 3) |
| host → style | request fields `resources` (sheet text by node id), `resourceFailures` | Lean (`sheetsIn`); 64 sheets, 4 MiB a request, 2 MiB of sheet text |
| DOM → scripts | the arena; numbered imports (`foafnaut_dom`, `node_query`, `tree_op`, `web_api`) | Lean serves; `prelude.js` shapes objects (section 5) |
| scripts → DOM | `Hosts.Dom.Command` values applied to the session's arena | Lean |
| scripts → render | the cumulative command list, as JSON, in each render request (`commands`) | Lean replays it on a fresh parse (`WebRenderScript.applyCommands`) |
| scripts → layout | `Page.Measure` = `WebDocument.measure`: `layOutDOM` on the session's arena | Lean; same cascade and layout functions as a render |
| scripts → network | turn fields `netRequests`, `netSync`, `fetches`, `navigations`; answers by `net`, `syncAnswer`, `fetched`, `frame` | Lean (`Net.PageFetch`), with host flags (section 6) |
| style → layout | `Array CSS.Computed` (the profile record) | Lean |
| layout → paint | `Laid` (scene, boxes) | Lean |
| paint → host | answer of `render`: GPU buffers, WGSL, link regions, `webRender.boxes` | Lean emits, host runs |

## 2. The path of a page in each host

| Step | WPT runner (`tests/browser-wpt/testharness-run.ts`) | Window (`run_html.ts`, `native_html_document.ts`) | Textnaut (`textnaut/textnaut.ts`) | Hub (`docs/web/hub/foafnaut/browser-worker.mjs`) |
|---|---|---|---|---|
| Document bytes | wptserve over HTTP, or the checkout's file | host `fetch` or file | as the window (`prepareHTML`) | host `fetch`, this site only |
| Decode | `decodeDocument` | `decodeDocument` | `decodeDocument` | `web_document_decode*` |
| XSLT (`<?xml-stylesheet?>`) | no | `xmlStylesheet` + `xslt` | as the window | `xmlStylesheet` + `xslt` |
| `inspect` | yes | yes | yes | yes |
| Linked style sheets | fetched, up to 64, any WPT host | fetched, up to 16 and 32 MiB, any HTTP(S) origin | as the window | **not fetched** |
| Classic `src` scripts | fetched | fetched | fetched | fetched |
| Module scripts | by the session (`netSync`), host answers | by the session, host answers | **not answered** (no `network`) | by the session, host answers |
| Images | only for `/canvas/` tests (regex on the page text) | fetched, **page's origin only**, 4 MiB each, 6 MiB a page | as the window | fetched, this site only |
| Web fonts (`@font-face`) | fetched, any WPT host, 8 MiB | fetched, **page's origin only**, 8 MiB each | as the window | fetched, this site only |
| Font at start | none: the bitmap face unless the page has a web font | Noto Sans + fallback fonts by script coverage | bitmap metrics by design | Noto Sans + fallback fonts |
| Script session `start` | `layout` with sheets and fonts; `commandLimit:200000`, `logLimit:100000`; `navigations:true`; `network:true`; `pageAddress:"127.0.0.1"`; script clock off | `layout` with the render's fields; default limits (4096 commands, 1024 log lines); `network:true`; viewport, shell | `layout` at text size 100; default limits; no `network` | `layout` **without sheets**; default limits; `network:true`, `hostCors:true` |
| Script engine | `engine:"bubblepop"` | Lean's plan for host "native": BubblePopJS | BubblePopJS | Lean's plan, asked as host "native": BubblePopJS |
| Time | `settle`: virtual time runs until quiet (70 s budget) | `advance` by real time each frame | `advance`, at most 8 turns and 1 s | `advance` by real time |
| Worker and imported scripts (`fetches`) | fetched; Content-Type and `X-Content-Type-Options` passed | fetched; **type passed as ""** | not answered | fetched; **type passed as ""** |
| Frames (`navigations`) | answered with action `frame` | **not asked for**: an `<iframe src>` stays `about:blank` | not asked for | not asked for |
| Page requests | `net` answers from wptserve | `net` answers (`native_net.ts`) | none | `net` answers; CORS left to the host browser (`hostCors`) |
| Viewport | 800 × 600 CSS px, text size 100 | the window; **text size 200 by default** (150 at `25c3a4510`), so half the CSS width | columns × rows of the terminal | the canvas; text size 200 by default |
| Render | never: results are console lines | `render` with `commands`, layers, GPU | `render`, then a text grid | `render` with `commands`, layers, GPU |
| Hit test for clicks | none | `nodeAt` with the render's options | — | `nodeAt` with **fewer layout fields than the render** |

## 3. Where the score says more than the browser shows

Ordered by how much of the gap between the WPT number and what a person sees each one explains. "R" is
the runner, "W" the window, "T" Textnaut, "H" the Hub.

1. **The cascade that draws the page is a second, small CSS engine.** This is the largest cause, and it
   is inside the engine, not in a host. `Rendering/Style.lean` has its own sheet reader (`parseRaw`), its
   own selector grammar (`compoundBody`, `selector`: tag, `#id`, `.class`, five pseudo-classes, the
   descendant combinator only) and its own value readers (`length`, `color`, `apply`: 40 properties).
   A rule with any other selector is dropped; so is a declaration with `var()`, `calc()`, `em` or `rem`.
   `querySelector`, CSSOM, `getComputedStyle`, `element.style` and `CSS.supports` use other code
   (`DOM/Selectors.lean`, `Rendering/CssSheet.lean`, `Rendering/CssValues/*`, `ComputedGeneric`), and
   that code is what WPT measures. Measured here on the engine of `25c3a4510` with one rule each
   (`#p>div{height:40px}` and so on, read back with `getBoundingClientRect`): no effect on layout for
   `>`, `+`, `:is`, `:where`, `:not`, attribute selectors, `:first-child`, `rem`, `calc()`, `min()`,
   `clamp()`, a custom property through `var()`, `block-size`, `@supports`, `@layer`, nesting, and a
   selector list that holds `:focus-visible`. The source of main `eccbb6b7f` is the same in these
   functions. The full diagnosis on eight live pages, with counts for each page, is agent `pages`'s
   record (`night/pages.md`; 24% to 69% of each page's rules are dropped for the selector alone).
   Owners: `pages` (selectors through `DOM.Selectors`, sheet limits, at-rules), `css-values` (the sheet
   reader, custom properties, values), `layout` (flex, grid, positioning). Section 4 says which copy to
   keep.
2. **The browser lays pages out at half width.** W and H start at text size 200 (`WebSelection.defaultPercent`;
   150 in the engine of the captures). The text zoom divides the viewport that media queries and
   percentages see (`WebDocument.mediaEnv`, `layoutInputs`): a 1600-pixel Retina window is 800 CSS px,
   and 400 CSS px to the page at size 200. Every responsive site therefore gives its phone layout, with
   body text twice the usual size; R lays out at 800 × 600 and size 100. The eight captures in
   `shots/out` were made at 533 CSS px (1600 device px, 2x, size 150). This is a setting, not a defect
   of the cascade, and it is the first thing to hold fixed when a capture is compared with another
   browser. Proposed: the capture tool and the fixtures of section 7 state the text size; a capture for
   comparison is made at size 100. The default is the owner's choice and is not changed here.
3. **The painted DOM is a second DOM.** Scripts change the session's arena; the render parses the page
   source again and replays the command list (`prepareDOMIn`). WPT reads only the session's arena
   (through `measure`), so nothing in WPT checks the replay. Two limits exist only on the render side:
   `applyCommands` refuses more than 4096 commands, and W, T and H leave the session's `commandLimit` at
   its default of 4096 (R sets 200,000). A page whose scripts make more than 4096 distinct DOM writes
   gets `RangeError: DOM budget exceeded` in the browser and passes in R. The list is also sent as JSON
   in every render request and compared in the layout key. Plan in section 5, item A.
4. **The Hub does not load linked style sheets.** `prepare()` reads `facts.images`, the web fonts, the
   icon and the scripts; `facts.stylesheets` is never read, and neither the render request nor the
   session's `layout` has `resources`. In liberal mode (the default) every `<link rel=stylesheet>` is
   skipped (`stylesheetMissing`) and the page is drawn with inline styles only; in strict mode the page
   is refused. No published demo page links a sheet, which is why it was not seen. Section 8 says what is fixed.
5. **Images and web fonts from another host are refused by the host.** `imageAllowed`
   (`native_html_document.ts:71`) lets W and T fetch images and fonts of the page's own origin only; H
   fetches this site only. This is a policy decision in TypeScript, not in Lean. Sites serve images and
   fonts from other hosts, so they show alt text and fallback fonts. R fetches fonts from every WPT host
   and images only for canvas tests. The engine also asks only for `<img src>` and SVG `image`: no
   `srcset`, `<picture>`, CSS `background-image` or `data-src` lazy loading. (Agent `pages` owns images;
   the move of the origin rule into Lean is item C of section 5.)
6. **Two answers to "what is the computed value".** A render and a layout read use the profile record
   `CSS.Computed`. `getComputedStyle` reads `ComputedValues.text` for profile properties and
   `ComputedGeneric.valueAt` (declared values through the property table) for the rest, and for the
   properties in `ComputedGeneric.declaredWins` the declared value wins over the profile. A property
   that the table can parse and serialise but layout does not read passes WPT's computed-value tests
   and changes nothing on screen. Section 4.
7. **Storage and cookies end with the page.** `localStorage`, `sessionStorage` and `document.cookie` live
   in the script session (`WebApi.State`), in memory. A navigation closes the session, so a site sees a
   first visit on every page (cookie banners, themes, logins). The document and subresource fetches are
   the host's and carry no cookie from the engine's jar; `Set-Cookie` of the document does not reach it.
   WPT tests within one page. Needs a store in the engine's state keyed by origin (not the session), and
   a decision on persistence; agents `net` and `storage` own the parts.
8. **Frames are loaded only by the runner.** R sets `navigations:true` and answers each navigation with
   the frame's document and scripts. W, T and H do not, so an `<iframe src>` keeps `about:blank`.
   23,712 subtests of `html/the-xhtml-syntax` alone were gained through this path.
9. **Document and subresource loads are outside the engine's network policy.** Only requests made by
   scripts (and module graphs) go through `Net.PageFetch`. The page, its sheets, classic scripts, images
   and fonts are fetched by the host's own `fetch`, with the host's redirects, no referrer policy, no
   CSP, no mixed-content check, and with response headers other than Content-Type dropped. WPT's
   policy tests exercise `PageFetch`; the browser's own loads do not pass through it.
10. **A security theorem whose hypothesis the browser hosts do not supply.**
   `LeanJSWorkers.scriptAccepted_nosniff` says a worker script with `nosniff` and a non-JavaScript type is
   refused. W and H answer `fetched` with `contentType:""` and no `contentTypeOptions`, and an empty type
   is accepted, so in the browser the check never runs. Section 8 says what is fixed.
11. **The Hub's hit test uses another layout than its render.** `nodeAt` is sent with `url`, the text size,
    `zoomUnit`, `shell` and `commands`, without `liberal`, `images`, `heldImages`, `webFonts` (and now
    `resources`). The key differs, so a second layout is made for each click, with no images and in
    strict mode: on a page that needs liberal mode the click is lost. Section 8 says what is fixed.
12. **Time.** R runs virtual time to quiescence with the script clock off; W and H move the clock by real
    time, with the script clock at 100,000 instructions a millisecond. Code that settles in R can be
    seconds of real time in the browser (lean-lang.org's start turn took 12.5 s of engine time).
13. **HTML or XML by the URL's ending.** `prepareDOMIn` chooses the XML parser from the path
    (`.xht`, `.xhtml`, `.svg`), not from the Content-Type. An XHTML page served as
    `application/xhtml+xml` at a path without that ending is parsed as HTML in every host; wptserve's
    names happen to carry the ending.
14. **Fonts.** R lays text out with the bitmap face (one advance for every glyph) unless the page loads a
    web font; W and H shape with Noto Sans. Line breaks and widths that WPT checks are therefore those
    of another font path than the one readers see, except in tests that load Ahem.
15. **Textnaut has no page requests** (`network` is not set): `fetch` and `XMLHttpRequest` are undefined
    and a module script's graph is never answered.

Not differences (checked): the window host does fetch linked sheets and gives them to both the render
and the session's `layout`; module scripts are fetched by the session in every host with `network`
(the "module script N is not run" lines of the captures are from the engine of `25c3a4510`, before
module scripts); the script engine default is BubblePopJS in W, T, H and R.

## 4. Parallel machinery, and which to keep

| Item | Copies | Keep | Size |
|---|---|---|---|
| The page's DOM | the session's arena; `parse + applyCommands` for each render | the session's arena (item A) | large |
| Selectors | `DOM/Selectors.lean` (Selectors 4, total parser and matcher: `querySelector`, CSSOM); `Style.lean` `compound`/`selector` (the cascade) | `DOM/Selectors.lean`, with the cascade's rule index keyed on its rightmost compound | medium (`pages`) |
| Style sheet readers | `Style.parseRaw` (the cascade); `CssSheet.lean` (CSSOM rules); `FontFaceRule.ofSheets`; `Rendering/SheetReader.lean` planned on `wip/css-values` | one reader that gives typed rules to the cascade, CSSOM and `@font-face` | large (`css-values`) |
| CSS values | `Style.length`, `Style.color`, `Style.apply` (40 properties); `CssValues/*` (the property table: grammar, parse, serialise) | `CssValues`; the profile record becomes a view of it (item B) | large (`css-values`) |
| Media queries | `MediaQuery.lean` for sheets and `media` attributes; `matchMedia` answered `false` for `(min-width: 700px)` at 800 px while the `@media` block applied (engine `25c3a4510`; to be measured again on main) | `MediaQuery.lean`, with the layout's environment given to `matchMedia` | small |
| Computed style | `CSS.Computed` (Style.lean: what layout reads); `ComputedGeneric` + `CssValues` (what scripts read) | one record made from the property table, read by both (item B) | large |
| Request assembly | each host builds `render`, `nodeAt`, `layout`, `selectedText`, `printLayout` requests by hand | one function per host now; `layoutFields` given by the engine next | small (done for H) |
| Page loading | `prepareHTML` (W, T), `prepare` (H), the runner's `run` | one loader module (item D) | medium |
| Script engine default | `WebRenderScript.defaultEngine` says QuickJS for "hub" and "wasm"; every host asks as "native" | BubblePopJS for every host name; QuickJS only by setting | small |
| Op numbers | literals in `prelude.js` and in `Hosts/Dom`, `DomOps`, `WebApi`, `Net/Xhr`, `Net/Storage`, ...; ranges claimed in the coordination log | one table checked by a tool | small |
| Limits | sheets: 16 (W), 64 (R, Lean); sheet bytes: 32 MiB (W), 4 MiB a request and 2 MiB of text (Lean); commands: 4096 / 200,000 | Lean's, reported by `inspect` | small |
| XPath | `L4Factoidal/XPath` (1.0, used by XSLT 1.0 and now DOM XPath on `wip/xml-specs-xmlweb`), `L4Factoidal/XPath4` (4.0) | both: they are two languages; DOM XPath belongs on the 1.0 engine, as that branch does | none |
| Lab server | `labs/demos/foafnaut/web-render/server.mjs` with its own QuickJS worker path | remove or mark as not a browser host | small |

`prelude.js` is 516 kB and `webassembly.js` is compiled in beside it. The sections that hold spec
algorithms in JavaScript rather than shaping objects are listed in section 5, item E, as they are found.

## 5. Consolidation plans

- **A. One DOM for scripts and paint.** The engine's state already holds the session (`Engine.scripts`).
  A render of a page with a session takes the session's arena: the layout key names it by
  `(session, changes)` in place of the command list, and `layOut` is split into the parse and
  `layOutDOM`, which `measure` already calls. Gains: no 4096 cap, no JSON of the command list in each
  request, no second parse, and the theorem "what scripts measure is what is painted" becomes a
  definitional equality (section 6). Cost: the memo's validity (`Lru.Valid (layOut h)`) must be restated
  over a function of the key and the arena. Owner: `integration`, after the cheap step (one bound for
  commands in Lean, the same for the session and the replay).
- **B. One computed style.** `CssValues` is the table; `CSS.Computed` should be a view of it, so that a
  property is either read by layout or reported as not supported by `CSS.supports` and
  `getComputedStyle`. First step: a test that lists the properties in `declaredWins` and those answered
  only by `ComputedGeneric`, so the set is visible and can only shrink. Owner: `css-values` with
  `layout`.
- **C. Loading policy in Lean.** `inspect` answers, for each resource, whether the host may fetch it
  (origin rule, size cap) so that `imageAllowed`, `MAX_RESOURCES` and the Hub's `siteOrigin` checks
  leave the hosts. Then the same decision function can be proved to refuse what it must. Owner: `pages`
  for images, `net` for the policy.
- **D. One page loader.** A module that holds the steps every host takes between `inspect` and the first
  render (which sheets to fetch, the layout fields of every request, the answer to a script fetch, the
  session's `start` request), with `fetch` and the engine call injected: `docs/web/hub/foafnaut/page-load.mjs`,
  used by H, W, T and R. A source check then fails when a host builds one of these by hand.
- **E. Spec algorithms in `prelude.js`.** To be listed section by section; each is either moved to a
  built-in or stays as object shaping.

## 6. Theorems across the seams

A theorem about one component can be recombined only if its hypotheses are what the neighbour provides.

| Theorem | Hypothesis | Provided by the neighbour? |
|---|---|---|
| `LeanJSWorkers.scriptAccepted_nosniff` | the host passes the type and `X-Content-Type-Options` | R yes; W and H no before this branch |
| `Net.PageFetch` CORS theorems (`corsOk`, preflight) | `page.hostCors = false` | W, T, R yes; H sets `hostCors:true`, so none of them speak about the Hub |
| `Net.Storage.op_partition`, `op_noninterference` | the origin is the session's page origin | yes, in every host; but the store ends with the session (item 6) |
| `WebDocument.lookupLayout_eq`, `layoutRequest_congr` | requests agree on `layoutFields` | H's `nodeAt` did not (item 10) |
| `WebDocument.layOut_liberal_conservative` | stated with nothing kept | `layOutDOM` passes what the strict run kept; not proved equal |
| `parseIn_eq`, `sheetIn_eq` | `Kept.Valid` | maintained by `Engine.layOutKept`; not proved as an invariant of the engine |

Host-supplied fields that change a policy decision (a host can relax the engine with each): `hostCors`
(no CORS check, no preflight, redirects followed by the host), `pageAddress` (a local address lets the
page reach local addresses), `network`, `navigations`, `liberal`, `scripting:false`, `commandLimit`,
`logLimit`, `instructionsPerMs`. Section 8 lists what is proved about them.

## 7. End-to-end fixtures

Original pages that use features together, each with the facts expected of it, run through the runner's
path and the browser hosts' path. Section 8 says what exists and what runs where.

## 8. Done in this branch, measured, and open

| Item | State |
|---|---|
| This record | first version, main `eccbb6b7f` |

Proved: nothing yet. Tested only: the two measurements named in section 3, item 1 and section 4
(media queries), on the engine of `25c3a4510`. Open: everything in sections 3 to 5.
