# Foafnaut release notes, 2026-11-10

Changes on `main` of https://github.com/danbri/factoidal-core since 2026-11-08 (commits after `49dd1eaab`, to `41a1aaeab`).

These parts are not in the npm package `@factoidal/core`. The Lean wasm dispatch table (`formal/lean4/Wasm/Dispatch.lean`) does not import the JavaScript engine, the WebAssembly engine or the rendering modules. The browser ships in the build sets `foafnaut-darwin-arm64` and `foafnaut-web` of https://github.com/danbri/factoidal-builds, and on the Hub.

Scope rule for "no `unsafe`, no `@[implemented_by]`": the count is 0 and 0 in `formal/lean4` (`tools/lean-hygiene-audit.py`). The audit does not read `labs/demos/foafnaut`, where the browser's engine modules have 29 `@[implemented_by]` and 29 `unsafe` definitions (https://github.com/danbri/factoidal-core/issues/390, engine state kept in `IO.Ref` cells). A statement about those two counts is true only with this scope.

## BubblePopJS (JavaScript engine)

- BubblePopJS is the default page script engine on the Hub and in the Foafnaut Wasm build. A saved setting is kept, and QuickJS-NG stays a choice in Settings. The QuickJS-NG guest is fetched and translated only when a page runs on it: the first frame after a script has run came at 1,455 and 1,522 ms against 1,936 and 1,888 ms on a default page (commit message of `226c14a0a`).
- A trap in the script engine does not stop the page. The page stays as drawn, its scripts stop, the browser bar says JS STOPPED, and the console tab gives the cause. The page does not move to QuickJS-NG.
- Wasm build: a use after free that stopped BubblePopJS is repaired. Lean 4.33.1 gives a `Nat` literal of 2^31 or more to several owners with no reference count, and on wasm32 that literal is a heap object. `tools/wasm32-nat-literals.py` makes each such literal one persistent object (254 sites), and `build-web-render.sh --wasm` fails when a compiled file keeps one. Record: `docs/designissues/2026-11-09-wasm32-nat-literals.md`.
- Wasm build: the fuel of the evaluator is 2^31 - 1, a scalar on wasm32. The first `fib(24)` turn went from about 580 ms to 265 ms (commit message of `c406d7dd7`).
- Names are resolved to slots, objects have small property tables, and writes are in place (`JS/Resolve.lean`, `PropMap`). `Array.prototype.push`, `pop` and `a[i] = v` do not copy the array. `indexOf`, `Map` and `Set` inserts and deletes, `Array.prototype.shift` and `s += x` on a local variable are linear. A loop of `indexOf` on 80,000 characters went from 196 s to 112 ms (commit message of `d8a8473e4`).
- A register machine runs hot functions (`JS/Compile.lean`, `vmLoop`): functions with plain parameters that no closure can hold, and top-level loops with no closures. A call between compiled functions uses no native stack frame (limit `vmMaxDepth` 20,000). About two thirds of the functions of `prelude.js` and `testharness.js` compile. The machine is not proved equal to the evaluator. It is tested: the Test262 subset gives the same result for each file with the machine on and off.
- Integer and float conversions do not go through the big number runtime. `natToFloat`, `intToFloat`, `ofScientificFast`, ToInt32 and ToUint32 are fast forms with theorems that they equal their specifications for every argument (`Prim/FloatOfNat.lean`, `JS/Number.lean`). On the register machine `i | 1` went from 394 to 92 ns and `a[i & 7]` from 433 to 121 ns (`docs/designissues/2026-11-09-foafnaut-perf-exploration.md`, section 2).
- Language repairs: the parser chooses between a division and a regular expression literal at the two places where the grammar decides; a function declaration has no private scope for its name; an assignment to the name of a function expression follows ECMA-262 9.1.1.1.5; `encodeURI` and `decodeURI` are there; `yield` and `await` work in loop tests, in a for-of iterable and in the branches of `?:`, `&&`, `||` and `??`. Tests: 91 scripts in `JS/RegressionTests.lean`.
- Test262, 6,301 files of `test/language`: 5,633 pass, 664 fail, 4 skip. Before the repairs of 2026-11-10: 5,629 pass, 668 fail. No verdict is worse (record section 6.6).
- A function with more than 24 names has an index for its scope lookup, and the parser keeps `var` names in a set. For the 1.18 MB `js_of_ocaml` bundle extracted from F\*, the load went from 2,195 to 1,058 CPU ms and the run from 8,031 to 3,401 CPU ms (record section 6.6).
- `s += v` on a local variable of a compiled function appends in place: 400,000 appends of one character went from 2.32 to 0.09 CPU s, and of the loop counter from 27.6 to 0.10 CPU s (record section 6.6).
- Real-world code (`labs/demos/foafnaut/bubblepop_perf/realworld.py`): BubblePopJS gives the reference answer on 6 of 6 workloads (5 of 6 before; `marked` did not load). Run time as a multiple of QuickJS-NG 0.18.0, one run on one Linux VM: lodash 5.1, acorn 7.1, pako 18.2, marked 5.3, immutable 9.1, the F\* bundle 11.0; geometric mean 8.4 over the six (record section 6.6).
- Page scripts: `console.warn`, `error`, `info` and `debug` (and `groupCollapsed`, `timeLog`, `count`, `dirxml`) carry their level to the console tab, on BubblePopJS and on QuickJS-NG.
- The plan for BubblePopJS and its proposed key results are in `docs/designissues/2026-11-09-bubblepopjs-plan.md` and https://github.com/danbri/factoidal-core/issues/378 (BubblePopJS plan). The key results are a proposal until the owner approves them.

## WasmVM (WebAssembly engine)

- Fixed-width SIMD: the `v128` type and the 236 instructions with binary prefix 0xFD, in the decoder, the validator, the interpreter, the AOT encoder and the API (`Value.v128`). Spec tests (`lake exe wasmvm-spectest`), pass, fail, not run: `simd` directory (59 files) 25479, 0, 511 (before 122, 0, 25868); all 259 files 60858, 0, 4495 (before 35501, 0, 29852). The 511 are text-format modules (`docs/designissues/2026-11-07-wasmvm-engine.md`, section "SIMD").
- Garbage collection proposal of WebAssembly 3.0, first stage: recursion groups, sub types, struct and array types, the instructions with binary prefix 0xFB, `ref.eq`, casts, and the heap types of the `any` hierarchy. Spec tests, pass, fail, not run: `gc` directory (17 files) 793, 0, 5 (before 14, 0, 784); all 259 files 61698, 0, 3655 (before 60858, 0, 4495). No directory has a lower pass count. The AOT encoder: 4730 files decode and round-trip, 0 failures (before 4519) (same record, section "GC").
- Cost for code with no SIMD and no GC (`lake exe wasmvm-bench engine 10000000`, six runs): the differences before and after are smaller than the range of one binary. Every new operation runs outside the hot loop `run`.
- `lake build wasmvm-bench` builds again (an import was missing in `WasmVM/Bench/Page.lean`).

## Rendering and fonts

- Colour glyphs: Lean reads COLR versions 0 and 1 and CPAL (`Rendering/SfntColr.lean`) and draws them with the Canvas 2D rasteriser (`Rendering/ColrRaster.lean`): solid fills, linear, radial and sweep gradients, every transform paint, and the 28 composite modes. A hostile font is refused by a depth limit (64) and a node budget (32,768). The standard font policy allows the colour capability.
- Emoji in HTML text: an emoji grapheme cluster (ZWJ sequence, skin tone, flag, tag sequence, keycap, presentation selector) goes whole to one font. Emoji presentation takes a colour font; text presentation (U+FE0E) takes a font with no colour (UTS #51 section 4). The emoji properties come from the Unicode data files (`Unicode/EmojiData.lean`). Tracking: https://github.com/danbri/factoidal/issues/1276 (emoji drew as .notdef).
- Fonts: Noto Color Emoji (COLRv1, OFL) is vendored in 17 slices, 5.6 MB in all. A page fetches only the slices of its emoji, and Noto Emoji for text presentation. A page with no emoji fetches no emoji font.
- Emoji in canvas `fillText` draw in colour. Emoji in SVG text draw again, as outlines from Noto Emoji in one colour.
- Colour emoji pixels are tested against an independent COLR renderer (blackrenderer and Skia) on 12 glyphs: mean difference 0.7 to 3.3 of 255, at most 1.4% of pixels over 32, against limits of 4 and 2.5% (commit message of `036aef425`).
- Web fonts: `font-family` lists, `@font-face` rules and font matching (CSS Fonts 4 sections 4 and 5.2) are in Lean. The host fetches only the faces that the rendered text uses, from the page's own origin, with limits of 8 MiB a face and 16 MiB a page. `document.fonts` answers from Lean. Fruktur (OFL) is vendored for the demonstration. Record: `docs/designissues/2026-11-09-web-fonts-and-paint-only.md`.
- Combining marks: a mark of one font is placed on a base of another font by HarfBuzz's fallback rule, and joins the cluster of its base for selection and copy. A mark that the font's GPOS leaves unattached is placed on the ink of its base. Thousands of marks on one base cost linear time. Tests compare with hb-shape 15. Tracking: https://github.com/danbri/factoidal-core/issues/368 (marks from a fallback font).
- SVG animation: SMIL timing and values are in Lean (`Rendering/Smil.lean`). An SVG transform or animation that changes paint only is drawn on the kept layout, with no new layout (theorems `paint_never_layouts`, `run_paints_never_layout`).
- SVG text: glyph outlines reach the scene reader as numbers, with no path data text. The dataviz page, median of layouts 2 to 14: 132 to 134 ms before, 96 ms after (commit message of `e80946ba7`).
- Paint: a long curve that crosses the canvas is cut, so a glyph at scale 200 and more stays in the backend's point limit. `WebPaint.cullCurve` no longer converts the literal `1e300` at run time for every curve (85% of a frame).
- `overflow: hidden` and `overflow: clip` clip the content to the padding box, not the box's own background (`Rendering/ClipTheorems.lean`). Ink is kept within 31 em of its cluster (`Rendering/InkBound.lean`).
- Device pixels: a page is laid out in CSS px and drawn at the device pixel ratio (`zoomUnit`). Before, on a 2x screen the Hub laid out in device pixels, so a 16px margin drew as 8 CSS px. Page scripts see CSS px and `devicePixelRatio`. Theorem `layoutInputs_ratio`: the layout inputs are the same at every ratio. On a Retina window with no saved zoom, the native app now starts at zoom 400.
- Layout speed on real sites. Native, 1600 by 1000 at 200%, liberal mode, scripts off, milliseconds, before and after: Wikipedia FOAF first compile 2,958 and 336, relayout 2,450 and 97; gov.uk 4,427 and 250, 4,326 and 122; BBC News 57,603 and 951, 58,648 and 537 (`docs/designissues/2026-11-09-real-site-layout-speed.md`, section "Numbers", on a loaded machine). The cascade reads element keys once and tries only the rules of an element's buckets (theorem `computeAll_eq_linear`); sheets, the page tree, images and shaped words are kept across layouts.
- Frames: origins and the iframe sandbox are decisions in Lean (`HTML/Frames.lean`; theorems `scripts_need_allow`, `sandboxed_no_access`, `flags_inherit`, `postMessage_star`, `postMessage_mismatch`). In the native script session each connected iframe has a document (`about:blank`, `srcdoc`, or a `src` URL that the host answers). `contentDocument` is given only for the page's origin. Record: `docs/designissues/2026-11-09-iframe-documents.md`.
- Forms: form submission is in Lean (`HTML/FormSubmission.lean`, HTML 4.10.21.3 to 4.10.21.6 and URL 5.2): the entry list, the form's encoding, `application/x-www-form-urlencoded` in that encoding, and the GET URL. `form.submit()` and a submit event that is not cancelled navigate the target frame. A same-origin frame answers `characterSet` and `inputEncoding`.
- WPT `encoding/`, BubblePopJS, native engine, subtests passed against Chrome's count on wpt.fyi: encode-form 550,053 of 550,054 (before 0); encode-href 216,479 of 216,479; decode 360,788 of 361,145 (before 0); 1,139,189 of the directory's 1,152,398 subtests. These figures are from an earlier build than `main`; no subtest was measured on the final tree (`docs/designissues/2026-11-09-encoding-wpt.md`, sections "Results" and "Which tree each number is from").

## Browser host and Hub

- Liberal mode is the default in the macOS app and on the Hub. Strict mode is a Settings choice, `--strict` and `?strict=1`.
- An HTML document or a stylesheet can be 16 MiB (was 1 MiB). The stylesheets of a page can total 32 MiB.
- A start page with a wordmark carousel opens when no page is given.
- `about:foafnaut` and `--version` give the commit, uncommitted changes and build time. The build writes this record from git and fails unless the compiled program reports the commit that is built.
- The browser bar shows which engine runs the page's scripts.
- Settings: a ticked box is filled.
- Address bar: Left, Right and Delete step by extended grapheme cluster (UAX #29).
- Hub: the GPU layer surface keeps its first error and reports it, with the device lost reason.
- Hub: SVG animations start from the idle state and continue. A new Hub page measures how deep a Web Worker's Wasm stack goes in the reader's browser (`/web/hub/wasm-stack/`).
- Native window: the worker has one list of engine calls. `encodingChoices`, `encodingSetting` and `decodeDocument` were missing from the client's copy.
- Demo pages: an emoji page with text and emoji presentation side by side; the Open Index Search page; a link to a JavaScript games collection (it needs module scripts). Page titles say "the built-in engine" or "the browser".
- Textnaut: a prototype of a text terminal front end on the same engine (https://github.com/danbri/factoidal-core/issues/371, terminal browser investigation), with a launcher in the repository, heading panels, rules and bullets, a contrasting colour for text on a page background, and `textnaut --screensaver`.

## Tools

- Developer proxy (`tools/devproxy/`, https://github.com/danbri/factoidal-core/issues/375, record and replay): it records a real page and its resources to WARC 1.1 and replays them with no outbound connection. Response services remove scripts or keep only text, CSS and links. It binds to 127.0.0.1 only. It is a test aid, not a user feature and not a sanitiser.
- Daily WPT job in https://github.com/danbri/factoidal-builds (`.github/workflows/wpt-score.yml`): each day at 02:47 UTC it runs `tests/browser-wpt/wpt-score.py` of factoidal-core with a released engine, for BubblePopJS and for QuickJS-NG, at a pinned and at the latest WPT commit, and appends one line for each score to `history.jsonl` on the branch `wpt-scores`. It runs on macOS, because a release holds a native engine library for macOS arm64 only.
- Measurement tools for BubblePopJS (`labs/demos/foafnaut/bubblepop_perf/`): `opcost.py` (61 single operations by engine), `scaling.py` (each operation at N and 4N), `realworld.py` (six workloads against a reference engine). `bubblepop_cost_test.ts` is a linear-cost check in `test.sh`.
- `tools/lean-literal-parse-audit.py` lists literals and conversions that the generated C evaluates at each call.
- `run_html.ts --watch-sweep SECONDS` gives the frame times of a page that moves with no input.
- Builds: `build-engines.sh` compiles and links `Prim/FloatOfNat` (the Foafnaut engines job of factoidal-builds failed without it; the repair was not run on the machine that made it). `build-web-render.sh` finds Emscripten's cache in a Homebrew install.

## Known limits

- Page scripts have no network: no `fetch`, no `XMLHttpRequest`, and a `<script src>` that a script adds is not fetched (https://github.com/danbri/factoidal-core/issues/374, page scripts have no network). The Open Index Search page is the acceptance page; `network_gaps_test.ts` is the expected failure.
- BubblePopJS is 5.1 to 18.2 times slower than QuickJS-NG on the six workloads of record section 6.6. The pako figure of that run is an outlier: two other runs put pako at about 31 times.
- BubblePopJS: `s += 'x'` at the top level of a script, where the variable is a global, is not repaired (2.50 CPU s before, 2.57 after, for 400,000 appends).
- BubblePopJS: the register machine has no proof. In the Foafnaut Wasm build the call depth is 100. Test262 has 664 failures of 6,301 files of `test/language`.
- BubblePopJS: on the tree with the repairs of 2026-11-10, a native build of the engine and `test.sh` were not run (record section 6.6).
- WasmVM SIMD refuses relaxed SIMD (79 spec commands not run), a tag type with a `v128` parameter, and a host function type with a `v128`. Each refusal has a check that names https://github.com/danbri/factoidal-core/issues/385 (SIMD parts refused). SIMD speed is not measured.
- WasmVM GC has no collector: an object stays until the store is dropped. Every object slot is 8 bytes. A `v128` field or element is refused (4 spec commands not run), and an array has at most 2^26 elements. The `wasm_of_ocaml` modules of this project are not checked (https://github.com/danbri/factoidal-core/issues/386, GC limits of the first stage).
- Emoji in SVG text draw in one colour.
- Web fonts: WOFF, WOFF 2, SVG and EOT sources are passed over (no decoder); `local()` never matches; there is no `FontFace` constructor.
- Forms: a sandboxed form does not submit. The targets `_blank`, `_parent`, `_top` and the page itself do not navigate. The frame `characterSet` change was type-checked only when its record was written.
- Layout: an empty block with a size and a background inside an inline-block is not painted (https://github.com/danbri/factoidal-core/issues/369, expected failure in `showcase_gaps_test.ts`).
- `unsafe` and `@[implemented_by]` in `labs/demos/foafnaut` are not read by the hygiene audit (https://github.com/danbri/factoidal-core/issues/390, scope rule above). A theorem about a function that reaches one of those cells is about the `opaque` declaration, not about the compiled code.
- There is no Linux desktop app and no Windows build (`docs/20261110-foafnaut-binaries-and-wasm-status.md`).
