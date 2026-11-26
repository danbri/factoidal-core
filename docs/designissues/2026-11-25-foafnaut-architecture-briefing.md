# Foafnaut: architecture, state and where help pays off (2026-11-25)

A briefing for a senior engineer who knows browser engines and Lean 4. Numbers are from main and from the
`danbri/factoidal-builds` records of 2026-11-25 (core commits 3f499a901 and 41789954b). The author has not read every
file. Code-quality statements below name their evidence.

## 1. What it is

Foafnaut is a web browser whose engine (BubblePopKit) is written in Lean 4 and compiled through Lean's C back end.
It has two forms: a native library (`libweb-render.dylib` / `.so`) and one Wasm module. The engine does all of these:

- HTML parsing (WHATWG tokenizer and tree builder);
- DOM, CSS cascade and computed values, block/inline/table layout;
- font loading and shaping (`Sfnt*`, its own shaper; HarfBuzz is only a differential oracle);
- image decoding, SVG;
- the scene (display list) and the WGSL that draws it.

Page JavaScript runs in BubblePopJS, a JS engine written in Lean (`L4Factoidal/JS`). Wasm runs in BubblePopWASM
(`L4Factoidal/WasmVM`). QuickJS-NG can run as a Wasm guest inside WasmVM, behind a setting.

The host is TypeScript on Deno:

- macOS: Cocoa window through FFI;
- Linux: SDL2;
- GPU: Deno's WebGPU (wgpu to Metal or Vulkan);
- network: Deno's `fetch` and TLS.

The Hub build runs the same Wasm engine in a browser Web Worker with WebGPU.

Sizes (lines of Lean):

| Part | Lines |
|---|---|
| `Rendering/` | 55k |
| `WasmVM/` | 42k |
| Lab engine modules (`labs/demos/foafnaut/*.lean`; `WebDocument.lean` alone is 4.3k) | 36k |
| `JS/` | 32k |
| `DOM/` | 15k |
| `HTML/` | 10k |
| `WHATWG/` | 7k |
| `PageGpu/` + `PageCanvas/` | 8k |

Host: about 160 TypeScript files; `run_html.ts`, the browser loop, is 2.5k lines.

The browser shares one Lake project with Factoidal's W3C data stack (RDF, SPARQL, XSLT, XML, URL, encodings). That is
why it has SPARQL and XSLT pages.

## 2. The design that shapes and constrains the code

These rules are set by the project owner (`CLAUDE.md`, `skills/foafnaut/SKILL.md`). They decide most of what follows.

1. **Every decision is in Lean.** The host only moves bytes: window events, GPU buffers, sockets. Layout, routing,
   gestures, console content, form submission and font policy are Lean functions. Host-side "cheats", such as overlays
   from a host browser or a host JS engine for page scripts, are refused. Hand-written TS or JS that decides RDF, HTML
   or CSS semantics is a rule violation.
2. **Spec and implementation are separate artefacts, both in Lean.** The aim is fast implementations proved (or
   differentially tested) equal to spec-shaped ones, so that optimisation cannot silently break conformance. In
   practice:
   - `@[csimp]` twins replace slow reference definitions at compile time;
   - "incremental equals full" lemmas exist per cache (`docs/designissues/2026-11-16-incremental-equals-full.md`), but
     most lack the preservation half;
   - the JIT tiers carry a `tier_refines` theorem.
3. **Totality and bounded resources.**
   - No new `partial def`, `sorry`, `native_decide` or `axiom`.
   - Loops over input-sized data are tail calls or `do`-loops with fixed memory.
   - Interpreters run on fuel.
   - Crashes and resource exhaustion count as safety defects.
4. **The engine is a request/answer function.** The ABI (`web_render_shim.c`, `native_html_engine.ts`) is:
   (HTML text, JSON request, viewport) → JSON head plus byte sections. A kept `Engine` value inside the worker holds
   the parse, the sheets, the layout memo and the scene between calls. There is no long-lived mutable DOM shared with
   the host.
5. **Threads.**
   - Main thread: window, input queue, GPU presentation, two-layer scroll composite.
   - One Deno Worker per tab (at most 8), each with its own engine copy and one ordered queue of engine calls.
   - Inside a call, `Task.spawn` parallelism since 2026-11-25: image decode, word shaping, and JIT compilation where
     enabled.
   - Gestures (click, Command-click, selection, copy) are answered from the frame already on screen, never after page
     scripts.
6. **Measure, then ratchet.** The measure of the product is the Web Platform Tests. Other suites: test262, the W3C SVG
   pixel suite, WPT reftests, html5lib, the HarfBuzz differential. The real-pages survey is the usability measure.
   Every performance change reports a before/after number, and many have a cost ratchet test (`*_cost_test.ts`,
   `frame_cost_test.ts`).
7. **Security posture.** Fonts are interpreted with fuel; hinting is not run; Wasm-in-font and AAT are refused.
   Risky code paths need a `--dangerously-…` flag. No third-party C in the engine, except the HACL\* crypto
   primitives.

## 3. Where it stands, in numbers

| Measure | Result |
|---|---|
| WPT, full run, native engine, BubblePopJS, 3f499a901 | 92.6% of subtests (2,107,480 of 2,275,009, 95,131 test files); 85.1% without `encoding/` |
| test262, BubblePopJS | 88.2% (47,461 of 53,795) |
| WPT reftests, SVG | 49.4% (343 of 695) |
| WPT reftests, CSS | 47.0% (12,157 of 25,868) |

Real pages (`realpages-survey`, macOS, live, 24 pages, engine 3f499a901):

- Verdicts: 6 usable, 17 slow, 1 unusable, 0 crashed.
- First frame: 1.7 s (a small W3C page) to 37.6 s (jvns.ca). Typical news and reference pages take 8 to 19 s.
- First layout: 0.2 to 12 s (MDN `display` 12.1 s; Wikipedia "United States" 10.6 s).
- Scroll input to present, p50: 4 ms on small pages; 500 ms to 3.5 s on large pages; 9.6 s on MDN. When no Lean frame
  is needed, the composite takes 1 ms.
- Peak RSS: 0.8 to 3.3 GB per page.
- Layout similarity against Chrome (1.0 means the same): median about 0.53. gov.uk, w3.org, infobomb and
  naturetelemetry are at 0.84 to 0.96. bbc.co.uk, mobile Wikipedia and the CSS Flexbox spec are at 0.05 or below
  to 0.2.

## 4. Why WPT is high but real pages are slow and wrong

**The WPT number measures something different from page use.**

- The share is weighted by subtests. It is dominated by testharness.js files with many subtests: encoding tables,
  URL parsing, IDL and DOM API behaviour, HTML parsing, `Intl`/JS built-ins.
- These are algorithmic, spec-literal checks, which is where a spec-transcribed Lean engine is strongest.
- WPT has no time limit that matters for these tests, and it does not test speed.
- The layout and painting suites are reftests. Those run apart and are near 47 to 49%.
- So the 92.6% says "the algorithms in the spec prose are mostly there". It does not say "pages lay out like Chrome,
  fast". Comparisons with Safari use other methods (wpt.fyi counts by test file and runs other directories), so treat
  them only as a rough guide.

**Measured causes of slowness, in order of size:**

1. **No real incrementality in the frame path.** A frame on a kept layout (status page, 2,940 primitives) cost
   249 M instructions. Correction, 2026-11-26: that figure is the path without layers, which no host uses. The same
   frame on the layers path, which every host uses, cost 12.3 M instructions, and 3.0 M after display list stage A
   (74d4c4f54, https://github.com/danbri/factoidal-core/issues/1124 (retained display list)). The breakdown below is
   for the path without layers. In that frame:
   - 39% turns the scene into float32 bytes;
   - 32% rebuilds the scene from the layout;
   - 19% writes boxes and glyph runs as JSON text (13% is `printf` float-to-text);
   - 781k allocations, with alloc/free 27% of samples.

   Scroll beyond the kept band, hover, and any DOM change come back through this path. On large pages, style and
   layout run again too. Memoisation exists (layout memo, retained compile, paint-only patch), but restyle and
   relayout after mutation are mostly whole-document.
2. **Style is not indexed enough.** On CSS-heavy pages, style is 34 to 52% of the first compile (MDN, Wikipedia).
   There are rule buckets (`RuleIndex`), but no Bloom-filter ancestor checks, no style sharing and no invalidation sets.
3. **Images and text in pure Lean.** On image-heavy pages, image decode is 45 to 68% of the first compile. Shaping is
   23 to 44% on text-heavy pages. Both now run in parallel tasks (merged 2026-11-25; time after the change not yet
   surveyed), but per-pixel and per-glyph code pays for boxed `Float`, reference counting and `Array` copies.
4. **Lean C back-end traps.** Several 10 to 85% wins this month came from code that was not algorithmic:
   - a float literal compiled to `Float.ofScientific`, which parses the decimal through GMP at each call (`1e300` was
     85% of a frame; `0.5` in canvas pixel loops was 17%);
   - `2^53` recomputed per typed-array access;
   - `Nat` arithmetic on hot paths;
   - lost destructive updates (RC > 1 forces a copy);
   - `List` where `Array` was meant.

   Audit tool: `tools/lean-literal-parse-audit`. There are surely more of these.
5. **JavaScript.** BubblePopJS was 6 to 25× slower than QuickJS-NG per operation (`fib(30)`: 145 ns against 23 ns,
   2026-11-09). Since then there is a register VM, a proved tier-1 compiler and inline-cache work. Big sites run many
   script turns, and each DOM-changing turn costs a restyle and relayout.

   Example: on Particle Rex, a canvas game, the game logic alone is 3 to 6 ms per frame, but a Foafnaut frame is 84 ms
   against 0.5 ms in Chromium. The cost is the canvas path (host round trip, raster into new bitmaps, a full-canvas
   GPU upload).
6. **Memory.** The engine holds immutable copies (parse, styled tree, layout, scene, byte buffers), per tab. With no
   arena or interning discipline, RSS reaches 1 to 3 GB.

**Measured causes of wrong layout.** CSS reftests are at 47%. The pages with the lowest similarity use, among other
things:

- flex and grid in depth;
- positioned and sticky elements;
- web fonts with fallback chains;
- `@media` and `@supports` combinations;
- responsive images;
- and, on BBC, layout built by scripts.

We have no per-feature attribution of the similarity gap yet. That is a cheap first project (section 6).

## 5. How good is the code

Evidence-based, from reading parts of it this month.

**Strong:**

- Spec traceability: section numbers in doc comments.
- Real test suites, run by CI on every release, with stored records (`runs.csv`, realpages trend).
- Ratchet tests on costs.
- Theorems where they are cheap. Total functions throughout.
- A reproducible measurement culture: every perf claim has a command.

**Weak:**

- Most of the code was written by many AI agent sessions over about four weeks, steered from a phone. It is broad
  before it is deep. Hot loops were often written spec-shaped first, and optimised only after a profile found them.
- Data representation is the main cost and is not designed for speed:
  - boxed floats;
  - JSON and decimal text across the ABI and inside the scene path;
  - persistent structures rebuilt per frame.
- The host TS is dense: long one-line functions and option parsing in one loop. `run_html.ts` (2.5k lines) and
  `WebDocument.lean` (4.3k lines) are central and hard to change safely.
- The engine core is under `labs/demos/foafnaut/` instead of the library tree.
- Proofs cover per-cache step lemmas but rarely the invariant preservation that would make the caches safe to extend.

It is not throwaway code. It is a large, tested, spec-faithful reference engine, with a performance architecture that
was never designed as a whole.

## 6. Where a senior engineer would change the outcome most

1. **Frame and scene architecture (largest, and needs judgement).** Design a retained display list in mutable
   `ByteArray`/`FloatArray` storage, with damage tracking. Patch it in place from a dirty set. Use a binary ABI with no
   JSON or decimal text on the frame path, and one upload of changed ranges. State the refinement against the current
   `Scene.make` / `jsonWith` as the spec. Target: a kept-layout frame at a small fraction of the cost on the
   layers path (12.3 M instructions before stage A, 3.0 M after; the 249 M figure above is the path without layers).
   The canvas-game frame (Rex) has other costs: https://github.com/danbri/factoidal-core/issues/1098 (canvas game at
   10 fps).
2. **Style invalidation and incremental layout.** Add selector invalidation sets, ancestor Bloom filters and style
   sharing. Add dirty bits through layout, so that a DOM change or a script turn costs a subtree, not the document.
   The "incremental equals full" statement already exists as the correctness target; what it lacks is preservation
   lemmas.
3. **Lean performance review of hot loops** (image decode, shaping, raster, the JS VM):
   - unboxed representations and `@[specialize]`/`@[inline]` choices;
   - keeping RC=1 for in-place updates;
   - removing `Nat` and `Float.ofScientific` from hot paths;
   - an audit rule set that CI can enforce.

   Lean-literate C-level eyes are rare here.
4. **Layout breadth with attribution.** Take the 24 survey pages. Find the first CSS feature where each one diverges
   from Chrome, and fix the top ten features by page count. The reftest suites give the regression net.
5. **JS engine direction.** Review `docs/designissues/2026-11-09-bubblepopjs-plan.md`: register VM, proved tiers,
   inline caches, the GC question. Tell us early if a design choice blocks the speed target.

## 7. How to start

- Read:
  - `skills/foafnaut/SKILL.md` (code map, build, measure, traps) and its `AGENT-BRIEF.md`;
  - `docs/designissues/2026-11-07-foafnaut-frame-pipeline.md`;
  - `docs/designissues/2026-11-09-foafnaut-perf-exploration.md` (sections 8 to 10: the instruction-level profiles);
  - `docs/designissues/2026-11-24-foafnaut-concurrency-and-network.md`;
  - `docs/designissues/2026-11-16-incremental-equals-full.md`.
- Builds: Linux x86_64 and macOS arm64 releases at https://github.com/danbri/factoidal-builds/releases. The Hub build
  is at https://danbri.github.io/factoidal/web/hub/foafnaut/.
- Profile one page with no GUI: `skills/foafnaut/SKILL.md` "Measure" (one page timed, then callgrind at COUNT 1 and
  COUNT 4).
- Tracking: https://github.com/danbri/factoidal-core/issues/1031 (concurrency, input, network, threads),
  https://github.com/danbri/factoidal-core/issues/471 (JIT), https://github.com/danbri/factoidal-core/issues/1098
  (canvas frame cost).
- Working rules: work lands on `main`; Lean builds run one at a time on a shared machine; no AI attribution in
  commits.

What we can do for you: run any measurement you name on the Linux rig the same day; turn a design note into
issues and agent tasks; give you a branch with a profile of any page you choose.
