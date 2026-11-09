# Lean HTML/CSS renderer

> Note, 2026-11-09: this file describes the local lab server (`server.mjs`) and its own
> QuickJS worker path, as of 2026-11-02. The browser window (`run_html.ts`) and the Hub
> have more: page scripts in the engine (BubblePopJS and QuickJS-NG in WasmVM) and font
> fallback. Do not read the script and font limits below as limits of the
> engine. See [skills/foafnaut/SKILL.md](../../../../skills/foafnaut/SKILL.md).

This local renderer accepts original HTML/CSS source. The existing Lean HTML
parser and DOM arena feed Lean computed styles, block/inline text flow and a
common retained Float vector scene. An explicit adapter feeds the existing
Lean SVG CPU/WGSL renderer. The browser host transports bytes and WebGPU
commands; it does not use browser DOM layout for candidate output.

Build from the repository root:

```sh
labs/demos/foafnaut/build-web-render.sh --native
FACTOIDAL_WASM_RUNTIME_CACHE=/absolute/verified/lean-4.33.1-runtime \
  labs/demos/foafnaut/build-web-render.sh --wasm
node labs/demos/foafnaut/web-render/server.mjs 8099
```

The runtime path must contain the pinned Lean 4.33.1 wasm object closure and
validated string-list patch witness. It is read only. All generated outputs
stay under the ignored `.build/web-render` directory. The script compiles the
specific HTML/DOM/rendering import closure, not the full Factoidal library,
and requires at least 3 GiB free before a heavy build.

Open the server URL. The browser shell has URL entry, Go, Back, Forward,
Reload and Stop. Rendered link clicks use the Lean picker and load the target
through the same native HTTP byte broker. The address bar commits the final
redirect URL after rendering. `?url=https%3A%2F%2Fexample.org%2F` loads an
initial URL. The original decoded UTF-8 page source remains in the editor.
Edits to source, CSS or viewport dimensions change GPU output. The inspector
shows source DOM indexes, layout boxes and consumed glyph runs. Link events
remain in the console and bounded same-origin `/events` server log. Disable
Follow rendered links for picker diagnostics without navigation.

Lean identifies and resolves external stylesheets, classic scripts and the
HTML base. The host fetches those bytes without rewriting markup. The
document API applies CSS and bounded script DOM commands in Lean. The
separate QuickJS worker supports synchronous classic scripts, simple ID
lookup, textContent, setAttribute and click listeners. Module scripts produce
an unsupported error; data script blocks remain inert. Each navigation/source
edit creates a new VM; a viewport change preserves its state. Scripts have
no host DOM, fetch, storage, timers, or Promise job loop.

Font requests come from the same prepared DOM/CSS/commands as the final
render. An explicit `font-family:Arial` uses the exact local Arial binding
through HarfBuzz/FreeType. `FACTOIDAL_FONT_FILE` can select another exact
Arial file. This is one font family per document; font matching/fallback and
downloaded web fonts are not implemented. The default bitmap profile remains
available for its existing subset.

The broker is a native network capability of this loopback server. A static
web deployment needs a broker or suitable resource CORS headers. It supplies
no cookies or authentication. UTF-8 is required. Fragments retain their URL
but do not scroll. Unsupported markup/style is an explicit rendering error.

Native CLI:

```sh
labs/demos/foafnaut/.build/web-render/web-render-native INPUT.html WIDTH HEIGHT
labs/demos/foafnaut/.build/web-render/web-render-native INPUT.html WIDTH HEIGHT --pixels
```

The default output is the existing `lean-svg-v1` data/WGSL artifact plus
`webRender` layout metadata. `--pixels` returns a full CPU RGB image, capped
at 1,048,576 pixels. An evaluated unsupported profile returns error JSON;
invalid command arguments or file IO fail the process.

The bitmap font profile is original ASCII bitmap outlines, with actual
word wrapping, baselines and source clusters. The supplied-font path uses
real font shaping; CSS/layout refusals remain explicit. Embedded SVG initially admits
only untransformed fill rectangles wholly inside their viewport until the
shared clip extension lands. This browser MVP is a working subset, not a
general HTML/CSS or JavaScript conformance claim.

The independent check uses installed Playwright Core and Chrome:

```sh
node labs/demos/foafnaut/web-render/check-browser.mjs \
  http://127.0.0.1:8099/ /absolute/playwright-core/index.mjs \
  /absolute/chrome /absolute/web-render-native /absolute/output-directory
```

It compares a whole GPU image against the whole CPU image and the original
HTML rendered independently by Chrome. It also changes CSS color/width and
text, verifies changed pixels/reflow, and checks unsupported font refusal.
It is a local profile check; upstream WPT results have their own corpus and
unchanged denominator. The browser reference receives the original HTML,
not an extracted SVG or candidate-generated markup.

Tracking: https://github.com/danbri/factoidal/issues/1230 (shared Lean web
renderer). Architecture and exact scope:
[design record](../../../../docs/designissues/2026-11-02-lean-web-rendering.md).

Navigation and the combined external CSS/script/font browser path have
separate executable checks:

```sh
node labs/demos/foafnaut/web-render/check-navigation.mjs
node labs/demos/foafnaut/web-render/check-navigation-browser.mjs \
  http://127.0.0.1:8100/ /absolute/playwright-core/index.mjs \
  /absolute/chrome /absolute/output-directory
node labs/demos/foafnaut/web-render/check-document-browser.mjs \
  http://127.0.0.1:8100/ /absolute/playwright-core/index.mjs \
  /absolute/chrome /absolute/output-directory
```

These checks create real local HTTP fixture servers. The browser checks use
actual Lean WASM, WebGPU and the Lean link picker. Their reports are local
profile evidence. The [navigation worknote](../../../../docs/20261103-lean-browser-navigation.md)
records execution status and remaining limits.

## Terminable renderer worker

`engine.mjs` is the foreground transport. `engine-worker.mjs` executes the Lean
ABI in `engine-core.mjs`. Stop and input cancellation terminate active renderer
work; the next call starts a fresh worker. Requests have bounded queue bytes,
count and deadlines. Link/node picks retain only scene metadata, with recovery
when a worker or cache entry is replaced. Details and evidence:
[worker design](../../../../docs/designissues/2026-11-04-renderer-worker.md) and
[worknote](../../../../docs/20261104-renderer-worker.md).

The async API is unchanged. Optional transport controls are a final argument,
separate from Lean document options:

```js
await engine.compileDocument(html, width, height, options, {signal});
engine.abortPending('Stop');
```

Run the actual-WASM tests with Node22 and actual font records:

```sh
FACTOIDAL_RENDER_MODULE=/absolute/path/to/web-render.mjs \
FACTOIDAL_FONT_DATA=/absolute/path/to/font-data.json \
node --test labs/demos/foafnaut/web-render/tests/engine-worker.test.mjs
```

The font records must contain space, `November2026`, `café` and `edited` at20px,
and `office` at28px, from one actual family. These are test inputs only. No
font bytes are committed. The tests fail if their required inputs are absent.

`tests/browser-server.mjs` starts a small harness on an ephemeral loopback port
when `FACTOIDAL_RENDER_MODULE` names the built renderer. Run its actual Chrome
check with:

```sh
node labs/demos/foafnaut/web-render/tests/check-browser-worker.mjs \
  HARNESS_URL PLAYWRIGHT_CORE_MJS CHROME OUTPUT_DIRECTORY
```

This harness checks the real worker and foreground heartbeat. The application
browser checks separately cover WebGPU and document/navigation integration.
