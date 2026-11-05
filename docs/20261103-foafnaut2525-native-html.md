# foafnaut2525 native HTML development app

The app is `foafnaut.app`, and its window title is `foafnaut - PAGE TITLE`.

2026-11-05: the HTML native window presents. Started by macOS (a small `.app`
wrapper around `run_html.ts`), the default page logged
`native-html-presented` (1600 x 1000, 1,405 primitives, 11 links, 1 frame) on
the Apple M1 adapter, and the Lean pixel checks on the GPU readback passed.
The cause of the earlier blank window was the surface format: the Lean
`svg-offscreen` plan answers `rgba8unorm`, which a macOS window surface does
not support. `native_html_session.ts` now uses the preferred surface format
and swaps blue and red in the readback before the Lean pixel checks. The final
fix belongs in `RenderPlan.lean`. An agent shell has no desktop session, so
test windows through `open`. A window fully behind another window waits with
no output. This log is not a human view of the screen.

The first host accepts an HTML file or an HTTP(S) URL, sends its original UTF-8
source to the published Lean WebDocument engine, and implements a Cocoa-window
presentation path through Deno WebGPU. Resize calls Lean again
with the current backing-pixel dimensions. Clicks use the published Lean link
picker. The host logs its returned href and node ID; `--follow-links` enables
navigation using the document base URL reported by Lean.

This work is isolated on `codex/foafnaut2525-native-app`, based on
`ed575e211b64fd166badc53c1de672cb3b0833d7`. There are no Lean, shader, Objective-C,
or shared browser-source changes. HTML parsing, CSS, layout, vector lowering,
WGSL generation, and link containment remain in Lean. The new TypeScript
handles bytes, resources, native events, GPU resource lifetime, and presentation.

## Existing native maturity evidence

On 2026-11-03 at 16:27–16:29, root launched the original published 988 FOAF
executable through a temporary `.app` wrapper in the native desktop context.
Root visually confirmed the eight-node graph, Bob selection and drag/pin,
Carol selection through the Cmd-L IRI field, and redraw after window resize.
The wrapper retained all 47 published package files, including their hashes
and file modes. The verification record is
`/private/tmp/factoidal-foafnaut2525-wrapper-988/verification.json`.

Earlier exec-context adapter requests returned null. That is a dated result
for those launches; it is not evidence that this machine lacks the native
route. The HTML host requires its own desktop qualification. FOAF desktop
evidence does not establish HTML desktop rendering.

## Published inputs and native route

Both original release metadata files identify source commit
`98896de16950c39d19f7791d49e31b3c9d5e607c`:

- [Native package release](https://github.com/danbri/factoidal-builds/releases/tag/build-98896de16950-foafnaut-darwin-arm64)
  supplies the original FOAF executable and adjacent `libnative-window.dylib`.
- [Browser runtime release](https://github.com/danbri/factoidal-builds/releases/tag/build-98896de16950-foafnaut-web)
  supplies the Lean HTML and render-plan modules. Its archive SHA-256 is
  `94841a65cea27cfe3bcf68e63f9e606297c6bcde3e26ca77a05a6b0aefbaa8eb`.

`tools/package-foafnaut2525.py` checks each archive when supplied, checks the
complete native package against the published 47-file inventory, and checks
all 16 browser-runtime files and modes before installing any runtime import.
It retains the original build-info files. It does not generate or replace an
engine source witness. Host source hashes and the host base commit are
recorded separately from the published engine commit.
The builder checks host hashes before and after compilation, rechecks installed
release bytes, and verifies the native package again before copying it.

Deno 2.9.4 supplies WebGPU through Rust wgpu. `native_window.ts` loads the
published Cocoa/CAMetalLayer bridge. `native_html_session.ts` reuses
`SurfaceLifecycle`, `requestRenderPlan`, `createPlanResources`, and
`commandInterpreter`. HTML uses a storage-buffer shader; the existing native
UI window plan uses a uniform buffer. This milestone therefore executes the
released `svg-offscreen` plan on the native `rgba8unorm` surface texture,
including its copy/readback commands and Lean pixel checks, then presents the
drawable. Each changed frame includes a readback. CPU/module checks have been
measured; this native presentation path still needs desktop qualification.

The HTML host compile uses the official Deno 2.9.4 ARM64 `denort` archive,
with SHA-256
`81bced8c72f5a1a64d6b1d85ac96aabef5fa559712ac54d2cdfbaa80002246ec`.
The compiler is checked for version 2.9.4. No Lean or Cocoa rebuild is needed.
The packager refuses to compile with less than 3 GiB free.

## Build and launch

The local inputs used for this check are named explicitly below. They are
downloaded release artifacts and metadata, not files inferred from another
worktree's build cache.

```sh
python3 tools/package-foafnaut2525.py \
  --native-package /private/tmp/factoidal-native-988-verified/foafnaut \
  --native-build-info /private/tmp/factoidal-native-988-build-info.json \
  --native-archive /private/tmp/factoidal-native-988-foafnaut-darwin-arm64.tar.gz \
  --web-build-info /private/tmp/factoidal-native-app-988-web-build-info.json \
  --web-archive /private/tmp/factoidal-native-app-988-foafnaut-web.tar.gz \
  --denort-archive /private/tmp/factoidal-svg-20261102-denort-aarch64-apple-darwin.zip \
  --deno /opt/homebrew/bin/deno \
  --html-shortcut \
  --output /private/tmp/factoidal-native-html-app-988
```

`--prepare-only` verifies and installs the runtime inputs without compiling or
creating an app. Output directories must be new. The complete build must run
from the isolated repository root. The temporary runtime paths are ignored.

The default `foafnaut2525.app` launcher changes directory to its own bundled
`Contents/Resources/foafnaut` and executes the unchanged FOAF UI with
`--demo foafnaut`. Its launcher also accepts:

```sh
foafnaut2525.app/Contents/MacOS/foafnaut2525 --html /absolute/path/page.html --follow-links
foafnaut2525.app/Contents/MacOS/foafnaut2525 --url https://example.test/page.html --follow-links
foafnaut2525.app/Contents/MacOS/foafnaut2525 --html-default
```

The optional `foafnaut2525-html.app` shortcut opens the bundled HTML example
and enables links. The original package remains present and unchanged. Its
original `SHA256SUMS` is retained; the new HTML executable and wrapper have a
separate inventory in `verification.json`. The wrappers are development
artifacts, with no new signing or notarization claim.

The HTML executable grants the trusted host read, network and FFI access.
This is not a process sandbox. Remote HTML cannot request a local file
stylesheet or navigate to a file URL, including through a file base URL.
Nonlocal file URL hosts and embedded credentials are refused. A user-supplied
local HTML input can use local stylesheets and links.

## Current limits and failure behavior

- The default font is the explicit Lean ASCII bitmap profile. Supplied font
  requests are refused. No font file, alias, HarfBuzz, or FreeType dependency
  is added to this milestone.
- Classic/module scripts are refused. Data scripts stay inert. There is no
  JavaScript execution, address bar, history UI, scrolling, fragment scrolling,
  or browser WebView in this host.
- Lean's existing HTML/CSS/SVG refusals remain in force. The example uses
  padding rather than unsupported collapsing vertical margins.
- Each input is at most 1 MiB, with fatal UTF-8 decoding and NUL rejection.
  External stylesheets are selected and URL-resolved by Lean, with at most
  16 resources and a 4 MiB host aggregate limit. Lean's existing 2 MiB
  stylesheet rule limit can refuse earlier. Network fetches time out after
  10 seconds. Navigation aborts and supersedes the prior pending request.
- Viewports are 1..4096 backing pixels per dimension. These are physical
  surface coordinates, with no CSS device-pixel-ratio scale. Retina screens
  can reach the limit before 4096 logical window points.
- Initial input failure exits before creating a window. Navigation or layout
  refusal is logged and does not commit the candidate document. GPU errors
  terminate after explicit resource cleanup. `R` reloads; Esc closes.

## Checks and qualification status

The local Deno type check passed. Four Deno integration groups passed against
the actual published Lean runtime: default-source reflow and link picking;
file base/external CSS; script/font/layout refusals; and resource/URL bounds.
The fifth group uses a real HTTP fixture. Direct Deno exec contexts refused
its socket bind with EPERM; outbound local HTTP also received EPERM.
Independent review then ran the identical five groups through the approved
Node 22 launcher and passed all five, including real HTTP redirect, CSS fetch,
and final URL/base behavior. That check used no GPU or native window. Its
command/status record is `/private/tmp/factoidal-native-html-review.json`;
stdout is `/private/tmp/factoidal-native-html-review.log`, SHA-256
`e242bb44a99146234c66c91c76bacf4ce206e32c600ff23ece5c7e5ec16f3aaa`.

```sh
deno check --no-config --no-npm --unstable-webgpu --unstable-ffi \
  labs/demos/foafnaut/run_html.ts
deno test --no-config --no-npm --unstable-webgpu --unstable-ffi \
  --allow-read --allow-write --allow-net labs/demos/foafnaut/native_html_test.ts
python3 tools/test-package-foafnaut2525.py -v
```

The five Python integrity controls passed, including changed/extra native
payload files, missing runtime manifest entries, wrong source commit, corrupt
archive, unsafe paths, and source/runtime mutation during compilation. These
controls do not claim to exercise GPU output.

One Deno compile completed with 7.8 GiB free at its start. Both app plists and
shell launchers passed syntax checks. Each app has 53 files; all original 47
package files have identical hashes and modes. The new HTML executable hash is
`677d6e93f9b1a7a677a1946d1e7badece491da35aae6de94cd74286c3bc74fbe`.
The compiled executable passed its CPU check from `/private/tmp`, using the
bundled HTML file: 1,405 primitives, 11 link fragments, and a Lean storage plan
with 157,104 parameter bytes. No window or adapter was requested by that check.
The first package used the builder before its concurrent-edit guard was added;
that exact builder is retained under the output's
`provenance/package-foafnaut2525.py`, and its hash matches the existing report.
No HTML/native host source or app file changed during that hardening.

HTML desktop qualification is pending in this record. It must separately
establish native presentation, resize reflow, link logging/navigation, and an
HTTP source. Reports and complete app inventories are under
`/private/tmp/factoidal-native-html-app-988/verification.json`.

## 2026-11-04 resume and integration review

Root resumed at approximately 15:36 on November 4 after the CUA app-selection
call stalled for about 14 hours and returned a running-app-not-found result.
There is no resulting native HTML GPU success, resize observation, or link
observation to record. The tool failure does not establish an application
crash or a GPU-driver failure. No further GUI calls or application launches
were made during this review.

Filesystem inspection found no HTML application output log under the package
directory or the known task-owned temporary paths, and no matching
foafnaut/native-webgpu/Deno crash report in the user's DiagnosticReports
directory. The retained `factoidal-native-html-review.log` is the successful
CPU/HTTP test output; it is not a desktop application log. The older
`factoidal-foafnaut2525-native-assessment-20261103.log` describes the earlier
exec-context FOAF assessment, not the new HTML app launch.

Current `origin/main` is
`7a9fa6abf54585e88992d70e7916e1a0015cb47f`. Compared with the isolated
`ed575e211` base, it changes no existing file under `labs/demos/foafnaut`, and
none of the rendering/DOM/HTML/CSS/XML module paths used by this host. The
mainline changes concern LWS, Solid, XMPP, dispatch/configuration and related
documentation. The HTML host continues to use the explicit 988 published
runtime, not an engine claimed to have been rebuilt from current main.
The updated mainline backup rule is noted; root retains ownership of this
lane's commit and merge.

Cheap checks on November 4 passed: all five Python integrity controls; all 13
compiled host/fixture source hashes; the retained original builder snapshot;
the complete 53-file inventory of each app, including the original 47 native
release files; and all 11 installed released runtime/library hashes, sizes,
and modes. Disk space was 3.6 GiB. No rebuild or repeat of the blocked direct
Deno networking context was attempted. The November 3 five-group CPU/HTTP
result remains historical evidence with its saved command, status and log.

## Frame timing, 2026-11-05

`run_html.ts` writes `native-html-frame` and `native-html-pump-stall` JSON lines.
`--resize-sweep` steps the window through fixed sizes and exits, with no person;
start it through `open`, then read it with `tools/native-frame-report.py`.

Baseline, Apple M1 with other work running, default page (1,405 primitives), 7
frames: median layout 157 ms, session 23 ms, draw and readback 2,035 ms, total
2,222 ms; 1,696 ns of draw for each pixel. Draw time follows the pixel count:
the fragment shader of `SVG.lean` loops over all primitives for every pixel.
Edge drags now reach Lean during the drag (8 resize events, 7 frames, no pump
stall in one human drag), but at this frame time few frames appear. Next: a
primitive list for each screen tile.

GPU step timing, same day and machine, `--resize-sweep`: at 1600 x 1000 the frame
took 2,974 ms, of which `mapRead` (the wait for the GPU) took 2,745 ms and copying
the readback out took 4 ms. The readback is not the cost; the shader is. A frame
is 1,600,000 pixels x 4 samples x 1,405 primitives, about 9.0 billion primitive
visits, or about 3.3 billion each second. Only polygons and paths have a bounds
check, and the walk over the variable-length records is serial for each sample.

## Primitive lists for each screen tile, 2026-11-05

`SVG.lean` writes a `tiles` table beside `data`: for each 32-pixel tile, the
primitives whose conservative box touches it, in paint order. The fragment shader
walks that list and not every primitive. A primitive with no known box joins every
tile, and a page over 1,000,000 list entries uses one tile. `data` and its proved
layout do not change. The table is a second storage binding, added by
`createPlanResources`; it is not yet in the Lean `RenderPlan`.

Same machine, `--resize-sweep`, default page, same seven sizes: median draw 2,074 ms
to 33 ms, median frame 2,278 ms to 209 ms. All seven frames have the same
`pixelHash` as the untiled engine. Lean layout, about 150 ms, is now the largest
stage. The hashes cover the default page only.

## Correction: why frames stopped, 2026-11-05

The commit that moved `installMenu` after `finishLaunching` says that the earlier
order stopped the window presenting. A 0-against-7 A/B supported that, but a later
run showed the same stall with the menu in its new place, and
`native-html-waiting` then recorded `occlusionVisible:false`: macOS reported the
window as covered. So the A/B was probably confounded by what was on the screen.
The cause of those stalls is unproven. `--resize-sweep` needs a visible window.

## Zoom, selection and copy (5 November 2026)

- Command-= or Command-+ makes text larger. Command-- or Command-_ makes it smaller. Command-0 resets it. The steps are in `WebSelection.lean`, and Lean layout applies them through `textScalePercent`. The scale stays when you go to a new page.
- A drag selects text, Command-A selects all and Command-C copies. Lean finds the glyphs, paints the highlight and makes the text. The host writes the clipboard only.
- A link now activates on mouse release, because a press can start a drag.
- Paste is not implemented: there are no form fields. Layout refuses `input` and `textarea`.
- Each drag step runs a full layout, about 300 ms on the home page. This makes selection feel slow.
- `--command-sweep` checks the menu keys, a drag and a link click in a real window. A covered window waits until it can present.

## XML pages with XSLT (5 November)

An XML page with `<?xml-stylesheet type="text/xsl" href="..."?>` in its prolog now renders. `labs/demos/foafnaut/WebXslt.lean` finds the instruction and reads the stylesheet's `version`: 1.x uses `L4Factoidal/XSLT`, and 2.0, 3.0 and 4.0 use `L4Factoidal/XSLT4`. The result goes to the normal HTML path. The host only fetches the page and the stylesheet.

A stylesheet receives no other document. So `xsl:import`, `xsl:include`, `document()` and `unparsed-text()` stop with a refusal. A remote page can not name a local stylesheet.

Cost of `web-render.wasm`, measured on 5 November with Deno on one laptop. The first row is an engine built before this change from nearly the same source.

| Engine | Bytes | Gzip | First start |
|---|---|---|---|
| no XSLT | 3,547,792 | 688,757 | about 220 ms |
| XSLT 1.0 only | 4,332,323 | 853,737 | about 300 ms |
| XSLT 1.0 and 4 | 14,501,181 | 2,928,175 | about 405 ms |

XSLT 4 is 10.2 MB of this. If that cost is too high, XSLT 4 can move to a second Wasm module that loads only for a page that needs it.
