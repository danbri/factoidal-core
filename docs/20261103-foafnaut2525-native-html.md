# foafnaut2525 native HTML development app

Native HTML desktop GPU qualification is still pending as of 2026-11-04.
The app and its CPU/runtime checks exist; no successful HTML native-window
presentation has been recorded.

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
