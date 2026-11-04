# Browser alpha packaging and release scope

The next browser alpha should first qualify the existing Builds document CLI
and WASM release, then add a portable browser host bundle. Do not bump the npm
package only to attach the current demo: `@factoidal/core` currently exposes the
RDF engine, not the document renderer.

## What is implemented

The qualified core source is
[`63a73ff4af77abb41ca9d423171da1ecd635be33`](https://github.com/danbri/factoidal-core/commit/63a73ff4af77abb41ca9d423171da1ecd635be33).
It declares `@factoidal/core@0.29.0`. Its `files`
and `exports` contain the fat Lean RDF WASM under `l4-assets/`, public RDF APIs,
and protocol/store hosts. They do not contain `WebDocument`, its separate WASM,
the browser UI/server, the font adapter or QuickJS.

The Builds packaging source is main commit
[`0108b528db50c75c420db9709ca06878d23596b5`](https://github.com/danbri/factoidal-builds/commit/0108b528db50c75c420db9709ca06878d23596b5).
Its HTML document closure and native CLI packaging are in
[Builds PR 13](https://github.com/danbri/factoidal-builds/pull/13).

Builds now publishes two relevant experimental products from a fixed core SHA:

- `build-<sha12>-foafnaut-web` includes the HTML runtime under
  `docs/web/hub/html-webgpu/runtime/`. Its seven files are `web-render.mjs`,
  `web-render.wasm`, `render-plan.mjs`, `render-plan.wasm`, `gpu-transport.mjs`,
  `render-plan-host.mjs` and `source-witness.json`, plus `manifest.json`.
  The packager follows the C shim's initializers through the Lean source import
  closure, including `WebDocument`, script mutations and font requests.
- `build-<sha12>-foafnaut-darwin-arm64` includes
  `lean-html-scene-darwin-arm64`, its native source witness, a typed document
  request example and native CLI instructions. Relocation checks invoke
  `--document` from a new directory and reject error JSON.

The native document CLI accepts supplied resource bytes, commands and font data.
It does not fetch a URL or execute page JavaScript. Neither product includes the
local browser server/UI, QuickJS or the font broker. The seven-file WASM runtime
is a renderer and transport bundle, not the complete local browser application.

## Fixed source while main advances

The existing policy permits releases only from a core commit already on main.
`Builds/scripts/publish.sh` accepts GitHub compare status `identical` or `behind`
for `main...SOURCE_SHA`. An unmerged branch can run build gates, but publication
stops without creating a release. The npm workflow requires the exact `web`
release of its selected SHA, so an unmerged alpha branch cannot publish through
the current route.

Use an ephemeral branch as a pointer to the tested main commit. Pass its full
SHA to the build and publish workflows. Later main commits do not change that
checkout or release identity. This satisfies the fixed-candidate requirement
without changing publication policy or blocking further main development.

```sh
gh workflow run build.yml --repo danbri/factoidal-builds \
  -f core_ref=FULL_TESTED_MAIN_SHA -f force=false
```

`build.yml` accepts a branch, tag or full SHA in `core_ref`; a full SHA is the
reproducible choice. `force` defaults to false. Do not force a web release already
named by a published npm version: Builds refuses replacement. One release
manager owns dispatches and reruns; the shared workflow queue has one running
and one waiting run.

## Minimal next increments

1. Qualify the same fixed source in the native document CLI and seven-file WASM
   runtime. The current WASM ABI gate must call `web_document_call` directly;
   the older HTML/RDF exports alone do not establish that the document export
   was linked. Test inspection/base URLs, supplied CSS, commands, computed font
   requests and refusals. Keep native relocation and exact source/C/engine
   witnesses. This increment needs no npm version change.
2. Add a separate portable host bundle to Builds. Include the actual UI,
   `engine.mjs`, navigation/resource/document clients and server, the font
   broker, QuickJS worker/guest/session, the pinned QuickJS WASM, the renderer
   and render-plan engines, and their licenses and manifests. Resolve the
   current development `/lab/...` paths in the packager or server URL map.
   Add the host source files and pinned upstream assets to provenance.
3. Package the native font adapter and its shared-library dependency closure
   for each supported host. Check `otool -L` or `ldd` after relocation. Make
   the font-file/family binding explicit. Do not redistribute system Arial.
   Use a licensed redistributable curved font for CI, with an exact font hash,
   family name and license. Linux cannot depend on the macOS default font path.
4. Run a relocated host-bundle browser check. It must load source bytes, fetch
   external CSS/JS, execute bounded QuickJS, mutate the Lean DOM, shape changed
   text through the actual adapter, render GPU pixels and dispatch a click.
   Verify the package runs without the development checkout. Distinguish these
   checks from native CPU checks and from a conformance claim.
5. Add an npm browser-document API only when there is a reusable consumer
   entry. An explicit subpath can preserve the existing RDF entry. Include its
   typings and renderer assets; do not put demo fixtures in the core tarball.
   Test import from an extracted tarball and a browser under CSP. A pure web
   caller must supply font/resource data or use a declared host capability;
   it cannot assume the local native broker exists.

## npm alpha parameters and gates

`npm-publish.yml` already accepts `dist_tag=alpha` and a prerelease version in
`confirm`. It requires `core_ref` to be exactly 40 lowercase hex characters,
`dist_tag` to match `^[a-z][a-z0-9-]*$`, and `confirm` to match the package version.
It consumes only `build-<sha12>-web`, not the experimental native/browser sets.
Therefore publishing an npm alpha today would not, by itself, distribute the
new browser products.

When useful browser package functionality is present, choose an unpublished
version such as `0.30.0-alpha.1`. Bump `package.json`, both root lockfile versions,
`lib/version.mjs` and the dated changelog heading together. Merge and test that
candidate on main, freeze its SHA, produce its `web` release, then dispatch:

```sh
gh workflow run npm-publish.yml --repo danbri/factoidal-builds \
  -f core_ref=FULL_TESTED_MAIN_SHA -f dist_tag=alpha \
  -f confirm=EXACT_UNPUBLISHED_PRERELEASE_VERSION
```

The existing workflow requires successful `web-gates` in the build run, verifies
release source identity and each installed file hash, checks version consistency
and the registry, checks packed WASM/stamp/source hashes, and publishes the
packed tarball with OIDC provenance. It does not run `prepublishOnly` on that
tarball. The package suite runs in `web-gates` and must report zero skips.
Trusted publishing uses Node 24 and npm at least 11.5.1. No token/login/OTP route
is needed.
The release manager must separately retain browser/CSP, bundler, native/WASM
identity and relocated host evidence. Existing core `web-gates` do not establish
the local browser application's complete runtime closure.

## Evidence and limits

The compiled document ABI probes are committed in
[`2f1d185fd`](https://github.com/danbri/factoidal-core/commit/2f1d185fd) and included
in the qualified core source above. They call the actual `web_document_call`
export and check seven operation groups: inspection/base/resource URL, typed
commands with supplied CSS, source-linked anchors, bitmap selection, computed
actual-font requests, missing/duplicate resource refusal and unsupported-command
refusal. Rendering uses the bitmap profile; request collection names Arial but
requires no proprietary font on the runner.

The source witness records core `63a73ff4af77abb41ca9d423171da1ecd635be33`, WASM
SHA-256 `7b8992f7268a6d957d75160fc6c36711fc5cade6566a68af3edcfb226d83ac37`, and
native SHA-256 `ee90a9317456104a6104f9219cfe536774fad9aa6888f94cfa18e6a1e7e3c7de`.
The native/WASM document-font comparison and browser document check report PASS
in `/tmp/factoidal-mvp-stack-document-fonts/report.json` and
`/tmp/factoidal-mvp-stack-document-browser/report.json`. These identify the local
qualified checkpoint. They are not a claim about completion of every remote CI
job or the presence of a published release.

Uncached npm registry and tarball reads failed with `ENOTFOUND` during this
audit. No live registry tag inventory or published-tarball contents are claimed.
The workflow input and package-scope findings above come from source inspection.
