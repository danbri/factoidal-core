---
name: npm-release
description: Release the Factoidal npm packages — which artifacts each build script produces, which files each package ships (since 0.9.0 the Lean 4 wasm engine only), how the version and the WebAssembly digest are stamped into version.json, how trusted publishing through the OIDC workflow works and why a token or one-time password never will, the gates that must be green first, and the traps that have cost time. Use before publishing @factoidal/core, before bumping a package version, when a wasm rebuild has to reach the package, when npm publish fails on authentication, or when the four wasm copies disagree.
---

# Releasing the Factoidal npm packages

Two packages exist. Only one is current.

| Package | Directory | Status |
| --- | --- | --- |
| `@factoidal/core` | `npm/factoidal/` | current; carries one engine, the Lean 4 wasm (since 0.9.0) |
| `@factoidal/lean` | `npm/factoidal-lean/` | superseded by https://github.com/danbri/factoidal/issues/618; never published; a frozen manual-override copy |

`@factoidal/core` carries ONE engine since 0.9.0: the Lean 4 library
`L4Factoidal` compiled to WebAssembly, under `l4-assets/`. Owner,
2026-10-10: "We should make the main module Lean4-based. Private builds
might compare this with F\* (or indeed different wasms from different
toolchains)." The F\* bundles (`factoidal.js`, `factoidal-npm-entry*.js`,
their wasm builds, `hacl-wasm/`) are `danbri/factoidal-builds` artifacts
only, used by the private comparison harness
`tests/engine-compare/run.sh PATH/TO/factoidal-npm-entry.js`. Do not put an
F\* bundle back into `files`. Record:
`docs/designissues/2026-10-10-npm-lean-only.md`,
https://github.com/danbri/factoidal/issues/713. Do not publish
`@factoidal/lean` unless the owner asks for the override channel by name;
its workflow refuses to run without a typed confirmation phrase.

## What builds what

Since 2026-10-09 (iron rule 9) none of the built files named below is
committed to `danbri/factoidal-core`; they are in `.gitignore`. The `web`
release set of `danbri/factoidal-builds` carries the F\* JS and wasm
bundles, the Lean wasm and its copies. `tools/fetch-builds.sh --set web`
installs them into a checkout. The commands below write the same paths
for a local build. Use them to test; do not stage their output.

### The Lean engine (WebAssembly)

```bash
bash formal/lean4/Wasm/build-wasm.sh          # about ten minutes
```

It compiles `L4Factoidal` to `l4factoidal.wasm`, writes Emscripten's glue
`l4factoidal.mjs` and the repository's own loader `l4factoidal.js`, then
installs **four byte-identical copies**:

| Copy | Directory | Who reads it |
| --- | --- | --- |
| 1 | `docs/web/hub/assets/l4/` | the GitHub Pages hub posts |
| 2 | `npm/factoidal/l4-assets/` | `npm install @factoidal/core` — the copy that ships |
| 3 | `npm/factoidal-lean/` | the superseded companion package |
| 4 | `docs/npm/lean/` | the Pages mirror of that companion |

**Gap found 2026-10-09, closed the same day (commit 15b4940d):** the core split had left out
`npm/factoidal/l4-assets/`, so `build-wasm.sh` printed "npm/factoidal/l4-assets
absent — in-package step skipped" and copy 2 was never produced. The
directory is in git again with its `package.json` and `version.json` (the
wasm and the loaders stay out, by `.gitignore`), and step 9 fills it.

`npm/factoidal/l4-assets/` also holds a four-line `package.json` that
says `{"type": "module"}`. The parent package sets no `"type"`, so `.js`
there is CommonJS, and without that file Node prints a
`MODULE_TYPELESS_PACKAGE_JSON` warning on stderr every time
`l4factoidal.js` is imported — which the `factoidal` command does on
every `inspect` and every `query`. `build-wasm.sh` copies the three
engine files by name and leaves it alone; do not delete it.

Step 9 of the script compares all four against the freshly built
SHA-256 and exits 1 when one differs. Trust that check; do not copy
these files by hand. Copy 2 was missing from the script until
2026-08-26, and one rebuild left `l4-assets/` holding the previous wasm
while the other three carried the new one, with every suite green.

The loader carries the wasm's own digest: step 9 rewrites
`const WASM_VERSION = "<first 12 hex of the sha256>";` inside
`l4factoidal.js` before copying it anywhere, and the loader puts that
value in the `?v=` query of its wasm fetch. The Pages service worker
(`docs/sw.js`) caches by pathname, so without that stamp a fresh loader
can pair with a stale wasm for one page load after a deploy.

### The F\* engine bundles: comparison builds only

`formal/fstar/build-ocaml.sh js` builds the js_of_ocaml bundles (and its
`npm` step still copies them into `npm/factoidal/`, where `files` ignores
them). They are not part of the package since 0.9.0. The comparison harness
takes the npm-entry bundle by path:

```bash
tools/fetch-builds.sh --set web           # docs/fstar-extracted/factoidal-npm-entry.js
tests/engine-compare/run.sh docs/fstar-extracted/factoidal-npm-entry.js
```

`npm run build` inside `npm/factoidal/` is
`bash ../../formal/lean4/Wasm/build-wasm.sh`.

## What each package ships

`files` in `npm/factoidal/package.json` is the list. Since 0.9.0:

- Entries: `index.js` + `index.mjs` (Node; `index.js` hands the ES module
  to `require()`, so `engines.node` is `>=22.12`), `browser.js`,
  `api.js` + `api.mjs` (`createApi(engine)`), `fn.js`, `rdfjs.js` +
  `rdfjs.mjs`, the 0.9.x aliases `l4.js` and `l4-core.js`, and a `.d.ts`
  beside each.
- The typed layer: `lib/` (`api.mjs`, `lean-entry.mjs`, `store.mjs`,
  `version.mjs`). ES modules with no Node built-ins: the browser imports
  them as they are.
- The engine: `l4-assets/` (`l4factoidal.js`, `.mjs`, `.wasm`,
  `version.json`, `package.json`).
- Store, command and protocol hosts: `store-host/`, `bin/`, `lws/`,
  `solid/`, `xmpp/`, `sample-store/` + `sample-store.mjs`.
- Metadata: `README.md`, `CHANGELOG.md`, `LICENSE`, `NOTICE`.

The wasm is not in git (iron rule 9). A tarball packed from a checkout
without `l4-assets/l4factoidal.wasm` has no engine;
`test/pack-integrity.test.js` fails then.

`bin` maps the command `factoidal` to `./bin/factoidal.mjs`. A consumer
gets it on PATH from a global install and in `node_modules/.bin` from a
local one. `bin/` holds three files: the command, `engine.mjs` (which
resolves and loads the wasm engine, in ESM so it works under Deno where
`l4.js` does not) and `store.mjs` (which drives the three store
operations). `version`, `inspect` and `query` run; `pack`, `activate`,
`update` and `compact` exit 3 and name
https://github.com/danbri/factoidal/issues/641.

Check the list before every publish:

```bash
cd npm/factoidal && npm pack --dry-run
```

Anything absent from `files` is absent from the tarball, whatever the
working tree holds.

## How the version and the digests are stamped

Two `version.json` files, two writers. (Until 0.9.0 a third,
`npm/factoidal/version.json`, carried the F\* engine's claims; it left the
package and git with the F\* engine.)

| File | Written by | Carries |
| --- | --- | --- |
| `npm/factoidal/l4-assets/version.json` | `build-wasm.sh` step 9 | the Lean engine's provenance, refreshed in place so its `engine` and `note` members survive |
| `npm/factoidal-lean/version.json` | `build-wasm.sh` step 9 | the same provenance for the superseded companion |

The Lean provenance members are `version`, `gitSha`, `builtAt`,
`leanToolchain`, `emscripten`, `abiVersion`, `wasmSha256`, `wasmBytes`
and `claims`. `factoidal version` prints them, which is the quickest way
to see which engine an install actually holds.

`l4-assets/version.json` is tracked in git with its `engine` and `note`
members; step 9 rewrites the provenance members in place on every build.
Commit only a deliberate edit of `engine`, `note` or `claims`, never the
stamped members (the same holds for the `WASM_VERSION` line the build
stamps into `docs/web/hub/assets/l4/l4factoidal.js`).

Bumping the package version is a manual edit of `version` in
`npm/factoidal/package.json`, `package-lock.json` (two places) and
`npm/factoidal/lib/version.mjs` (the browser cannot import JSON;
`test/dts-drift.test.js` checks the two agree), plus a `CHANGELOG.md`
entry.

## How publishing works

**Status 2026-10-09: no active publish workflow exists for
`danbri/factoidal-core`.** `npm-publish.yml` and `npm-publish-lean.yml`
moved to `factoidal-builds/legacy-workflows/` in `danbri/factoidal-builds`,
where they are inactive (not under `.github/workflows/`). Porting them
needs an owner step on npmjs.com: the Trusted Publisher entry must name
repository `factoidal-builds` and the new workflow file. Read
`legacy-workflows/README.md` in that repository for the current state of
the port. The copies that remain in `danbri/factoidal` (branch
`claude/main`) belong to that repository and build its tree, not the
`factoidal-core` tree; do not use them to release core. The rest of this
section describes the old workflow. A port has to reproduce it.

`.github/workflows/npm-publish.yml` (old repository), trusted publishing
through OIDC. There are no npm tokens anywhere in this repository, and
there is no way to add one that would work.

**The owner's npmjs.com account is security-key-only. Publishing with a
token, or with a one-time password, always fails.** Do not suggest
`npm login`, `npm publish --otp`, an automation token or a CI secret;
each of those is a dead end for this account. The only path that
publishes is the workflow.

Trigger it in one of two ways:

- `gh workflow run npm-publish.yml --repo danbri/factoidal` (old
  repository only; see the status note above)
- push a tag matching `npm-v*` (same)

What the workflow does, in order:

1. checks out with `submodules: recursive` — the package's own
   `prepublishOnly` runs `npm test`, and that suite reads vendored W3C
   fixtures from `third_party/testing/`. Without the submodules the
   suite dies on ENOENT and the publish aborts. That is how run 2 failed
   on 2026-08-27, 22 minutes after the drift check had passed.
2. installs opam, F\* and z3 4.13.3, with caches.
3. re-extracts the whole F\* corpus with
   `./build-ocaml.sh extract --force-full` and fails on any difference
   against the committed `.ml`. `--force-full` is what stops a manifest
   hit turning the check into a vacuous pass.
4. logs a provenance witness: F\* and z3 versions, the digest of the
   `.fst` input tree, the digest of the glue tree.
5. `npm publish` from `npm/factoidal`, with provenance generated
   automatically (Sigstore-signed, Rekor-logged; a consumer checks it
   with `npm audit signatures`).

The npmjs.com side was configured once by the owner: package Settings →
Trusted Publisher → GitHub Actions, organization `danbri`, repository
`factoidal`, workflow filename `npm-publish.yml`, environment blank,
allowed action `npm publish`. Those fields are case-sensitive and npm
validates them only at publish time, so a typo shows up as a failed
publish and nothing earlier. That entry names `danbri/factoidal`; a
workflow in `danbri/factoidal-builds` publishes only after the owner
changes it.

Cost: five to ten minutes with warm caches; about two hours with a cold
`.checked` cache, because the tree re-verifies.

## The gates before a release

Run these from the repository root, with the numbers each one must
produce. A number that has moved is a finding to explain, not a number
to overwrite. Gates that read `docs/fstar-extracted/*.js`, `npm/factoidal/`
bundles or the Lean wasm need those files installed first
(`tools/fetch-builds.sh`) or built locally.

| Gate | Command | Expected, measured 2026-10-10 (0.9.0, issue 713 stage 3) |
| --- | --- | --- |
| package suite | `cd npm/factoidal && npm test` | 372 pass, 0 fail, 0 skipped (out of 372), after the issue-716 merge (371 pass, 0 fail (out of 371) at the stage 3 merge). 4 of the 372 are expected-failure cases, each naming its open issue: 717 (1, `SERVICE` without `SILENT`), 691 (1, unused `@prefix xsd:`), 676 (2, PRECIS); the 2 cases of 716 (`{lenient:true}`) are assertions since that merge. A function the wasm does not serve FAILS; no test skips on a capability probe. (0.8.0: 340 pass, 0 fail, 2 skipped (out of 342), on the F\* bundles) |
| store host | `node tests/store-host/conformance.mjs` | 34 pass, 0 fail, 0 skipped (out of 34) under Node |
| the command | `node tests/store-host/cli.mjs` | 33 pass, 0 fail, 0 skipped (out of 33) under Node |
| LWS and Solid hosts | `node tests/lws/server.mjs`, `node tests/solid/server/protocol.mjs`, `node tests/solid/client/against-own-server.mjs` | 8, 12 and 7 pass, 0 fail |
| tarball | `cd npm/factoidal && npm pack --dry-run` | the `files` list above: 161 files, 2,410,574 bytes packed, 12,042,704 unpacked; no F\* bundle, no `hacl-wasm/` (0.8.0: 193 files) |
| wasm copies | the tail of `build-wasm.sh` | "all committed wasm copies agree" |
| Lean native | `bash formal/lean4/Wasm/native-smoke.sh` | 297 pass, 0 fail (out of 297); needs `lake` on PATH (`export PATH=$HOME/.elan/bin:$PATH`) |
| browser | `tests/web-demos/npm_browser_smoke.sh` | PASS: `browser.js` in headless Chromium runs a parse, a SELECT, `canonicalize`, `xpathEval` and `openStore` over `fetch`, with one `instantiateStreaming` call and the wasm served as `application/wasm` |
| bundler and CSP page | `tests/web-demos/bundler_csp_smoke.sh` | PASS, exit 0 (esbuild bundle of the package under `script-src 'self' 'wasm-unsafe-eval'`) |
| engine comparison (private build, not a release gate) | `tests/engine-compare/run.sh docs/fstar-extracted/factoidal-npm-entry.js` after `tools/fetch-builds.sh --set web` | 7 pass, 0 fail (out of 7) against the F\* bundle of build-dba1bdb1d320-web; exit 2 when the bundle is absent |
| hub notebooks | `node --test tests/hub/*_test.mjs` | not a package gate since 0.9.0: the node harness binds this package (Lean) and the hub pages load the F\* driver `docs/fstar-extracted/browser.js`. 353 pass, 34 fail (out of 387) on 2026-10-10 with no F\* bundle or F\* native binary installed; the failures are Lean/F\* output differences, F\*-only functions (COTTAS, `text:query`, `geof:distance`, `geof:envelope`) and files that need an F\* build (design record `docs/designissues/2026-10-10-npm-lean-only.md` § 7) |

The package suite runs again inside `npm publish` through
`prepublishOnly`, so a failure there aborts the publish after the
workflow has already spent its F\* re-extraction time.

Install the tarball somewhere else and run the command before
publishing. A `files` entry that names a directory which does not exist
produces a tarball that installs and then fails on first use:

```bash
cd npm/factoidal && npm pack --pack-destination /tmp
mkdir /tmp/probe && cd /tmp/probe && npm init -y
npm install /tmp/factoidal-core-<version>.tgz
./node_modules/.bin/factoidal --help
./node_modules/.bin/factoidal version
# The store path, against a generation the native packer wrote:
./node_modules/.bin/factoidal inspect STORE
./node_modules/.bin/factoidal query STORE 'SELECT (COUNT(*) AS ?n) WHERE { ?s ?p ?o }'
deno run --allow-read node_modules/@factoidal/core/bin/factoidal.mjs query STORE 'ASK { ?s ?p ?o }'
```

`version` alone does not exercise the engine: it reads
`l4-assets/version.json` and never loads the wasm. `inspect` is the
cheapest command that proves the shipped wasm loads and answers.

## Traps

1. **The four wasm copies drift when a file is copied by hand.** Let
   `build-wasm.sh` place them; its step 9 is the only thing that checks
   them. (Issue 618, 2026-08-26.)
2. **`npm pack` reports the `files` list, not the working tree.** A new
   directory is invisible to the tarball until it is added to `files`.
   Both `bin/` and `store-host/` needed an entry when they were added on
   2026-09-03; without them `npm pack --dry-run` listed 53 files and the
   `bin` mapping pointed at nothing.
3. **`bin` needs the executable bit and a shebang.** `bin/factoidal.mjs`
   starts with `#!/usr/bin/env node` and is committed with mode 755. npm
   sets the bit on install, but a source checkout that runs the file
   directly needs it too.
4. **Deno ignores the shebang.** Run the command under Deno as
   `deno run --allow-read --allow-write node_modules/@factoidal/core/bin/factoidal.mjs`.
   Grant only the permissions the subcommand needs; `inspect` and
   `version` need `--allow-read` alone.
5. **`.js` in `npm/factoidal/` is CommonJS.** The package sets no
   `"type"`, so ESM files carry the `.mjs` extension. `store-host/` and
   `bin/` are `.mjs` for that reason.
6. **Deno 2 removed the resource-id fsync calls.** `Deno.fsyncSync` no
   longer exists; the file-handle method `FsFile.syncSync()` is the one
   to call. Code written against Deno 1 fails at run time with
   "Deno.fsyncSync is not a function".
7. **A conformance run that finds no native binary reports a green
   skip.** `tests/store-host/conformance.mjs` prints the skipped count
   next to the passes for exactly that reason, and it raises rather than
   skips when `L4_BIN_DIR` names a directory with no `l4block-shard-pack`
   in it. Read the skipped column before quoting the score
   (anti-pattern 3).
8. **A git worktree has no `formal/lean4/.lake/build`.** Tools that need
   the native Lean binaries must fall back to the main checkout
   (the conformance test reads the worktree's `.git` pointer file to
   find it) or take an `L4_BIN_DIR` override.
9. **The version in `package.json` and the versions in the three
   `version.json` files diverge silently.** Bump, then rebuild, then
   check `factoidal version` before tagging.
10. **`process.exit()` truncates a piped result.** Node writes to a pipe
    asynchronously and drops what is still buffered when the process
    exits. `factoidal query --format json` printing 6455 rows into a
    pipe arrived cut at the 64 KiB boundary until `bin/factoidal.mjs`
    stopped calling `process.exit()` and set `process.exitCode` instead
    (2026-09-03). Any new subcommand that prints a large result must
    keep that shape.
11. **Node's WebAssembly frame budget is smaller than Deno's.** Some
    Lean evaluator paths recurse once per row. Measured 2026-09-03 on a
    6455-row store, `SELECT ?s ?p ?o WHERE { ?s ?p ?o }` raises a
    `RangeError` inside the wasm module under Node's default while
    `SELECT *`, or the same query with a `LIMIT`, does not, and Deno
    clears all of them; `node --stack-size=4000` clears it too. The
    command turns that into an explained exit 1, and
    `tests/store-host/cli.mjs` gates the explanation rather than the
    success, because the outcome depends on the runtime. Do not read a
    green run under Deno as evidence that the Node path is clear.

## Where the pieces are

- Lean wasm build and its mirrors: `formal/lean4/Wasm/build-wasm.sh`,
  and [`skills/lean4-wasm-export/SKILL.md`](../lean4-wasm-export/SKILL.md)
  for the toolchain and the export ABI.
- F\* bundle and package population: `formal/fstar/build-ocaml.sh`
  (`js`, `wasm`, `npm` steps), and
  [`skills/build-and-test/SKILL.md`](../build-and-test/SKILL.md).
- Bundle profiles (full and lite), the entry ABI contract and the
  measured sizes: [`docs/designissues/2026-09-16-npm-usability-and-bundle-profiles.md`](../../docs/designissues/2026-09-16-npm-usability-and-bundle-profiles.md)
  and `bin/npm-entry/README.md`.
- Publish workflows: `npm-publish.yml` and `npm-publish-lean.yml`, now
  inactive under `legacy-workflows/` in `danbri/factoidal-builds` (see
  "How publishing works"). Release files: the `build-<12 hex>-<set>`
  releases of `danbri/factoidal-builds`.
- The persisted store the command drives:
  [`skills/shardborough-storage/SKILL.md`](../shardborough-storage/SKILL.md)
  and `docs/shardborough-storage-spec.md`.
- The milestone that adds the remaining subcommands:
  https://github.com/danbri/factoidal/issues/641, with the byte
  transport it depends on at
  https://github.com/danbri/factoidal/issues/640.
