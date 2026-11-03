# Checked browser development bundle, 2026-11-03

`tools/package-web-render.py` packages the local browser without compiling,
downloading or rewriting its host modules. It checks committed input bytes,
the complete Lean source and generated-C closure, engine hashes and the separate
QuickJS pin before it writes a deterministic archive. The launcher verifies the
inventory and probes the actual font adapter before binding a loopback server.

A later host commit can reuse an ancestor engine only when every witnessed
engine source file is byte-identical to that build commit and to the committed
checkout. Generated C and binary hashes must still match, and the complete
source/C dependency checks still apply. The manifest records `sourceCommit`
for the host and `engineSourceCommit` for the engines separately. This permits
UI fixes without recompiling unchanged Lean code; a changed Lean file cannot
be admitted by simply editing its witness hash.

The bundle contains the HTML/CSS UI, navigation and resource clients, document
host, four Lean renderer/plan engine files, the QuickJS worker/runtime and MIT
notice, font broker and native font adapter. The development fixtures are kept
in this separate bundle. They are not added to the core npm tarball.

This is a development bundle with external dependencies: Node 22.13 or newer,
a WebGPU browser, the adapter's listed HarfBuzz/FreeType libraries, and a licensed
Arial font selected with `FACTOIDAL_FONT_FILE`. No system font or Homebrew library
is copied into it. The adapter binary and source hashes are recorded; the
packager does not itself prove their build correspondence. It is not a standalone
native macOS browser application.

## Qualified source and runtime

Core `63a73ff4af77abb41ca9d423171da1ecd635be33` has been built and tested locally.
The macOS ARM64 CLI SHA-256 is
`ee90a9317456104a6104f9219cfe536774fad9aa6888f94cfa18e6a1e7e3c7de`;
the renderer WASM SHA-256 is
`7b8992f7268a6d957d75160fc6c36711fc5cade6566a68af3edcfb226d83ac37`.
Both include the proved path/scene stack repairs and normalized script kinds.

- Six complete native/WASM document groups pass, including arbitrary real-font
  edits, supplied CSS order and importance, MIME normalization and refusals.
- The WASM ABI gate passes the original HTML/RDF checks and seven document
  operation groups, without depending on a proprietary font on CI.
- Four actual Chrome document groups pass: external resources, script click,
  Lean mutation, new shaped words and changed GPU pixels; resize preserves
  the VM and replacing source resets it.
- Seventeen native/WASM layout stress controls pass on the new engines,
  including 50,000 siblings and exact depth refusal. The native execution
  thread's requested 512 KiB stack is calibrated with an overflowing control.

Reports: `/tmp/factoidal-mvp-stack-document-fonts/report.json`,
`/tmp/factoidal-mvp-stack-wasm-check.json`,
`/tmp/factoidal-mvp-stack-document-browser/report.json` and
`/tmp/factoidal-layout-stack-final-runtime.json`.

## Packaging checks

Ten structural/negative controls pass. They reject stale source, missing
source/C dependencies, unreviewed initializer imports, wrong engine/dependency
bytes and unsafe inputs. The three additional controls admit a host-only
descendant, reject changed Lean bytes even with a modified witness hash, and
reject an unknown engine commit. These structural fixtures do not claim to run Lean.

The separate integration check packages the actual runtime twice and compares
the entire archives, extracts into a directory containing spaces, verifies the
launcher, then runs Chrome against the relocated application. Actual Arial
text, the QuickJS counter, link navigation and Back pass. An altered host module
is then rejected before the server binds. An independent check also verifies
12 served routes and an actual font-shaping response.

The initial archive is
`/private/tmp/factoidal-browser-development-verification/first.tar.gz`, SHA-256
`e640bc2bbdf42660f0b46d4afa6c106cd10c5e9a324c1fd2e769810c7fd3fa1c`.
It contains 37 inventoried files plus the manifest and checksums. The clean
extracted bundle is `first/`; the separate relocation-test copy is deliberately
altered by the negative control. Reports are `package-report.json` and
`browser-report.json` in that directory, and
`/private/tmp/factoidal-browser-package-independent-review.json`.

Build from a checkout with matching witnessed engines:

```sh
python3 tools/package-web-render.py --out /tmp/NEW-browser \
  --archive /tmp/NEW-browser.tar.gz
node /tmp/NEW-browser/start.mjs --verify
FACTOIDAL_FONT_FILE=/path/to/licensed/Arial.ttf node /tmp/NEW-browser/start.mjs 8099
```

The unit and integration commands are documented in
`tests/test_package_web_render.py`. Environments that require direct Node
launches can use its prepare, browser and finish phases; the finish phase
requires a real successful browser report and runs the tamper control.

## Shipping boundary

The [alpha plan](designissues/2026-11-03-browser-alpha-packaging.md) separates the
current document CLI/WASM release from this host bundle and a future reusable
npm entry. No npm browser alpha or public deployment is claimed by these local
checks. Core PR 308 remains subject to its exact source and Builds gates.
Independent SVG/font conformance failures remain open.
