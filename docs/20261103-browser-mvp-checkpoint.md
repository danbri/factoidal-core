# Browser MVP checkpoint, 2026-11-03

The local browser at `http://127.0.0.1:8099/` serves a frozen, tested snapshot.
Source checkpoint `285f83448d2824b403f025a8b78200c3c68cbaba` is pushed in
[Core PR 308](https://github.com/danbri/factoidal-core/pull/308).
Its post-checkpoint host fixes preserve the initial page in navigation history
and cancel obsolete renders. The snapshot records all host and binary hashes in
`labs/demos/foafnaut/.build/mvp-verified-20261103/snapshot.json`.

## What runs

Lean parses HTML, owns the DOM, parses and cascades CSS, lays out text and
blocks, lowers inline SVG and glyph outlines into the common path scene,
and selects click targets. WebGPU paints that scene. The host fetches resource
bytes and supplies HarfBuzz/FreeType glyph data for Lean-generated font requests.
It does not use the host browser to parse or lay out the displayed document.

The UI has URL entry, Go, Back, Forward, Reload and Stop. External CSS keeps
document order. The actual QuickJS-NG 0.18.0 WASI reactor runs in a separate
Worker and heap. Its small DOM binding returns commands that Lean applies to
the document. The initial fixture has real Arial text, SVG curves and a clickable
scripted counter. Script state survives viewport changes and resets on navigation
or source replacement.

This is a bounded rendering and scripting profile, not general Web platform
conformance. Flex/grid, complete font fallback and bidi, general WebIDL and JS
modules remain outside this profile. Unsupported cases must remain visible.
The independent SVG and font edge mismatches recorded in earlier worknotes are
not closed by these integration tests.

## Measured checks

| Check | Result | Local evidence |
| --- | --- | --- |
| Complete native/WASM document results, actual dynamic Arial data and CSS/DOM updates | 5 groups passed | `/tmp/factoidal-mvp-document-fonts/report.json` |
| Actual HTTP resources, QuickJS click, Lean mutation, font refresh and changed GPU pixels | 4 groups passed | `/tmp/factoidal-mvp-document/report.json` |
| Browser navigation and initial MVP screenshot | 5 groups passed | `/tmp/factoidal-mvp-navigation/report.json` |
| Frozen port 8099: counter click, link navigation, Back to fresh script state | 3 groups passed | `/tmp/factoidal-mvp-live-click-report.json` |
| Actual isolated QuickJS runtime, interrupts, timeouts and reset | 7 tests passed | `web-render/script-engine/session.test.mjs` |
| Actual HarfBuzz/FreeType font broker | 5 tests passed | `tools/test-font-broker.mjs` |
| Native/WASM width and nesting stress | 17 controls passed | [Layout stack audit](20261103-layout-stack-audit.md) |

The native macOS ARM64 scene CLI SHA-256 is
`82053979c7960447ff10318f4ca32e280dcf7d80a96941489b11d63698001b40`.
The paired WebAssembly SHA-256 is
`ce2f61b2ba4fe11f7ba86075025bb5d9630e039b836327f8e65f5e6499a4104a`.
These hashes identify the tested snapshot before the subsequent stack repairs.
The native CLI generates scenes; a native Metal window is not verified by these
checks. The actual GPU checks used Chrome 156.0.8078.80 on this Mac.

## Landing and distribution

Core PR 271 has merged to main. PR 308 is now the browser integration against
main. Its full-corpus CI exposed four retained recursion rows. Two are repaired
with exact compiler replacement proofs: [linear path extraction](20261103-rendering-path-stack-repair.md)
and scene traversal with an explicit work stack. The other two are the bounded
layout traversals; their emitted C, production callers and stress controls are
recorded in the [layout audit](20261103-layout-stack-audit.md).

[Builds PR 13](https://github.com/danbri/factoidal-builds/pull/13) has merged.
It checks the native document CLI initializer closure and relocated package
execution. That package does not yet bundle the browser host, font broker or
QuickJS runtime. The current npm package likewise does not expose this browser
API. A passing source checkpoint is not evidence of a published browser package.

The release process can pin an exact candidate SHA while main advances. An alpha
uses a prerelease version and the npm `alpha` tag; the stable `latest` tag stays
unchanged. Build and package gates apply to that exact candidate before publish.
An ephemeral branch is a useful name for the candidate, not a substitute for
recording its SHA. The next release decision must state which browser APIs and
assets the tarball actually contains.

Design records: [navigation](designissues/2026-11-03-lean-browser-navigation.md),
[fonts](designissues/2026-11-03-dynamic-font-requests.md),
[scripting and WASM boundaries](designissues/2026-11-03-script-engine-architecture.md).
