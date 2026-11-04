# Browser alpha packaging, 2026-11-03

[The packaging and alpha plan](designissues/2026-11-03-browser-alpha-packaging.md)
records the document CLI and WASM product scope, fixed-main-SHA publication,
portable host closure and exact npm workflow inputs.

The qualified core source is
[`63a73ff4af77abb41ca9d423171da1ecd635be33`](https://github.com/danbri/factoidal-core/commit/63a73ff4af77abb41ca9d423171da1ecd635be33).
The Builds packaging source is
[`0108b528db50c75c420db9709ca06878d23596b5`](https://github.com/danbri/factoidal-builds/commit/0108b528db50c75c420db9709ca06878d23596b5).

The compiled document ABI gate now calls `web_document_call` directly. It checks
inspection/base/resource URLs, typed commands with supplied CSS, bitmap
rendering, computed font requests, deterministic output and explicit resource
and command refusals. The gate is included in the qualified core source.

The next packaging increment is a portable browser host bundle in Builds.
An npm version change waits for reusable browser package functionality; the
current core tarball exposes the RDF engine and does not contain that bundle.
