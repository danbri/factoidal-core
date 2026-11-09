---
title: "WebAssembly in pages"
date: 2026-11-09T02:52:09Z
category: "Wasm"
commit: "8c0a68eb0"
summary: "Page scripts have the WebAssembly JavaScript API on both script engines. Lean decodes, validates and runs each module in WasmVM; the browser's own WebAssembly engine runs none of them."
demos: ["wasm-mandelbrot.html"]
---

The demo instantiates a 310-byte module. Its script reads the module's memory through
`Memory.buffer` and draws eight SVG paths; a click zooms.

- Web platform tests `wasm/jsapi`: 940 subtests pass on QuickJS-NG and 937 on
  BubblePopJS, up from 1. Chrome passes 1,169 of 1,322.
- One call from JavaScript into WebAssembly and back takes 0.05 ms on BubblePopJS
  and 0.19 ms on QuickJS-NG, natively.
- A page that does not touch `WebAssembly` pays nothing: the API's script loads on
  first use.

Not yet: SIMD, GC types and 64-bit memories (WasmVM has none of them), and
`compileStreaming` (pages have no `fetch`).

Numbers: the design record
[2026-11-08-page-wasm.md, sections 6 and 7](https://github.com/danbri/factoidal-core/blob/main/docs/designissues/2026-11-08-page-wasm.md#7-wpt).
