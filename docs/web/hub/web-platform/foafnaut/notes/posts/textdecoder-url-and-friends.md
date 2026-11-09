---
title: "TextDecoder, URL and friends, computed by Lean"
date: 2026-11-08T22:35:06Z
category: "Web APIs"
commit: "6f53d6ab7"
summary: "Page scripts have TextDecoder and TextEncoder, URL and URLSearchParams, atob and btoa, crypto.getRandomValues and randomUUID, structuredClone, and performance.mark and measure. Lean computes each operation in one call."
demos: ["js-status.html"]
---

- `TextDecoder` reads every encoding of the Encoding Standard, with `fatal`,
  `ignoreBOM` and streaming. `URL` is the WHATWG URL parser, with every setter.
- The page's JavaScript only converts arguments and shapes objects. Each API is set up
  on its first use, so a page that does not use it pays nothing.
- Lean now decodes the pages themselves too (commit
  [165a4af8f](https://github.com/danbri/factoidal-core/commit/165a4af8f)): HTML
  encoding sniffing, then the Encoding Standard's decoders. A 1 MB UTF-8 page takes
  7.2 ms; a 1 MB Shift_JIS page takes 66 ms.
- Theorems: the decoder never ends in an error in replacement mode, and a single-byte
  encoding gives back the byte it decoded.

Numbers: the design record
[2026-11-08-page-scripts.md, section 7](https://github.com/danbri/factoidal-core/blob/main/docs/designissues/2026-11-08-page-scripts.md#7-web-apis-over-lean).
