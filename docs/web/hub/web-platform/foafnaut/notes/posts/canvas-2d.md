---
title: "Canvas 2D, drawn by Lean"
date: 2026-11-09T00:28:21Z
category: "Canvas"
commit: "b5e306863"
summary: "Page scripts can draw with canvas.getContext('2d'). Lean parses the colours and fonts, builds and strokes the paths, shapes the text and rasterises every pixel."
demos: ["canvas-chart.html"]
---

The demo is an animated bar chart with a gradient, a line, dots and text labels. Each
frame, the page's calls go to Lean as one display list.

- 27 of 27 small test scenes match Chrome's pixels, on both script engines.
- Web platform tests `html/canvas/element` and `html/canvas/offscreen` on
  BubblePopJS: 1,764 of 2,294 subtests, up from 30.
- The chart demo's frame takes 28 ms natively.
- A page with no canvas pays nothing.

Not yet: images from the network (no `fetch`), `currentcolor` and `color-mix()`.

Numbers: the design record
[2026-11-08-canvas-2d.md, section 9](https://github.com/danbri/factoidal-core/blob/main/docs/designissues/2026-11-08-canvas-2d.md#9-results-2026-11-09-apple-m1-native-engine-library).
