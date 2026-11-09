---
title: foafnaut2525 project status
description: Where the Lean web rendering engine stands, with the score of each test suite. The engine renders this note itself.
layout: hub.njk
---

# foafnaut2525 project status

8 November 2026. The engine that this note describes renders it too: choose Project status in the Lean HTML page below. The rendering is plain ASCII text with no script.

foafnaut2525 is a web rendering engine written in Lean. It aims to become a browser. It is not the FOAF social network application that it is named after.

## Where it is

- The engine parses HTML, computes CSS, lays out text and boxes, and draws with WebGPU.
- It runs in a web page, in its own macOS window, and as a sandboxed guest.
- Page scripts run in BubblePopJS, a JavaScript engine written in Lean, in the macOS app, and in QuickJS-NG inside WasmVM, a WebAssembly engine written in Lean, on the Hub. Settings choose between them. Lean's event loop and DOM decide every callback and every change.
- Pages can draw with WebGPU and WebGL 1 and 2; Lean checks every command first. Without WebGPU, a CPU renderer draws the same pixels.
- Real sites mostly do not load yet.

## Since 6 November

- BubblePopJS is the default script engine in the macOS app, with a switch in settings. There it runs the same scripts 10 to 13 times faster than QuickJS-NG in WasmVM.
- WasmVM runs QuickJS-NG, HarfBuzz and media decoders, and on the Hub it translates guest WebAssembly for the browser's own engine: 36 to 216 times faster.
- Page scripts: timers, animation frames, Promises, clicks and pointer events, forms, DOMParser, MutationObserver and layout reads.
- Arabic letters join, and mixed left-to-right and right-to-left text is ordered by the Unicode bidi algorithm. Emoji draw from Noto Emoji.
- Momentum scrolling, swipes for back and forward, a folding address bar, Copy address and Paste and go, and printing.
- Links work anywhere on a long page, with theorems that every link region is kept.
- Text starts larger, and settings have large text-size buttons.

## Measured scores

- HTML tree construction: 1,963 pass, 10 fail (out of 1,973).
- HTML tokenizer: 7,047 pass, 6 fail (out of 7,053).
- WPT SVG and HTML images: 39 match, 68 mismatch, 214 unsupported, 23 rejected, 257 unavailable (out of 601).
- WPT scripted documents (dom, events, timers, microtasks, event loops), QuickJS-NG in WasmVM: 12,605 of 13,705 subtests pass (8 November).
- Test262 sample (436 files), QuickJS-NG in WasmVM: 431 pass. BubblePopJS: 5,618 of 6,297 in a 70-directory language subset (8 November).
- W3C SVG Tiny 1.2, WebGPU pixels against the W3C images: 0 match, 157 close, 336 mismatch, 2 refused, 1 not read (out of 496). No test passes yet. Our 1-pixel lines are anti-aliased, and the 2008 reference snaps them, so a strict match needs more than correct drawing. A blank image scores 1 match, 495 mismatch.
- HarfBuzz 15.0.0 shaping suite: 4,175 pass, 533 fail, 169 refused (out of 4,877 applicable).

The match and close bands are ours, not a W3C verdict. The WPT image score still comes from the old CPU test tool. These suites are separate. Their numbers do not add up to one browser score. The script scores are from 8 November; the others were measured between 4 and 7 November.

## What comes next

- A named release every day: one to three, never four.
- BubblePopJS on the Hub: its evaluator needs more stack than the WebAssembly build gives it.
- Module scripts and fetch from scripts.
- Indic shaping.
- Pages from the real web.

## Read more

- [Objectives and key results](https://github.com/danbri/factoidal/issues/1245)
- [Source code](https://github.com/danbri/factoidal-core)
- [HTML and CSS in Lean](https://danbri.github.io/factoidal/web/hub/html-webgpu/)

This is experimental, unreviewed code. Do not create public services with it without careful independent expert review.
