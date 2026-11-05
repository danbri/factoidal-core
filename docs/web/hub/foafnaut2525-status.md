---
title: foafnaut2525 project status
description: Where the Lean web rendering engine stands, with the score of each test suite. The engine renders this note itself.
layout: hub.njk
---

# foafnaut2525 project status

5 November 2026. The engine that this note describes renders it too: choose Project status in the Lean HTML page below. The rendering is plain ASCII text with no script.

foafnaut2525 is a web rendering engine written in Lean. It aims to become a browser. It is not the FOAF social network application that it is named after.

## Where it is

- The engine parses HTML, computes CSS, lays out text and boxes, and draws with WebGPU.
- It runs in a web page, and in its own macOS window.
- Page scripts run in a local development bundle. Real sites mostly do not load yet.
- The rendered note uses an ASCII bitmap font. Real fonts are the next large step.
- The engine has no scrolling yet. A long page needs a tall canvas.

## This week

- Frame time fell from 2,278 ms to 209 ms, for the same image. Each screen tile now has its own list of primitives.
- The native window draws. It lays pages out again during a window drag.
- The Lean text shaper and the font safety policy are on main.
- Every frame now writes a timing record, and a repeatable sweep measures it with no person.

## Measured scores

- HTML tree construction: 1,963 pass, 10 fail (out of 1,973).
- HTML tokenizer: 7,047 pass, 6 fail (out of 7,053).
- WPT SVG and HTML images: 29 match, 21 mismatch, 264 unsupported, 30 rejected, 257 unavailable (out of 601).
- WPT scripted documents: 0 complete passes (out of 784); 103 assertions pass, 1,342 fail.
- SVG Tiny 1.2: 0 admitted (out of 496).
- HarfBuzz 15.0.0 shaping suite: 4,175 pass, 533 fail, 169 refused (out of 4,877 applicable).

These suites are separate. Their numbers do not add up to one browser score. Most were measured on 3 or 4 November.

## What comes next

- A named release every day: one to three, never four.
- Real fonts, with outlines and shaping in Lean.
- Faster layout. It is now the largest part of a frame. This note takes about 2 seconds to lay out in the browser, and 63 ms to draw.
- An address bar, and pages from the real web.

## Read more

- [Objectives and key results](https://github.com/danbri/factoidal/issues/1245)
- [Source code](https://github.com/danbri/factoidal-core)
- [HTML and CSS in Lean](https://danbri.github.io/factoidal/web/hub/html-webgpu/)

This is experimental, unreviewed code. Do not create public services with it without careful independent expert review.
