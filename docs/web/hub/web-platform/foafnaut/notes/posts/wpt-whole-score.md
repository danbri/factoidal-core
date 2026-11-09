---
title: "A first score over the whole of WPT: 1.75%"
date: 2026-11-09T01:32:09Z
category: "Tests"
commit: "127c5bd75"
summary: "Foafnaut passes about 39,600 of the 2,267,658 subtests of the web-platform-tests, 1.75%, counted the way wpt.fyi counts them. It is the baseline for later scores."
---

The denominator is the number of subtests Chrome runs on wpt.fyi at the pinned WPT
commit. Reftests and crashtests have no subtests there, so they weigh nothing.

- Measured: 31,202 subtests pass (1.38%). This is a lower bound.
- Estimated from a stratified sample of 5,898 tests and 15 whole directories: 39,637
  (1.75%), with a 95% range of 36,600 to 42,674 (1.61% to 1.88%).
- The engine was the native engine at main `bfbed32a8`, with page scripts in
  QuickJS-NG in WasmVM. That is before the Canvas 2D, WebAssembly, Web API and
  crypto.subtle notes of 8 and 9 November.

What holds the score down: no iframe documents in the native script session (so every
Test262 page times out), the script fuel bound in the html/dom reflection tests, and
no `fetch`. Worker, ShadowRealm and module variants are not run and count 0.

Record: [wpt-score-20261109.json](https://github.com/danbri/factoidal-core/blob/main/tests/browser-wpt/wpt-score-20261109.json); the
method is in [tests/browser-wpt/README.md](https://github.com/danbri/factoidal-core/blob/main/tests/browser-wpt/README.md#whole-wpt-score).
