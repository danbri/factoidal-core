---
title: "BubblePopJS runs page scripts in the desktop browser"
date: 2026-11-08T22:30:54Z
category: "Scripts"
commit: "98cc094f7"
summary: "BubblePopJS, the JavaScript engine written in Lean, is now the default for page scripts in the native browser. The Hub keeps QuickJS-NG in WasmVM. Settings chooses between them."
demos: ["settings.html", "js-status.html"]
---

Settings has three choices under Page scripts: BubblePopJS, QuickJS-NG and None.
Both engines run the same page objects on Lean's DOM, so a page gives the same DOM
commands on either.

- Web platform tests on the native engine (dom, events, timers, microtasks, event
  loops): BubblePopJS passes 8,844 of 9,729 subtests, QuickJS-NG 8,858.
- Natively, BubblePopJS runs the same scripts 10 to 13 times faster: `fib(24)` takes
  134 ms against 1,773 ms, and the engine is ready for the first page in 120 ms
  against 1,594 ms.

On the Hub, BubblePopJS does not run yet. Its evaluator needs more stack than the
WebAssembly build gives it, so Lean refuses it there and the settings row says so.

Numbers: the design record
[2026-11-08-lean-js-engine.md, section 12](https://github.com/danbri/factoidal-core/blob/main/docs/designissues/2026-11-08-lean-js-engine.md#12-bubblepopjs-in-pages-results)
and [testharness-bubblepop-20261108.json](https://github.com/danbri/factoidal-core/blob/main/tests/browser-wpt/testharness-bubblepop-20261108.json).
