# Page scripts run by Lean in the Foafnaut engine

Date: 2026-11-08. Author: page-js, a subagent of session depmap-0e.
Related: https://github.com/danbri/factoidal/issues/1244 (WasmVM engine),
https://github.com/danbri/factoidal/issues/1271 (scripted pages refused),
https://github.com/danbri/factoidal/issues/1274 (do not call what an old engine lacks).
Records it joins: `2026-11-07-wasmvm-engine.md` ("QuickJS in WasmVM") and
`2026-11-08-event-loop.md`.

## 1. Result

Page scripts run inside the Foafnaut engine. No host JavaScript engine runs a page
script, natively or on the Hub.

- QuickJS-NG v0.18.0, compiled to WebAssembly (`tools/wasmvm/build-quickjs.sh`), runs in
  WasmVM, the WebAssembly engine written in Lean, inside the engine.
- Each DOM read and change of a script is an import that Lean serves on the page's
  `DOM.Arena`. Each change is a typed command (`WasmVM.Hosts.Dom.Command`).
- The HTML event loop model (`L4Factoidal.EventLoop`) decides every next callback:
  timers and animation frames are its tasks, and the listener order of every dispatch is
  `EventLoop.Dispatch.plan`. Lean decides when a microtask checkpoint runs.
- A host gives clicks and moves time; it lays the page out again only when the DOM
  changed.

## 2. Parts

- `formal/lean4/L4Factoidal/WasmVM/Hosts/Page.lean`: the session. A `Session` is a pure
  value: the WasmVM store (the QuickJS heap), the DOM host state, the event loop state
  and the listeners. `start`, `click`, `advance`, `settle` are functions from a session
  to a session. The WASI clock of the module is the loop's virtual clock (`Date.now()`
  and `performance.now()` read it); nothing else of WASI is granted.
- `formal/lean4/L4Factoidal/WasmVM/Hosts/Dom.lean`: 10 more imports (`node_info`,
  `node_string`, `node_children`, `create_node`, `insert_before`, `remove_child`,
  `replace_child`, `remove_attribute`, `clone_node`, `tree_op`, `node_query`) and their commands, and
  `Command.apply`, the replay of a command. `call_writes_within` still holds for all 23
  imports (the two new imports that write VM memory write only their output buffer).
- `tools/wasmvm/quickjs/prelude.js`: the page objects (build-quickjs.sh puts it into the
  module). `EventTarget`, `Node`, `Element`, `HTMLElement` and its tag classes,
  `CharacterData`, `Text`, `Comment`, `DocumentFragment`, `Document`, `Event`,
  `CustomEvent`, `UIEvent`, `MouseEvent`, `KeyboardEvent`, `ErrorEvent`,
  `AbortController`/`AbortSignal`, `DOMException`, `NodeList`, `HTMLCollection`,
  `DOMTokenList`, a selector subset, event handler attributes (IDL and content), and
  "report an exception" as an `ErrorEvent` at the window. The functions stay in the
  prelude by number; Lean keeps the listeners, timers and frames.
- `tools/wasmvm/quickjs/qjs_wasmvm_entry.c`: new exports `qjs_dispatch`, `qjs_run_job`,
  `qjs_page_mode`, `qjs_page`.
- `labs/demos/foafnaut/WebScripts.lean`: the engine op `scriptSession` (actions `info`,
  `load`, `start`, `click`, `advance`, `settle`, `turn`, `close`). The guest module comes
  through the font byte call with the family `guest:quickjs`, so there is no new export.
- `WebDocument.lean`: the op `nodeAt` (the node under a window point, from the layout
  boxes), and the dispatch of `scriptSession`.
- `WebRenderScript.lean`: the render replays every command kind (`commandJson`,
  `Command.apply`).
- Hosts: `run_html.ts` (native window), `native_html_document.ts`, the engine worker,
  and the Hub worker `docs/web/hub/foafnaut/browser-worker.mjs`.
- Runner: `tests/browser-wpt/testharness-run.ts`, with this repository's
  `tests/browser-wpt/testharnessreport.js`, over the pinned WPT files in
  `third_party/testing/wpt-scripting/`.

## 3. How a page runs

`start`:

1. The page is parsed as `WebDocument.prepareDOM` parses it, so node numbers agree with
   the render's replay.
2. The session is a copy of a base instance: `_initialize`, `qjs_new` (the prelude) and
   page mode ran once, on an empty document, when the module was loaded. The prelude
   costs about 55 M instructions; the copy costs one copy of the module memory.
3. `qjs_page 2` (content event handler attributes), the URL, then each classic script in
   document order with `document.currentScript` set, each followed by a microtask
   checkpoint (HTML "clean up after running script").
4. `DOMContentLoaded` at the document, then the `load` event at the window as a task of
   the DOM manipulation source, and the tasks due at time 0.

A click is a task of the user interaction source with an event. The click goes to the
node `nodeAt` found, or to its nearest element. A dispatch, from Lean or from
`dispatchEvent`, asks Lean for its plan: the path from the arena's parents (with the
window after the document), and `Dispatch.plan` over the listeners Lean keeps. The
prelude runs the plan in order, with `stopPropagation` as `Dispatch.afterStop` (the rest
of the same invoke), and skips a listener removed during the dispatch.

`advance(ms)` and `settle(budget)` run the loop: `EventLoop.State.step` gives the next
task (a timer callback, an event); when none is runnable, `advanceTo` moves the clock to
the next timer or animation frame time (every 16 ms of virtual time while a frame is
requested), and the timers due then become tasks. After each task Lean runs the
microtask checkpoint with `qjs_run_job`.

## 4. Cost

The contract: a turn's answer says `changed` exactly when the command list grew. A host
renders again only then. The render request carries the command list, which is a field of
the layout key (`WebDocument.layoutFields`), so a render with the same list reuses the
kept layout (`WebDocument.lookupLayout_eq`). No DOM change, no layout. The scripted-page
test checks that a turn with no change has no commands. A Lean theorem of the contract
(the command list only grows, so equal length means equal list) is not written yet; the
"perf-theorems" work proves the frame contracts.

Measured on the owner's Mac, native engine library (2026-11-08):

- Module load once (decode, validate, `_initialize`, `qjs_new` and the prelude): about
  1.1 s.
- Page start on the base copy: 2 to 12 ms for a small page; a WPT test page (with
  testharness.js, 5200 lines) about 60 M instructions, 0.5 s.
- A click turn: 150 000 to 220 000 instructions, about 2 ms.

## 5. Limits

- Scripts inserted by scripts are not run; `src` scripts come only from the host
  (`resources`), as stylesheets do. Module scripts are not run.
- Promise jobs are QuickJS's own queue (one queue, in order, as HTML's microtask queue);
  Lean decides when a checkpoint runs, not the order inside it. A host click's listeners
  get one checkpoint after the whole dispatch, not one after each listener.
- No layout reads from script (`offsetWidth` is 0); `style` is the `style` attribute.
- No `innerHTML` setter, no `Range`, no `TreeWalker`.
- Iframes: only in the WPT bench (`wasmvm-bench page`, `Limits.frames`). Markup iframes:
  the bench parses each `src` document (XML for `.xml`, `.xhtml` and `.svg`, else HTML;
  `about:blank` with no `src`) and `Hosts.Page.start` grafts it into the page's arena
  (`Dom.graft`). An iframe a script connects to a document with a browsing context gets an
  `about:blank` document at once (`Hosts.Dom.connectFrames`) and a navigation to its `src`,
  which `settle` hands back to the embedder (`Session.frameLoads`); the bench answers with
  `Session.attachFrame`, which queues the `load` event. Setting `src` navigates again.
  `node_info` 11 gives an iframe's document. The frames share the
  page's script realm: a frame's `window` is a view of the page's window with its own
  `document`, so a frame's constructors are the page's. The engine (`scriptSession`)
  passes no frames: a frame's nodes are not commands, so the layout replay of the
  command list would not see them.
- A page may make at most 4096 commands (the bound of `WebRenderScript`); the WPT runner
  allows 200 000 because it lays nothing out.

## 6. WPT

`deno run -A tests/browser-wpt/testharness-run.ts --out FILE` runs the testharness.js
tests of `html/webappapis/timers`, `html/webappapis/microtask-queuing`, `dom/events`,
`dom/nodes` and `html/webappapis/scripting/event-loops` at wpt ce5ca396. Counts: the
baseline `tests/browser-wpt/testharness-20261108.json`.

Namespaces (2026-11-08): `Dom.validateAndExtract` (DOM §1.4) for `createElementNS`,
`createAttributeNS` and `setAttributeNS`; `getAttributeNS`, `removeAttributeNS`,
`lookupNamespaceURI` and `lookupPrefix` (DOM §4.4 "locate a namespace") are Lean's. The
namespaced attribute imports pass "namespace U+0000 name" in the name argument (no valid
name contains U+0000); the import `node_query` (string in, string out) answers the
lookups and the namespaced attribute list. `Attr` objects name an attribute of the arena
(element, namespace, local name); a removed or new `Attr` keeps its own value. A guest
built with `node_query` needs an engine that serves it.

Selectors (2026-11-08): `querySelector`, `querySelectorAll`, `matches` and `closest` are
Lean's (`DOM.Selectors`, `node_query` 6 to 9): CSS identifier and string tokens with
escapes, namespace prefixes, attribute selectors with flags and HTML's case-insensitive
attribute values, the structural pseudo-classes with `An+B [of S]`, `:not`, `:is`,
`:where`, `:scope`, `:lang`, `:link`, `:checked`, `:disabled`, `:enabled`. User-state
pseudo-classes match nothing; the four legacy pseudo-elements never match. The JavaScript
selector engine of the prelude is gone.
