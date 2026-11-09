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

Since 2026-11-08 evening a second engine runs the same pages: BubblePopJS, the
JavaScript engine written in Lean (`scriptSession` with `engine:"bubblepop"`,
`WasmVM/Hosts/LeanJS.lean`; record `2026-11-08-lean-js-engine.md`, sections 11 and 12). It
runs this prelude with the same imports, commands and event loop, and is the default in
native hosts; the Hub keeps QuickJS-NG. The setting is on the settings page.

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
the next timer, and the timers due then become tasks. After each task Lean runs the
microtask checkpoint with `qjs_run_job`.

One advance runs at most one animation frame batch, as a browser runs "update the
rendering" at most once per rendering opportunity: at the last 16 ms frame time the
advance reaches (`EventLoop.frameSlot`), never at the time of the frame before. Timers
due before that time run first, in order; timers due after it run after it. A host
that fell behind (a slow turn) gets one frame with the latest time, not every missed
frame back to back. The loop is `EventLoop.Driver.advanceGo`, and
`Driver.advanceGo_frames` proves the bound. Hosts pace frames: the Hub worker and
`run_html.ts` start no turn while a frame is asked for or being drawn, so each presented
frame has at most one turn before it.

### Pointer input

A host asks `nodeAt` for the window point. Lean takes the smallest layout box there; when
that box is an embedded `svg` (or inside one), the target is the shape under the point
(`WebHit.svgTarget`): each SVG primitive keeps the source path of the element that
painted it (`NativeSVG.Primitive.element`; a `use` instance is its `use` element), and
`NativeSVG.Scene.hitTestWith` takes the topmost primitive at the point in painter order,
with the sampler's coverage, clips and transforms, under the primitive's
`pointer-events` (SVG 2 §15.6: `none`, `visiblePainted` (initial), `visibleFill`,
`visibleStroke`, `visible`, `painted`, `fill`, `stroke`, `all`). The answer has the node
and the event's coordinates: `clientX/Y` (in the page's viewport), `pageX/Y` (plus the
scroll) and `offsetX/Y` (from the target's box; an SVG shape's box is its outer `svg`'s).

The host passes that answer to `scriptSession pointer` with `kind` (down, move, up,
cancel), `button`, `buttons` and `pointerType`. Lean (`Page.Session.pointer`) dispatches
`pointerdown` then `mousedown`; `pointerup`, `mouseup`, then `click` at the common
ancestor of the press and release targets; `pointermove` and `mousemove`;
`pointercancel` (a press that scrolled). A canceled `pointerdown` drops the compatibility
mouse events of its press, not the click. At most one move is dispatched in a frame (16
ms of the clock): a later move in the same frame replaces the one that waits, which is
dispatched at the next turn of a later frame (`nextWake` says when). The event data
reaches the prelude through `node_query` op 16 while Lean dispatches: no change to the
guest's exports. A move or a press changes no DOM by itself, so no layout.

### Layout reads

`innerWidth`/`innerHeight` are the viewport the host gives at `start` (`width`, `height`
less the full chrome of `shell`) and at `resize` (which also dispatches `resize` at the
window). `clientWidth/Height/Left/Top`, `offsetWidth/Height/Left/Top`,
`getBoundingClientRect`, `getClientRects` and SVG `getBBox` ask Lean (`node_query` ops
17 and 18). Lean lays the arena out as a render with the session's `layout` request
(`WebDocument.measure`, `layOutDOM`: no parse) when a read first asks, and keeps that
layout until a DOM write or a resize, as a browser forces one layout for a read after
writes. Each turn's `layouts` counts the layouts made for reads. An SVG element inside
an `svg` has no CSS box: its client box is zero and its rectangle is the bounds of what
it painted (`WebHit.elementBounds`); `getBBox` is in the element's user space, exact for
shapes and groups of shapes (a path's bounds are those of its control points).

### The script clock

The event loop's clock is virtual and moves by rule, so runs replay. Script time is the
instructions a script ran at `instructionsPerMs` (100 000 by default, a stated rate near
QuickJS on the native and Wasm engines; `start` may give another), in whole milliseconds
from a mark (`Page.ScriptClock`). `performance.now()` and `Date.now()` read the later of
the loop's clock and script time. The loop's clock moves up to script time before a timer
or an animation frame is requested and after each run of the module, so a timer set after
a long script is due its delay after the time it was set at. A host moving the clock past
script time moves the mark. Readings never go back (`ScriptClock.read_monotone`,
`read_read`) and the loop's clock never goes back (`sync_ge`); a page that runs fewer than
`instructionsPerMs` instructions between moves of the clock sees the clock alone
(`ms_mark`). The WPT runner gives a rate of a trillion a millisecond (script time as good
as off): testharness.js times a file out after 10 s of browser time, and this engine runs
many more instructions than a browser for the same work.

## 4. Cost

The contract: a turn's answer says `changed` exactly when the turn recorded a DOM change
(`Hosts.Dom.State.changes` grew). A host renders again only then. The render request
carries the command list, which is a field of the layout key (`WebDocument.layoutFields`),
so a render with the same list reuses the kept layout (`WebDocument.lookupLayout_eq`). No
DOM change, no layout. Writing the value an attribute or a text node already has records
nothing. The scripted-page test checks that a turn with no change has no commands.

The command list is compacted (`Hosts.Dom.addCommand`): a write of an attribute, or of
the data of a text node, takes the place of the last write of the same one, when no
command between them reads it (`cloneNode` and `normalize` read). The replay gives the
same arena, with attributes in the order of their first write;
`WasmVM.Tests.DomCommands` checks it against the replay of every command. So the list,
and the render request, are bounded by the DOM, not by the number of changes: an
animation of twelve SVG transforms keeps twelve commands however long it runs.

Measured on the owner's Mac, native engine library (2026-11-08):

- Module load once (decode, validate, `_initialize`, `qjs_new` and the prelude): about
  1.1 s.
- Page start on the base copy: 2 to 12 ms for a small page; a WPT test page (with
  testharness.js, 5200 lines) about 60 M instructions, 0.5 s.
- A click turn: 150 000 to 220 000 instructions, about 2 ms.
- An animation frame of `pages/timers-and-clicks.html` (twelve `transform` writes): about
  0.40 M instructions natively. On the Hub (headless Chrome on the same Mac, local engine
  build): a turn of 40 to 50 ms (WasmVM runs about 8 to 10 M instructions a second
  there), a layout of 20 to 25 ms and a draw of about 25 ms, so 9 to 11 frames a second
  while the dots move. A `setAttribute` costs about 17 000 instructions in the guest, a
  host read such as `nodeType` about 6 000: the guest's path to an import is the next
  cost to cut.

## 5. Limits

- Scripts inserted by scripts are not run; `src` scripts come only from the host
  (`resources`), as stylesheets do. Module scripts are not run.
- Promise jobs are QuickJS's own queue (one queue, in order, as HTML's microtask queue);
  Lean decides when a checkpoint runs, not the order inside it. A host click's listeners
  get one checkpoint after the whole dispatch, not one after each listener.
- `style` is the `style` attribute; `getComputedStyle` returns it too. `scrollTop` is 0.
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
- A page may keep at most 4096 commands after compaction (the bound of
  `WebRenderScript`); the WPT runner allows 200 000 because it lays nothing out.

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

DOMParser (2026-11-08): `parseFromString` makes the document with Lean's HTML parser
(`text/html`) or namespace-aware XML parser (the four XML types), grafted into the arena
(`create_node` kinds 11 and 12, so the command list replays it). An XML source that is not
namespace-well-formed gives a document whose element is `parsererror` with the parser's
message.

Activation (2026-11-08): the dispatch of a `click` MouseEvent asks Lean for its activation
target (`DOM.Forms.activationTarget`, `node_query` 10), runs the legacy-pre-activation
behaviour of a checkbox or radio button before the listeners, and after them either the
legacy-canceled-activation or the activation behaviour: `input` and `change` for a
connected checkbox or radio button, form submission (the `submit` event; no navigation)
and reset, a fragment navigation of `a` and `area` (the URL is parsed by Lean's WHATWG URL
parser, `node_query` 12; a `hashchange` task follows), the labeled control's `click()` for
a `label`, and the `open` toggle of `details` for its summary. Checkedness and its dirty
flag are arena state (`Node.checkedness`, commands `setChecked` and `resetForm`).
`click()` does nothing on a disabled form control. Event handler content attributes of
cloned and imported subtrees are compiled as those of the page are; on `body` and
`frameset` the window-reflecting handlers are the window's.

## 7. Web APIs over Lean

The everyday web APIs that are pure algorithms are computed by Lean
(`formal/lean4/L4Factoidal/WasmVM/Hosts/WebApi.lean`), through one import,
`foafnaut_dom.web_api(op, flags, args, len, out, cap)`: the arguments are one byte block
(a count, then each argument as a length and its bytes), the answer is bytes. One call is
one whole operation (a `decode` of 1 MiB is one call), and an answer that does not fit the
guest's buffer waits in the host for op 0, so a stateful operation runs once. The QuickJS
guest's native is `n.api(op, flags, bytes, ...args)`; BubblePopJS serves the same native
(`Hosts.LeanJS` native 24) through `Page.serveExtra`, with ArrayBuffer answers
(`JS.HostAns.bytes`).

| API | Lean | Ops |
|---|---|---|
| `TextDecoder` (all 40 encodings, `fatal`, `ignoreBOM`, `stream`), `TextEncoder` (`encode`, `encodeInto`) | `WHATWG.Encoding.Core` (existing), `.Api` (bytes out, a UTF-8 fast path) | 2-5 |
| `URL` (every attribute and setter, `canParse`, `parse`), `URLSearchParams` | `WHATWG.URL.Parser` (existing) | 10-13 |
| `document.characterSet`; `a` and `area` URL attributes, parsed with the document's encoding | `WebApi.documentEncoding`, `parseWith` | 9, 10 |
| `atob`, `btoa` | `WHATWG.Base64` (forgiving-base64) | 20, 21 |
| `crypto.getRandomValues`, `randomUUID` | `Crypto.WebCrypto` (HMAC_DRBG over HMAC-SHA-256) | 30, 31 |
| `crypto.subtle`: `digest`; HMAC, HKDF, PBKDF2, ECDSA and ECDH on P-256, Ed25519, X25519, ChaCha20-Poly1305 (keys behind handles) | `Crypto.WebCryptoKeys` over HACL* (`Crypto.WebHacl`); record `2026-11-09-hacl-web-crypto.md` | 32, 40-42 |

State in `Page.Host.web`: the decoders of `TextDecoder`s in the middle of a stream (by the
number the page gave them; at most 4096), the waiting answer, and the generator. The
generator is seeded per session by the embedder (`Page.Limits.entropy`: `WebScripts`
gives 32 bytes of `IO.getRandomBytes`, the operating system's natively and the browser's
`crypto.getRandomValues` under Emscripten, then the session number). With no entropy,
`getRandomValues` and `randomUUID` are absent.

prelude.js (section "basics") does WebIDL conversion, object shapes and promises only.
Each API is a getter on the global object that probes `n.api` once on first use; an
engine without the op leaves the API undefined. Nothing runs at page start.
`crypto.subtle` promises are settled by a task of Lean's event loop. Since 2026-11-09
the engine links HACL* (record `2026-11-09-hacl-web-crypto.md`), with RSA for imported
keys. Off natively, because HACL* has no such primitive: AES, P-384, P-521, Ed448, X448
(NotSupportedError). On the Hub the browser's crypto.subtle does the primitives under Lean's
rules (host mode), which adds AES, P-384 and P-521 there.

`structuredClone` (HTML §2.7) is glue that walks JavaScript values, step for step:
primitives, the wrapper objects, Date, RegExp, ArrayBuffer (and resizable ones), views,
Map, Set, the native errors, DOMException, arrays and plain objects, with the memory map
for repeated and cyclic references, DataCloneError for functions, symbols, platform
objects and objects with internal slots, and `transfer`. `performance.mark`, `measure`
and the entry list are glue over QuickJS-NG's `performance.now`, which reads Lean's
script clock through WASI.

Theorems: `decodeLoop_replacement_ne_error` (the decoder loop never ends in error in
mode "replacement"), `xUserDefined_roundTrip`, `singleByte_roundTrip` and
`reverseIndex_getElem?` (`SingleByteTheorems.lean`), with `#guard`s that every single-byte
index is a bijection on its used pointers; the existing `utf8_decode_encodeList` and
`utf8DecodeWithoutBOMOrFail_toUTF8` (decode of encode is the identity on scalar values).
The UTF-8 fast path of `decodeBytes` is checked against `decodeBytesRef` by `#guard`s
on each of its conditions.

Pages are decoded by Lean (`web_document_decode_call_bin`, `WebDocument.decodeBin` over
`WHATWG.Encoding.Sniff`): the native loader, the Hub worker and the WPT runner pass a
page's bytes and its `Content-Type`, and `document.characterSet` is the encoding Lean
chose (passed to the session as `encoding`). A page that is UTF-8 with no other
declaration takes the fast path (one validation and one copy: 7.2 ms for 1 MB, against
4.9 ms for Deno's TextDecoder); a 1 MB Shift_JIS page decodes in 66 ms. Subresources
(scripts, stylesheets, XSLT) are read as UTF-8.
An undeclared page whose bytes are UTF-8 is read as UTF-8 (like Firefox's detector);
WPT `encoding/sniffing.html`, which expects windows-1252 there, is an expected difference.

Measured (native engine, 2026-11-09; QuickJS-NG in WasmVM unless named): the guest's
module load (the prelude) 1,261 → 1,504 ms with the prelude as source, once for each
engine; with the prelude compiled to QuickJS-NG bytecode at guest build time
(`prelude_bytecode.c`, `JS_ReadObject`, no source text kept) 1,342 → 501 ms on the same
machine and load (BubblePopJS makes its realm, the prelude parsed and run, once for each
engine: about 165 ms of its first page start); a page start 5.97 → 6.03
ms; a Timers and clicks frame 0.67 → 0.65 ms mean. TextDecoder on 1 MiB: UTF-8 795 ms
(almost all of it QuickJS making its string inside WasmVM; BubblePopJS takes the Lean
string at no cost), Shift_JIS 1,218 ms (BubblePopJS 115 ms). SHA-256 in pure Lean is
about 13 MB/s here (digest of 1 MiB: 76 ms), so PBKDF2 at 100,000 iterations takes
about 9 s (1,000 iterations: 93 ms), as a task.
