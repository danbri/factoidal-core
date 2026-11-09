# Shadow DOM, frames and the sandbox, decided in Lean

Date: 2026-11-08. Author: shadowframes, a subagent of session depmap-0e.
Records it joins: `2026-11-01-dom-arena.md` (the DOM arena), `2026-11-08-page-scripts.md`
(page scripts), `2026-11-08-event-loop.md` (dispatch order), `2026-11-08-lean-js-engine.md`
(BubblePopJS).

## 1. Result

- Shadow trees are part of the Lean DOM arena. `attachShadow`, `shadowRoot`, `slot`
  elements with named and default slots, manual slot assignment (`slot.assign`),
  `assignedNodes`/`assignedElements` (flattened or not), `assignedSlot`, `slotchange`,
  `getRootNode({composed})`, `isConnected` and clonable shadow roots are Lean algorithms
  (`L4Factoidal/DOM/Shadow.lean`); prelude.js only shapes the calls.
- The HTML parser makes declarative shadow roots (`<template shadowrootmode>`,
  `DOM.OfHtml.declarativeShadow`). `DOMParser` does not.
- Events go through shadow trees: the event path follows slots and shadow roots, a
  shadow root stops a non-composed event, each listener sees the target retargeted
  against its own node (DOM §2.5), a host is at the target for events from its shadow tree
  (`EventLoop.Dispatch.planAt`), and `composedPath()` leaves out what a closed shadow root
  hides from the listener (`DOM.Dom.hiddenFrom`).
- Layout and style: a page with a shadow host is laid out on its flat tree
  (`DOM.Dom.flat`, CSS Scoping 1 §2.2). Each style rule matches in its own tree: a shadow
  tree's `<style>` rules match only in that tree, `:host` and `:host(...)` match its host,
  `::slotted(...)` matches the elements assigned to its slots; in the cascade a shadow
  tree's normal declarations lose to the document's and its important ones win
  (`Rendering.CSS.TreeScope`, `selectorMatchesIn`).
- Frames: the origin of each frame's document and its sandboxing flags are decided by
  `L4Factoidal/HTML/Frames.lean`. `contentDocument` answers only a document of the page's
  origin; a frame with `sandbox` and no `allow-same-origin` has a fresh opaque origin, so
  neither side reaches the other's document; its `contentWindow` is a cross-origin window
  with `postMessage` and `location` only. A form of a frame with the sandboxed forms flag
  does not submit.
- A sandboxed frame with `allow-scripts` (and no `allow-same-origin`) and a `srcdoc` gets
  a script session of its own (`HTML/FrameSessions.lean`, `WebScripts.pumpFrames`): its own
  arena, its own heap (a WasmVM instance of QuickJS-NG, or a BubblePopJS realm), its own
  event loop and smaller budgets. The page and the frame talk only by `postMessage`;
  messages cross as strings. Without `allow-scripts` no session is made.
- Frame documents in the native script session (`frames:true`): every connected `iframe`
  gets a browsing context with `about:blank` at once; Lean loads `srcdoc`; a host that sets
  `navigations:true` in `start` gets `navigations` in each turn and answers each with the
  action `frame` (the WPT runner does, from the WPT copy, with Lean's document decoding). A
  frame document is a command (`Command.frameDocument`), so a render's replay over the
  parsed page keeps the node numbers. A same-origin frame's scripts run in the page's realm,
  with `document` the frame's document while they run, and with a window target of their
  own for `load` and `error`; so `contentDocument`, `contentWindow.document` and functions
  a frame defines (`contentWindow.run`) work. The window's `load` event waits for frames that
  are still loading (`Hosts.Dom.State.loadWaits`). A sandboxed frame's scripts never run in
  the page's realm (`Hosts.Dom.frameScriptsInRealm`).
- `window.postMessage` with the target origin check (`HTML.Frames.postMessageDelivers`)
  delivers a `MessageEvent` as a task; `MessageChannel` and `MessagePort` work in one realm.

## 2. The model

A shadow root is a DocumentFragment with a `ShadowInit` (mode, delegates focus, slot
assignment, clonable, serializable, declarative). Its `host` field is its host, as the
template contents of a `template` element have their element as host; the host's `shadow`
field names the shadow root. It is not a child of its host, so tree order, selectors of
the light tree and the mutation algorithms never enter it, as DOM requires. No `NodeType`
changed; the arena keeps one node per index.

Slot assignment is computed from the tree when asked (`findSlot`, `findSlottables`,
`findFlattenedSlottables`). DOM runs "assign slottables" after every change, so the
assigned nodes always equal what "find slottables" answers on the current tree; computing
on demand gives the same answers with no state to keep in step. `slotchange` compares the
assignments of all slots once per microtask (`node_query` 33, `DOM.Dom.slotChanges`),
and only after a shadow root has been seen by the page's scripts.

The flat tree is an arena with the same node numbers: each node's children are its flat
children, and a slot of a shadow tree is replaced by what it shows (as `display:
contents`, which is a slot's default). An arena with no shadow host is answered
unchanged.

## 3. Theorems

- `DOM.Dom.flat_eq_of_noShadow`, `flatChildren_eq_kids`: with no shadow tree the flat tree
  is the tree, so pages without shadow DOM lay out as before.
- `DOM.Dom.shadowIncludingRoot_eq_root`: with no shadow root, the shadow-including root
  is the root.
- `DOM.Dom.retarget_visible`, `retarget_closed`: retargeting never answers a node inside
  a closed shadow root to a listener outside it.
- `EventLoop.Dispatch.planAt_plan`: with no shadow tree the new plan is the old one.
- `Hosts.Dom.shadowInitOfFlags_flags`: the shadow state survives its bit encoding.
- `HTML.Frames.scripts_need_allow`, `sandboxed_no_access`, `flags_inherit`,
  `postMessage_star`, `postMessage_mismatch`.
- `Hosts.Dom.sessionFrames_scripts`: every frame that gets a session may run scripts.
- `HTML.FrameSessions.exchange_frame`, `exchange_parent`, `exchange_isolated`: after an
  exchange each session is a function of its own state and of the message strings
  addressed to it, so no session reads or writes another session's heap.

## 4. Codes

`node_info` 20-29 (shadow root, host, shadow state, assigned slot, composed root,
connected, raw shadow root, arena has a shadow host, root, iframe sandbox bits); `node_query`
30 (assigned nodes), 31 (composedPath), 32 (postMessage origin check), 33 (slot changes),
34 (a message to another session); `tree_op` 20 (attachShadow), 22 and 23 (manual slot
assignment); `dispatch_plan` flags 1 bubbles, 2 composed, 4 the shadow format (a fifth
number per listener call: its retargeted target). Commands `attachShadow`, `assignSlot`.

## 5. Not done, and what it would take

- Drawing a frame's document. A frame's document is not laid out yet. It needs the
  layout's embedding to answer glyph runs as well as paint nodes, a remap of the frame's
  node numbers in boxes and links, a clip to the content box, its own scroll, and input
  routed by the hit test. The band and layer caches would then keep an idle frame's
  layer.
- Same-origin frames share the page's script realm: a frame's globals are the page's, and
  its `location` is the page's. Realms of their own need cross-realm WindowProxy objects
  for synchronous same-origin access (one WasmVM instance or BubblePopJS heap per frame, and
  calls between them served by Lean).
- A frame document arrives as text: the host decodes it (the WPT runner through Lean's
  `decodeDocument`); `document.characterSet` of a frame is the page's.
- `customElements`: a registry in Lean (names, the definition's callbacks by number) and
  the reactions queue run by the prelude; the "is" value and upgrades at insertion. The
  shadow-root parts (valid custom element names) are here already.
- Named access on the window (an element's id as a window property) as a proxy in the
  window's prototype chain works on QuickJS-NG but breaks lookups through the chain on
  BubblePopJS (its proxies are not consulted there), so it is not in; many shadow-dom tests
  name elements this way.
- `relatedTarget` retargeting, `delegatesFocus` focus steps, `:host-context()`,
  `::part()`, inheritance from a slot (a slot is not a box here), and `getHTML()`.
- Structured clone across sessions uses JSON until the Lean clone of the basics work is
  exposed as bytes.
