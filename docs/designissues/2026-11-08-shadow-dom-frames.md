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

## 2a. Shadow trees and the fast cascade

The cascade of the real-site work (`2026-11-09-real-site-layout-speed.md`) is
keys, buckets and `computedFrom`. A shadow page uses the same pieces:

- `CSS.computeFor treeScope` sends a page with no shadow host to `computeAll`, unchanged
  (`computeFor_none`). `:host` and `::slotted()` selectors go in no bucket of `RuleIndex`
  (`Bucket.never`), so they cost a page with no shadow tree nothing, and a selector that
  names them never matches there.
- A page with a shadow host uses `computeAllIn`: the key table is of the node tree,
  and `ScopedIndex` holds one set of buckets per tree (the rules of that tree's
  `style` elements) with the user agent's rules in a set of their own. An element tries
  the user agent's buckets, its own tree's, the `:host` rules of the tree it hosts (only
  on that host) and the `::slotted()` rules of the tree its parent hosts (only on the
  children of a host). Numbers index one entry array, so the merged list keeps sheet order.
  Each slot lookup is made only for a rule whose `::slotted()` compound matched.
- The cascade key keeps its length: the context of CSS Cascade 4 shares a position
  with the origin (`origin*2 + context`), so the inline-style position that the SVG
  paint boundary reads did not move.

## 3. Theorems

- `CSS.computeFor_none`: with no shadow tree the cascade is `computeAll`, the same term.
- `CSS.selectorMatchesK_admits` (statement unchanged): a selector that matches an element has the
  element in its bucket, with `:host` and `::slotted()` outside every bucket of `RuleIndex`.
- `CSS.selectorMatchesInK_admits`: a selector of tree `scope` that matches element `id` has it
  where `ScopedIndex` looks: under `::slotted(c)` in the bucket of `c` with a slot of that
  tree assigned, under `:host` as that tree's host, otherwise in the bucket of the rightmost
  compound and in that tree.
- `CSS.computeAllIn_eq_linear`: wherever `ScopedIndex` gives the plain loop's matches
  (`matchedRulesIn`, every rule tried in order), `computeAllIn` gives `computeAllInLinear`.
  The premise is checked on every node of shadow test pages (`CascadeTests.lean`, with
  `:host`, `:host()`, `::slotted()`, nested shadow roots and pointer states), not proved,
  as for the unscoped buckets.
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
- `HTML.Frames.frameFlags_narrows`, `frameOf_narrows` (2026-11-11): sandbox flags only
  narrow. `SandboxFlags.Narrows a b` says `b` sets every flag `a` sets (`a ∪ b = b`); a
  frame's flags narrow its parent document's whatever its `sandbox` attribute says, and
  `Narrows` is reflexive and transitive, so it holds down any chain of nested frames.
  `nested_sandboxed_opaque`, `nested_no_scripts`: a frame in a frame with the sandboxed
  origin flag has an opaque origin, and one in a frame without scripts runs none, whatever
  its own `allow-same-origin` or `allow-scripts`.
- `HTML.FrameSessions.exchange_out`, `exchange_data` (2026-11-11): each message out of an
  exchange is one a session posted, with its data and origin unchanged; the page's go to
  the frame they name, and a frame's go only to the page, as from the frame's own element,
  whatever address the frame wrote. A message is a record of strings, so what crosses is
  the serialized clone (`JSON.stringify(structuredClone(x))` in the sender's realm), never
  a reference into a heap; the origin is set by Lean (`Page.postToFrame`), not by the
  sender's script.

### 3a. Isolation: what is proved, what is tested, what is open (2026-11-11)

Proved, on the decisions (`HTML.Frames`, `HTML.FrameSessions`, `Hosts.Dom`): a sandboxed
frame without `allow-same-origin` has a fresh opaque origin and neither side's access check
passes (`sandboxed_no_access`); without `allow-scripts` no script runs and no session is
made (`scripts_need_allow`, `sessionFrames_scripts`); flags only narrow, down nested frames
too (above); a frame's scripts run in the page's realm only for a same-origin frame
(`frameScriptsInRealm_sameOrigin`); sessions meet only through message records
(`exchange_*`).

Tested, not proved: that every host path that hands out a frame's document asks
`frameAccessible` (`node_info` 11 does, by its definition; `contentWindow` in prelude.js
goes through it); that the page's scripts cannot name a node of a same-arena frame
document by number (node numbers reach a script only through the natives' answers); the
per-frame entropy (`WebScripts.frameEntropyOf`: fresh machine bytes each turn, suffix
`frame:<session>:<element>`, never a worker's suffix, and none when the page has none).

Open:
- Storage: the engine has no `localStorage`, `sessionStorage`, IndexedDB or cookies, so a
  frame reaches no storage of its parent's because there is none. When storage comes it
  must be keyed by `Frame.origin` (an opaque origin gets a fresh, empty store), with a
  theorem like `sandboxed_no_access` for the store lookup.
- Host-level narrowing: `frameFor` uses a frame kept when its browsing context was made
  (`frameInfo`) before computing one; that the kept frame's flags narrow its container's
  is an invariant of `connectFrames`, not proved.
- Opaque origin identity is `10^9 + element` in each arena. Within one arena two elements
  never share one; a frame's own session numbers its elements from 0, so a frame in a
  sandboxed frame (which gets no browsing context there: `frames := false`) could share
  the number of its parent frame's origin. Harmless while frames in frame sessions get no
  context; to fix before they do (a per-session counter).
- Same-origin frames share the page's realm (section 5), as before; only the sandboxed
  ones are separate sessions. The AOT path (the Hub) makes no frame sessions: a sandboxed
  frame's scripts do not run there at all, which is safe and incomplete.
- The structured clone across sessions is JSON (section 5): cyclic data, Maps, Dates and
  ArrayBuffers do not survive; a failure to clone throws in the sender, as it should.

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
- Named access on the window (an element's id as a window property) is a proxy in the
  window's prototype chain. It is on only where property lookups consult such a proxy
  (probed once): QuickJS-NG yes, BubblePopJS not yet (its lookups skip proxies in a
  prototype chain).
- `::slotted()` matches the elements directly assigned to a slot, not those assigned through
  a chain of nested slots ("after flattening"). A style attribute of an element in a shadow tree
  is treated as outside the tree for the cascade context; both are edge cases of the port.
- `relatedTarget` retargeting, `delegatesFocus` focus steps, `:host-context()`,
  `::part()`, inheritance from a slot (a slot is not a box here), and `getHTML()`.
- Structured clone across sessions uses JSON until the Lean clone of the basics work is
  exposed as bytes.

## 6. Merge with main of 2026-11-11

Main had landed frame documents for 0.35.0 (`srcdocLoads`, the `frame` action, the
embedder's navigations), the engine state as a value passed through the C ABI (issue 390)
and dedicated workers. The merge keeps main's frame loading and adds the sandbox, frame
sessions and shadow trees on it: one frame implementation. Changes the merge needed:

- Frame entropy comes from the machine (`WebWasm.Machine.randomBytes`), as workers' does,
  not from an `@[implemented_by]` of its own, so the lab keeps 3 `unsafe` and 3
  `implemented_by` (`LabHygiene.lab_ratchet`). One draw a turn (`turnBytes`) feeds the
  turn's workers (`workerEntropyOf`) and its new frames (`frameEntropyOf`); the interpreter
  path draws only when the turn made an `iframe`.
- `Page.serveExtra` sends `node_query` ops 30 to 32 to `Hosts.Dom` with those below 16
  (`domQueryOps`); the branch had sent every op but 16-19, 33 and 34 there, which took
  ops 20-29 from the measure and 100-199 from `domOp`.
- BubblePopJS runs the prelude once, with no document, to make its realm. The shadow probe
  asks `node_info` 27, which `Hosts.Dom` answers for any node number, in place of 20,
  which needs a node.
- Shadow trees' `style` text is read through the engine's kept sheets (`sheetIn`) in
  place of the module-level memo main removed.
- `findFlattenedSlottables` keeps its nesting in a work list (`flattenedLoop`), so a page
  that nests slots deeply does not deepen the stack; checked against the recursive
  `flattenedGo` on every slot of test pages, not proved equal.
