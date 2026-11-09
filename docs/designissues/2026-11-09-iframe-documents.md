# Frame documents in the script session

Date: 2026-11-09. Author: shadowframes, a subagent of session depmap-0e.
Records it joins: `2026-11-08-page-scripts.md`, `2026-11-08-shadow-dom-frames.md` (the
rest of the frames and Shadow DOM work, which follows).

## Result

The native script session (`scriptSession`, both engines) gives every connected `iframe`
a browsing context, as the WasmVM bench already did:

- At `start` and on insertion, an `iframe` gets an `about:blank` document at once
  (`Hosts.Dom.connectFrames`). A `srcdoc` document is parsed and loaded by Lean after the
  turn (`WebScripts.srcdocLoads`). A `src` URL is the embedder's: with `navigations:true`
  in `start`, each turn lists `navigations: [{nodeId, url}]` (the URL parsed against the
  page's URL), and the embedder answers each with the action `frame` (`node`, `url`, and
  `bytesBase64` with `contentType`, which Lean decodes with
  `WHATWG.Encoding.Sniff.decodeDocumentFast`, or `source` as text, with `resources` for
  its `src` scripts, or `failed:true`). Without `navigations:true` a frame with a URL keeps
  `about:blank` and gets its `load` event.
- A frame document is a command, `Command.frameDocument (el, source, xml, root)`, so the
  replay of a render over the parsed page makes the same node numbers.
- `contentDocument` (and `contentWindow.document`) answer a frame's document only for a
  frame of the page's origin (`Hosts.Dom.frameAccessible`, from `HTML.Frames`: `srcdoc`
  and `about:blank` have the page's origin, a URL its own, a sandbox without
  `allow-same-origin` a fresh opaque one).
- A same-origin frame's scripts run in the page's realm, in document order, with
  `document` the frame's document while they run (the prelude's `script()` sets it from
  the current script), and with a window target of their own for `load` and `error`. So
  functions a frame defines are reachable as `contentWindow.f`. A frame of another origin,
  or one whose sandbox lacks `allow-scripts`, runs no script there
  (`Hosts.Dom.frameScriptsInRealm`, theorem `frameScriptsInRealm_sameOrigin`;
  `HTML.Frames.scripts_need_allow`, `sandboxed_no_access`).
- Load events: the frame's window `load`, then the `iframe`'s; the page's window `load`
  waits for frames still loading (`Hosts.Dom.State.loadWaits`), except `loading=lazy`
  ones. The initial `about:blank` of the parser's iframes fires no event.

## What a frame shares

Same-origin frames share the page's realm: their globals are the page's, and so is
`location`. Realms of their own (one heap per frame, WindowProxy objects between them) are
later work; so are drawing a frame's document, and the AOT path (the Hub), where frames
stay off.

## Cost

A page with no `iframe` pays one look at its nodes at start and one look at an empty list
after each turn. Render timings of plain pages are within noise of the engine before.
