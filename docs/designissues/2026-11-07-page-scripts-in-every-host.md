# Page scripts in every host: the engine setting, the guest API, timers and frames

Owner, 2026-11-07, verbatim: "Can we have a basic JS engine that engages with content
please? One of the two we started towards. A switch inthe settings to chose
none/VerifiedJS/TheOtherOneJS". Earlier (issue 1252): "We should move to VerifiedJS for JS.
And get it wired up via DOM. Behaviour in pages needs to be JS."

Tracking: https://github.com/danbri/factoidal/issues/1271 (page scripts in the window) and
https://github.com/danbri/factoidal/issues/1252 (VerifiedJS). This record extends
[the script engine architecture](2026-11-03-script-engine-architecture.md); the engine
artifact, the worker boundary and the budgets there still hold.

## 1. The setting

The settings page has three links: `foafnaut:scripts/quickjs`, `foafnaut:scripts/verifiedjs`
and `foafnaut:scripts/none`. `WebShell.link` makes each a `scripts` command. The host keeps
the value; Lean says what it means (`WebRenderScript.setting?`, `WebRenderScript.plan`,
ops `scriptSetting` and `scriptPlan` of the document call):

| Setting | A page with classic scripts | Chrome marker | Page notice |
| --- | --- | --- | --- |
| QuickJS-NG (default, `defaultEngine`) | runs | `JS QUICKJS-NG` | none |
| VerifiedJS | refused (section 6) | `JS REFUSED` | `Page scripts refused (VerifiedJS): <reason>` |
| None | does not run | `JS OFF` | none |
| any, engine failed later | stops | `JS STOPPED` | `Page scripts stopped (<engine>): <reason>` |

The default is QuickJS-NG because it is the engine that runs pages. To change the default,
change `WebRenderScript.defaultEngine`. A new setting applies to the pages opened after it.
The marker is drawn at the right end of the address field (`WebShell.Shell.script`). The
notice is a `p` element that Lean puts first in the body after the script commands
(`WebRenderScript.withNotice`, request field `scriptNotice`), so it takes no node id that a
script holds. A page's scripts are never inert without a marker or a notice: a host with no
engine says so on the page (`native_html_document.ts`).

## 2. The guest API

Every DOM change is a typed command that Lean checks and applies
(`WebRenderScript.applyCommand`). The fields of each command are exact.

| Script API | Command | Lean semantics |
| --- | --- | --- |
| `textContent`, `innerText` (set) | `setTextContent` | DOM §4.4; one Text child changes in place, so the arena does not grow |
| `setAttribute`, `id`, `className` | `setAttribute` | DOM §4.9 (`DOM.Dom.setAttribute`) |
| `removeAttribute` | `removeAttribute` | DOM §4.9; HTML names in lower case |
| `document.createElement`, `createElementNS` (HTML, SVG) | `createElement` | DOM §4.5; the id must be the next arena id; `script` and `template` are refused |
| `appendChild`, `append` | `appendChild` | DOM §4.2.3 pre-insert; a cycle is HierarchyRequestError |
| `removeChild`, `remove` | `removeChild` | DOM §4.2.3 pre-remove |
| `classList.add`, `remove`, `toggle` | `classList` | DOM §7.1 ordered set, written to `class` |
| `style.setProperty`, `style.x = v`, `removeProperty` | `setStyleProperty` | CSSOM §6.6.1, written to `style` |
| `querySelector`, `querySelectorAll`, `getElementsBy*` | (query) `scriptQuery` | the cascade's selector matcher (`Rendering.CSS.selectorMatches`) |

Reads (`textContent`, `getAttribute`, `children`, `parentNode`, `isConnected`) see Lean's
arena: the guest sends its queued commands as one batch to the worker's own Lean instance
(`lean-dom.mjs`, op `scriptSnapshot`) before it reads. `setAttribute`, `appendChild` and
`removeChild` send at once, so a DOM error is thrown at the call. `innerHTML`, `dataset`,
`getBoundingClientRect`, `createTextNode`, `fetch` and `alert` throw a TypeError that names
this issue; nothing is silently ignored.

Events: `click` and `input` on elements, with the path from the target through its
ancestors to the document and the window; `keydown` and `keyup` on the document and the
window (no focus model). `preventDefault`, `stopPropagation` and `on<type>` properties work.
An error in a listener, a timer or a script is reported in the batch (`errors`) and the turn
goes on (HTML §8.1.4.3); a budget end stops the turn and the session.

Timers and frames (HTML §8.6, §8.10): `setTimeout`, `setInterval`, `clearTimeout`,
`clearInterval`, `requestAnimationFrame`, `cancelAnimationFrame`, `queueMicrotask`;
`performance.now()` is the host clock of the turn. A late interval runs once, not once for
each missed period. Promise jobs run after each turn (at most 1000).

## 3. Turns, order and history

`page-scripts.mjs` is the runtime of one document in every host. Input, timer and frame
turns run one at a time in the order they are asked for. Each batch says when the next
timer is due and whether a frame is wanted. The next frame turn is asked for only after the
host has shown the last batch (`onBatch` resolves when a presented frame has its commands),
so a slow frame slows the animation and does not queue turns. A page in a hidden tab gets a
frame or timer turn at most once a second.

The host replays the document's command history in each render, so the layout cache key
(`WebDocument.LayoutKey`, field `commands`) changes with the DOM. An animation writes the same
attributes on every frame; past 1024 commands the runtime asks Lean for a shorter history
(`WebRenderScript.compact`, op `compactCommands`). Compaction drops a write that a later
write to the same target replaces, and Lean keeps the result only when it replays to the
same arena node by node (`sameDom`). A Lean guard checks 15,000 commands of an animation
compact to 5; a Node test runs 1,500 frame turns and stays under 1,024 commands.

## 4. The desktop window

`native_html_scripts.ts` makes the hook that `prepareHTML` calls before it returns, so the
first frame has the scripts' first changes. The engine and its Lean instance run in their own
worker; the window's event loop only queues turns and asks for frames. A click goes to the
element under the pointer that has a click listener (Lean's hit test over the layout boxes);
a link under it is followed after the turn unless a listener cancelled the click. Text and
named keys go to the page's `keydown` listeners when the address bar does not have the
focus; they keep their default action (scrolling). `--script-sweep` opens
`pages/showcase-script.html`, clicks the counter, the list and the table buttons, types
`abc` while the animation runs, and checks Lean's DOM and the pixel hash after each step.

## 5. The Hub

`docs/web/hub/foafnaut/browser-worker.mjs` uses the same session and runtime (copied to
`web/hub/foafnaut/script-engine/` by the site build). The QuickJS-NG reactor and the Lean
module come from the site's runtime directory (`web/hub/html-webgpu/runtime/`), which the
release installs; the reactor is never committed. When the reactor is absent, or a nested
worker can not start (a sandboxed guest), the page says that the scripts were refused and
why. A runtime from before these Lean operations shows a note over the page.

## 6. VerifiedJS

`verifiedjs/adapter.mjs` gives VerifiedJS the same session interface. VerifiedJS has no
licence, so its source and binaries are not in this repository: `fetch-verifiedjs.mjs`
fetches the pin into the ignored `.build/verifiedjs/`, where it is built. When the compiler
is not there (the normal case on the owner's laptop, which takes no Lean build artifacts),
the page is refused with the commands that build it. When it is there, each script is
compiled; at the pin the module imports only `wasi_snapshot_preview1.fd_write` and exports
`main`, `_start` and `memory`, so it has no way to reach the document and the page is refused
with that interface named. In a web page VerifiedJS is refused: its compiler is a native
program with no WebAssembly build. Two expected-failure tests in `page_scripts_test.ts` hold
this; they fail when VerifiedJS can run a page, and then they and issue 1252 change together.

## 7. Measurements

See the issue comment of the landing for the numbers of `--script-sweep --perf-summary`
(click or key to present, and frame time and period during the animation).

## 8. Gaps

- Event targets are the elements with listeners, not the deepest element under the
  pointer; `event.target` is the listening element.
- No focus model: keys go to the document. No form controls, so `input` events come only
  from a host that sends them.
- No `innerHTML`, no text nodes as script objects, no `insertBefore`, no `dataset`, no
  layout reads (`getBoundingClientRect`, `offsetWidth`).
- Each command batch replays the history from the source in the worker's Lean instance; a
  retained Lean document would remove that cost.
