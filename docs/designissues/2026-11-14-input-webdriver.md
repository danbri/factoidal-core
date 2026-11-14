# User input as tests and automation see it: WebDriver actions, the test driver, a WebDriver endpoint (2026-11-14)

Two things were missing on main `19fb349c1`:

- **Input of a user in the WPT runner.** `resources/testdriver.js` asks its vendor file for
  clicks, keys and action sequences. The runner had only key actions (on a branch). About
  38,000 Chrome subtests are in tests that load `testdriver.js`: editing/other (16,742),
  input-events (3,366), pointerevents, uievents, touch-events, html/semantics and
  html/interaction, focus and selection tests.
- **Remote control of the browser.** `webdriver/tests` (wdspec: Python tests that drive a
  browser over the WebDriver protocol) is 9,810 Chrome subtests in 685 files, 3,704 classic
  and 6,086 BiDi, none run. The same protocol is how any tool automates the browser
  (screenshots and scripted checks of real pages).

Both are the same thing underneath: input that the page must see as its user's, injected by
something that is not the page. This record is the design of that channel.

## One pipeline

```
WebDriver Perform Actions (JSON)          test_driver.click / send_keys / Actions
            \                                   /   (console line, WPT runner only)
             scriptSession action `actions` (the host's channel into the engine)
                         |
        WebDriver.Actions.parse      sources and actions, or `invalid argument`
        WebDriver.Actions.ticks      tick i = action i of every source
        WebDriver.Actions.step       input state (keys held, modifiers, pointers) -> Low events
                         |
        Hosts.PageEvents.dispatchLow
           key      keydown -> [keypress -> [beforeinput -> edit -> input]] ; keyup
           pointer  hit test (measure op 35, the layout's) -> boundary events ->
                    pointerdown/mousedown/[focus] | pointerup/mouseup/click/dblclick | move | cancel
           wheel    hit test -> wheel
```

Everything in the diagram is Lean. The engine is told nothing about tests: the runner's vendor
file turns a `test_driver` call into the WebDriver request a WebDriver client would send.

| Module | Content |
|---|---|
| `L4Factoidal/WebDriver/Keys.lean` | WebDriver's key table (U+E000 to U+E05D): `key`, `code`, `location`, legacy `keyCode`; the keys of a US keyboard; which characters need Shift. |
| `WebDriver/Errors.lean` | The 28 error codes with their JSON error code and HTTP status; the error and success bodies. |
| `WebDriver/Actions.lean` | `parse` (§15.3 extract an action sequence), `ticks` (§15.4), `State` and `step` (§15.4.2 to §15.4.4), `performTicks` over any engine, `release` (§15.6), `typeable` (§12.5.3 Element Send Keys), `inViewCentre` (§12.1). |
| `WebDriver/Input.lean` | `hitOf` and `pointerTarget` (the hit test answer and capture), `boundary` (over, out, enter, leave), `clickCount`, `keypressChar`, the event inits, `resolvePath` (the test driver's element references), `afterCancelable`, `Trusted`. |
| `WebDriver/Gate.lean` | Whether the endpoint starts and whether a request is let in. |
| `WebDriver/Protocol.lean` | The endpoint table (§6.2), `route`, capabilities processing (§7.2), sessions, timeouts (§9), `handle`. |
| `WasmVM/Hosts/PageEvents.lean` | `key` (now with `keypress`), `lowPointer`, `lowWheel`, `lowKey`, `dispatchLow`, `inputDriver`. |
| `WasmVM/Hosts/LeanJS.lean` | `Session.trusted`, kept outside the script heap, with the isolation theorems. |
| `DOM/Focus.lean` | `pressTarget`: the focusable area a press focuses. |

Host side: `labs/demos/foafnaut/WebScripts.lean` (scriptSession actions `actions` and
`message`; a turn's `inputError`), `tests/browser-wpt/testdriver-vendor.js` and the drive loop
of `testharness-run.ts`.

### Decisions

- **Hit testing is the layout's.** The target of a pointer event at a viewport point is the
  first element of measure op 35, the answer `document.elementFromPoint` gets
  (`WebHit.target`). There is no second hit test for input. `Input.pointerTarget` is where
  capture will override it.
- **Element origins are resolved at the action.** `Actions.performAction` asks the engine for
  the page's `Env` (viewport, in-view centre of an element) before each action, after the
  events of the action before it were dispatched. So an origin element that an earlier event
  moved is found where it is now. Only an action with an element origin lays the page out.
- **A move is one event.** WebDriver interpolates a pointer move over its duration; here the
  pointer arrives at the target in one `pointermove` and the tick's duration then passes on
  the virtual clock. Tests that Chrome passes do not depend on the intermediate points.
- **Blink's order of boundary events**: pointer out, leave, over, enter, then the mouse four,
  then the move.
- **Click count**: a press within 500 ms of the last at the same point with the same button
  counts one more; `dblclick` follows the click of an even count.
- **Default actions run through one function.** `Input.afterCancelable cancelled default s`.
  `keypress`, `beforeinput`, the editing command, `input` and the caret move are default
  actions of `keydown`; the edit is a default action of `keypress` and of `beforeinput`;
  `mousedown` and `mouseup` are withheld after a cancelled `pointerdown` (Pointer Events 3
  §11); the focus change is a default action of `mousedown`.
- **Key events go to the focused element** (`Node.states` bit 8), else the editing host of
  the selection, else the `body`.
- **The test driver's element reference** is the element's tree path from the document
  (child indices, `s` into a shadow root). It is not observable by the page (wptrunner's own
  vendor file may add an attribute to the element).
- **The page is answered with a `message` event**, as wptrunner answers its vendor file
  (`{type: "testdriver-complete", id, status}`).

## Trusted input can not be forged by page script

What "trusted" means here, and what holds it:

1. **The input state** (keys and buttons held, modifiers, pointer positions, the time of the
   last user activation) is `LeanJS.Session.trusted`. It is a field of the session, not of
   the script heap. Every run of page script, and every import that serves it, is a function
   of the heap handed to `Session.run` or `Session.runG`. **Proved** for every such function:
   `run_trusted`, `runG_trusted`, and from them `api?_trusted`, `dispatchOnly_trusted`,
   `callbackOnly_trusted`, `runJobs_trusted`: the trusted state after equals the state
   before. `setTrusted_spec`: the setter changes that field and nothing a script reads. The
   setter is called in one place: the `actions` action of `WebScripts.actLean`.
2. **The events.** A trusted event exists only where the engine calls the prelude's
   `dispatch` hook (`Session.dispatchOnly`). The hook object is the return value of the
   prelude, held in `Session.api`; it is not a property of any object a script can reach.
   Callers of the hook with an input event type (key, pointer, mouse, wheel, click) are
   `PageEvents.key`, `lowPointer`, `lowWheel`, `pointer`, `click`, all reached only from a
   scriptSession action of the host. The event loop queues events of two types for the
   page's own work: `load`, and the `click` of the host's `click` action. **Not proved**
   (it is a property of `prelude.js`): that `dispatchEvent` marks a script's own event
   untrusted and that the hook object does not leak. Tested by WPT
   (`dom/events/Event-isTrusted.any.js`, `uievents`).
3. **The channel.** A console line `__wpt_driver {...}` is input only in the WPT runner
   (`testharness-run.ts` reads it, as wptrunner reads its vendor file's messages). The
   browser hosts (`run_html.ts`, the Hub worker) do not read console lines as commands.

## The WebDriver endpoint and its security

A WebDriver endpoint is remote control of the browser: whoever can send it a request can read
every page it shows and act as its user.

| Threat | Defence | Where |
|---|---|---|
| A user who did not ask for it | Off by default: no endpoint without the user's flag; the flag is a risk token (`Risk.Accepted .webdriverEndpoint`, made only by `Risk.dangerouslyAccept`), so code that starts an endpoint without naming the risk does not compile. Only the test runner's `--dangerously-enable-webdriver-endpoint` will make one | `Gate.start`, `start_off`, `start_default`, `L4Factoidal/Risk.lean` |
| Another machine | Bound to a loopback address only | `Gate.start`, `start_not_loopback`; the listener binds the address it asked about (host plumbing) |
| Another process or user of this machine | A secret of 128 bits from the machine's generator, made at start, first segment of every request path; no generator, no endpoint | `Gate.start`, `start_no_entropy`, `start_secret_length`; `Gate.admit`, `admit_no_secret` |
| Guessing or timing the secret | The comparison reads every character; the endpoint locks after 16 refusals until it is started again | `sameText_iff`, `admit_locked`, `admit_failures_mono`, `admit_refused_counts` |
| A web page (any browser on this machine, this one included) posting to the port | A request with an `Origin` header is refused even with the secret | `admit_origin` |
| DNS rebinding (a page's own host name pointed at 127.0.0.1) | The `Host` header must be this endpoint on a loopback name | `admit_ok` |
| Page script in this browser reaching the endpoint | The three rows above; and a page loaded from a public address can not reach loopback at all (`Net.PageFetch`) | |
| A second client taking over | One session at a time; every command but Status and New Session names the session id | `endpoints_session`, `handle_no_session` |

`Protocol.handle` runs the gate before anything else. **Proved**: `handle_refused` and
`handle_no_secret`: a request the gate refuses leaves the session exactly as it was, is never
handed to the page, and is answered 403 with no detail. Only the gate's count changes.

Open (security):

- The compiled comparison is not shown to be constant time (it has no early exit; the branch
  on each character is data-dependent). The lock bounds the leak to 16 tries. Register entry
  in `skills/lean-risk-flags`.
- The secret reaches the client through the host (printed for the process that asked, or a
  file only the user can read): host plumbing, not checked by Lean.
- No TLS: loopback only.
- A WebDriver client is trusted with everything once it holds the secret. There is no
  per-origin permission inside a session.

## One key path for every host

The test driver's keys (`actions`), the window's keys and typed text, and the Hub's keys take
one path: `WebDriver.HostKeys` turns what a host has (a macOS virtual key code with modifier
bits, a DOM key value, or committed text) into WebDriver key actions, and the session action
`key` runs them through `Actions.perform` and `PageEvents.dispatchLow`, the code `actions`
runs. Committed text is typed as Element Send Keys types a string (`text_is_send_keys`), and a
host's press releases what it pressed, last first (`press_balanced`). A key in a focused
`input` (text, search, url, tel, password) or `textarea` edits the control's value
(`Editing.TextKeys`: `beforeinput` at the control, then the command through `textEdit`, op
179, which fires `input`); Enter edits nothing in an `input` (`textKeyCommandIn_single`). The
turn's `keyDefault` tells the window whether to scroll for the key: only when its `keydown` was
not canceled and the key went to no text control or editing host. Space goes as its key
(U+E00D), so the window drops its committed text. The window sends no key releases, so a press
is whole. Open: the Hub does not send keys yet (it would send `{action:"key", key, modifiers}`);
keys in an `email` input (no selection there in the page's glue).

## wdspec in the full run

wptrunner runs a wdspec file by calling pytest on it, with a JSON file that names the
WebDriver host and port, the capabilities and wptserve's configuration
(`tools/wptrunner/wptrunner/executors/pytestrunner/runner.py`). The project's runner does the
same per name: `testharness-run.ts` classifies a `.py` name as `wdspec`; with a WebDriver
endpoint of its engine it starts `wdspec-run.py` (pytest from the WPT tree's
`tools/third_party`, the client from `tools/webdriver`) and records each pytest test as a
subtest, as wpt.fyi does. The WPT tree for a shard needs `webdriver/` whole and `tools/`
(already there for wptserve).

## Measured

| Step | Commit | Run | Result |
|---|---|---|---|
| Key actions (editing's work), on main | `2598f05e7` | branch check 43559453757 | +13,980 on /editing/, /input-events/, /selection/, /uievents/, sample:150 against main `19fb349c1`: editing/other 2,203 -> 12,014 of 16,742; input-events 303 -> 2,545 of 3,366; editing/plaintext-only 593 -> 1,526; editing/whitespaces 424 -> 1,161. 9 tests worse, -19 subtests |

## Proved, tested, open

Proved (Lean, no `sorry`, no axiom):

- Keys: `special_bounded`, `ofRaw_printable`, `ofRaw_special`, `modifier_iff`.
- Errors: `status_is_error`, `mem_all`, `names_nodup`, `ofName_name`, `name_injective`, `body_error`.
- Actions: `ticks_length`, `ticks_getElem?`, `mem_tickAt` (tick `i` is exactly the actions
  numbered `i`); `performTicks_append` (ticks are dispatched in order); `performTick_error`,
  `performTicks_error` (nothing is dispatched after an error); `step_pause`,
  `step_keyUp_notHeld`, `step_pointerDown_held`, `step_pointerUp_notHeld`;
  `step_move_out_of_bounds`; `inViewCentre_inside`; `release_clears`.
- Input: `pointerTarget_free`, `pointerTarget_captured`; `boundary_same`, `boundary_leave`,
  `boundary_enter`; `afterCancelable_cancelled`, `afterCancelable_run`; `clickCount_pos`;
  `keypressChar_modified`.
- Focus: `pressTarget_focusable`.
- Trusted state: `run_trusted`, `runG_trusted`, `setBudget_trusted`, `setHost_trusted`,
  `fail_trusted`, `api?_trusted`, `dispatchOnly_trusted`, `callbackOnly_trusted`,
  `runJobs_trusted`, `setTrusted_spec`.
- Gate: `start_off`, `start_default`, `start_not_loopback`, `start_no_entropy`,
  `start_secret_length`, `mismatches_zero_iff`, `sameText_iff`, `admit_ok`,
  `admit_no_secret`, `admit_origin`, `admit_locked`, `admit_failures_mono`,
  `admit_refused_counts`.
- Protocol: `endpoints_nodup`, `endpoints_session`, `route_error`, `handle_refused`,
  `handle_no_secret`, `handle_no_session`.

What the three theorems the task named say here:

- *An actions sequence dispatches events in tick order*: `performTicks_append` with
  `mem_tickAt`. The run of ticks `a ++ b` is the run of `b` from the state the run of `a`
  left, for every engine.
- *Pointer capture and hit testing agree with the layout's hit test*: `pointerTarget_free`,
  and `PageEvents.hitAt` is defined as `Input.pointerTarget none` of measure op 35's answer.
  The agreement is by definition (one hit test), not by a proof about two.
- *A key action's default action runs only if the keydown was not cancelled*:
  `afterCancelable_cancelled`; `PageEvents.key` passes everything after `keydown` to it.
  The theorem is about that function; that `key` uses it is read from `key`'s definition.

Tested only: every `#guard` in the modules above (requests of the WPT tests); the prelude's
part (event classes, `relatedTarget`, the focus update steps); the runner's drive loop.

Open:

- Pointer capture (`setPointerCapture` and the capture events), touch events
  (`TouchEvent`, `touchstart`), compatibility mouse events after a touch, pen hover.
- Selection by pointer (caret at the press, drag selection); scrolling by wheel (the page of
  a script session does not scroll).
- Typing in `input` and `textarea` by keys; Tab focus navigation; activation of a button or
  link by Enter and Space.
- `navigator.userActivation` and APIs gated by activation (the time of the last activation
  is kept in `Session.trusted`; no page API reads it yet).
- Interpolated pointer moves.
- The browser hosts' own pointer path (`PageEvents.pointer`, fed by `nodeAt`) does not use
  `lowPointer` yet: boundary events, click count and press focus are in the new path only.
