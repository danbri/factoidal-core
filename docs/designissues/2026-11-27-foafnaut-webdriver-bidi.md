# Foafnaut: WebDriver BiDi, stage 1

Status: stage 1 in progress (2026-11-27). Tracking:
https://github.com/danbri/factoidal-core/issues/372 (Foafnaut developer tools; BiDi is its stage 3
in the first order and stage 5 in the order of 2026-11-09).

Owner, 2026-11-27, verbatim: "Do items 1 and 2", where item 2 was "live remote debugging,
WebDriver BiDi first, then a part of the Chrome DevTools Protocol only where Chrome's own panels
need it". Record: CLAUDE.md, "Foafnaut timelines, remote debugging and WebDriver scores".

Specification: W3C WebDriver BiDi, editor's draft (https://w3c.github.io/webdriver-bidi/).
Tests: WPT `webdriver/tests/bidi/`.

## 1. What exists

- WebDriver classic in Lean, `formal/lean4/L4Factoidal/WebDriver/`: `Gate` (who may use the
  endpoint), `Protocol` (routing, sessions, capabilities, timeouts), `Window`, `Page`, `Actions`,
  `Input`, `Capture`, `Errors`. Security record: `docs/designissues/2026-11-14-input-webdriver.md`,
  "The WebDriver endpoint and its security".
- The endpoint is started only by the WPT runner, `tests/browser-wpt/testharness-run.ts`, with
  `--dangerously-enable-webdriver-endpoint`. The runner's listener is `Deno.serve` on 127.0.0.1.
  The engine side is the `webdriverStart` and `webdriver` actions of
  `labs/demos/foafnaut/WebScripts.lean`.
- `Protocol.Browser.socketBase` and the `webSocketUrl` capability were in `Protocol` before this
  stage, but no host set `socketBase` and nothing listened for WebSocket connections.

## 2. Transport

BiDi messages are JSON texts in WebSocket text frames (BiDi section "Transport").

- A client that made a classic session with the capability `webSocketUrl: true` gets the value
  `ws://127.0.0.1:<port>/<secret>/session/<session id>` back from New Session
  (`Protocol.handle`; `socketBase` is `ws://<address>:<port>/<secret>`). It opens a WebSocket
  connection to that URL. The WPT fixture `bidi_session` does this
  (`webdriver/tests/support/bidi/fixtures.py`).
- A client with no classic session opens `ws://127.0.0.1:<port>/<secret>/session` and sends
  `session.new` (a "BiDi-only" session). That session has no HTTP flag: classic commands that
  name it answer `invalid session id` (`Protocol.Session.http`).
- The secret is the first path segment, as for classic requests. The upgrade request goes
  through `Gate.admit` with the same gate state as classic requests: one count of refusals, one
  lock.
- Messages on an open connection carry no secret: the connection was admitted once. A
  connection value exists only as the result of `BiDi.connect`.

## 3. Where each decision is

All protocol decisions are in Lean. The host moves bytes.

| Decision | Lean | Host |
|---|---|---|
| Endpoint on or off, address, secret | `Gate.start` (unchanged) | binds the address Lean allowed |
| Admit a WebSocket upgrade (secret, `Origin`, `Host`, lock) | `BiDi.connect` (calls `Gate.admit`) | passes the path and two headers; answers 403 or 404 when Lean refuses |
| Which session a connection belongs to | `BiDi.connect` | keeps the connection value Lean returned |
| Parse a message; error for a bad message | `BiDi.parseMessage` | passes the text of each text frame; a binary frame is passed as `binary` |
| Session check, static commands | `BiDi.exec` | none |
| Each command's parameters, result and errors | `BiDi.exec` | none |
| Navigation | `BiDi.exec` answers `navigate url`; the page load is the same host load that classic Navigate To uses | loads the page, then sends the reply Lean gave |
| Event subscriptions | `BiDi.State.session.subscriptions`, `BiDi.subscribed` | none |
| Event messages | `BiDi.eventMessage` (stage 1 sends none; see section 6) | sends what Lean gives |

## 4. Gate and invariants (issue 1120)

Gate items of `docs/designissues/2026-10-28-feature-combination-safety.md` section 5, for this
surface:

1. Kind: listener (WebSocket on the WebDriver endpoint's port).
2. Principal: the holder of the endpoint secret. `Gate.admit` on the upgrade request; no
   identity beyond the secret. Loopback only, no TLS (I4: loopback).
3. Access decision: `BiDi.connect` (through `Gate.admit`) for the connection; `BiDi.exec` for
   each message. Theorems: `connect_refused` (a refused upgrade gives no connection and changes
   no session), `connect_no_secret`, `connect_origin`, `handle_error_keeps` (a message answered
   with an error changes no state).
4. Credentials: the secret only, received, never sent anywhere. The `webSocketUrl` value holds
   it and goes only to the client that made the classic session (which already holds it).
5. Outbound requests: `browsingContext.navigate` loads a URL the client chooses. This is the same
   reach as classic Navigate To; the client already has full control of the browser.
6. Browser reach (I7): a page's WebSocket handshake always carries `Origin`
   (RFC 6455 section 4.1, item 8 for browser clients), so `Gate.admit` refuses it
   (`connect_origin`). `Host` must be this endpoint on a loopback name. No CORS.
7. Limits: the gate's lock after `Gate.maxFailures` refusals (shared with classic). Not
   enforced: a limit on message size and on the number of open connections. Expected failure
   and issue: section 7.
8. Records: none. Messages are not logged.
9. Rows: C7 (browser reach), C13 (limits). Invariants I7 (Host and Origin; `connect_origin`,
   `admit_ok`), I13 (not met for connection count and message size; section 7).
10. Defaults and notice: off by default (`Gate.start_off`); the flag
    `--dangerously-enable-webdriver-endpoint` is the only route; the host prints the experimental
    code notice on standard error when the endpoint starts.

## 5. Order of modules and the WPT directories that measure each

| Stage | BiDi module and commands | WPT directories |
|---|---|---|
| 1 (this) | `session.status`, `session.new`, `session.end`, `session.subscribe`, `session.unsubscribe`; `browsingContext.getTree`, `browsingContext.navigate`; message errors | `bidi/session/status`, `bidi/errors`, `bidi/session/subscribe`, `bidi/session/unsubscribe`, `bidi/browsing_context/get_tree`, `bidi/browsing_context/navigate` |
| 2 | `browsingContext.create`, `close`, `activate`, `reload`, the context events (`contextCreated`, `contextDestroyed`, `navigationStarted`, `domContentLoaded`, `load`) | `bidi/browsing_context/create`, `close`, `context_created`, `context_destroyed`, `load`, `dom_content_loaded`, `navigation_started` |
| 3 | `script`: `evaluate`, `callFunction`, `getRealms`, `disown`, preload scripts; remote values | `bidi/script/` |
| 4 | `log.entryAdded` (console and errors) | `bidi/log/` |
| 5 | `network` (events, then interception) | `bidi/network/` |
| 6 | `input.performActions`, `releaseActions`, `setFiles` (over `WebDriver.Actions`) | `bidi/input/` |

Many tests of `navigate` and `subscribe` use the fixture `new_tab` (`browsingContext.create`) or
`create_console_api_message` (`script.evaluate`), so their scores move with stages 2 and 3.

## 6. Stage 1 behaviour

- Message errors: a binary frame, a text that is not JSON, or JSON that is not a command gives an
  error message with `id` null unless the text has an `id` that is a JS unsigned integer. A
  `method` that is a string and not a command name gives `unknown command`; anything else gives
  `invalid argument`.
- Without a session, every command but `session.new` and `session.status` gives
  `invalid session id`.
- `session.subscribe` checks every event name (a module name expands to its events), every
  context id and every user context id before it changes anything; one bad entry and nothing is
  subscribed. `contexts` with `userContexts` is `invalid argument`.
- `session.unsubscribe` by `subscriptions` removes each named subscription; an unknown id is
  `invalid argument` and removes none. By `events`, it removes the events from the global
  subscriptions; an event that no global subscription has is `invalid argument`.
- `browsingContext.getTree`: the one top-level context (the window handle of
  `WebDriver.Window.State`), its URL, `children` empty, or null at `maxDepth` 0.
- `browsingContext.navigate`: `url` must parse (`WHATWG.URL.parseUrl`); `wait` must be `none`,
  `interactive` or `complete` (absent and `none` mean "committed" in the specification). The
  host loads the page before the reply, for every `wait`. The `navigation` id is a version 4
  UUID from the machine's generator.
- `session.end` ends the session for a BiDi-only session and for a classic session (the
  specification refuses neither), then the host closes the connection.
- An upgrade to a path that is not `/session` or `/session/<the active session id>` is answered
  404. The specification says only "act as if the requested service is not available"
  (RFC 6455 section 4.2.2 allows the server to answer with an HTTP error); 404 is our choice.
- No event messages are sent in stage 1 (subscriptions are kept; stage 2 sends the context
  events).

## 7. Shortfalls of stage 1

Each is an expected failure (`#guard` of today's result, which fails when the behaviour changes)
plus an open issue: https://github.com/danbri/factoidal-core/issues/1203 (WebDriver BiDi stage 1
shortfalls).

1. One top-level context only: `getTree` reports no child contexts for iframes.
2. `browsingContext.create` and `close` are `unknown command` (stage 2).
3. No event is sent, although subscriptions are accepted.
4. No limit on the size of a message or the number of open connections (I13).
5. `navigate` with `wait` absent, `none` or `interactive` waits for the load, not for the commit
   or for `DOMContentLoaded`.

## 8. Tests

- Lean: the `#guard`s and theorems of `L4Factoidal/WebDriver/BiDi.lean`.
- Host: `tests/browser-wpt/testharness-run.ts --dangerously-enable-webdriver-endpoint` with a
  list of `webdriver/tests/bidi/` files (`skills/wpt-runs`). Scores in section 9 when measured.

## 9. Measurements

None yet.
