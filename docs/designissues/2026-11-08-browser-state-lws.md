# Foafnaut browser state in Linked Web Storage

Date: 2026-11-08. Author: browser-state, a subagent of session depmap-0e.
Owner's request, 2026-11-08: "Add loopback lws local service for storing state
eg bookmarks, history, … Optionally remote hosted pod used to sync/save this too."

## 1. Result

Foafnaut keeps bookmarks, history, settings and open tabs as Linked Web Storage
(LWS) resources.

- The native browser starts `factoidal lws-serve` on 127.0.0.1, with
  authorization on and a root ACL that gives only this browser's `did:key` Read,
  Write and Control. Another program on the computer gets 401 without that key.
- The Hub keeps the same resources in the browser's IndexedDB.
- `:sync` exchanges bookmarks, history and settings with a remote pod (native
  browser only, for now). The same `did:key` authenticates there.

Before this change, Foafnaut kept no state between runs. History was the
session history of each tab (`WebHistory.lean`, in memory). Theme and text zoom
were host variables, lost at exit.

## 2. Who decides what

| Part | File | Decides |
| --- | --- | --- |
| Lean | `labs/demos/foafnaut/WebState.lean` | the path and JSON-LD text of each resource, the merge of two copies, the sync plan, which URLs a sync may fetch, the pages `foafnaut:bookmarks` and `foafnaut:history` |
| LWS client (Lean) | `formal/lean4/L4Factoidal/LWS/Client/` | every HTTP request, header, token exchange and retry |
| LWS server (Lean) | `formal/lean4/L4Factoidal/LWS/`, `Authz/` | status codes, containment, Web Access Control |
| Store and sync path (JS) | `docs/web/hub/foafnaut/browser-state.mjs` | nothing: moves Lean's texts between Lean and a store |
| Native host | `labs/demos/foafnaut/native_state.ts` | starts the server, keeps the key file, carries bytes |

The engine answers the ops through `web_document_call` (`WebDocument.lean`
dispatches to `WebState.op`). An engine built before `WebState` answers
"unknown op". The native host then uses `web-state`, a small program with the
same ops (`WebStateCLI.lean`, `build-web-state.sh`). The Hub then has no state
and says so on `:bookmarks`.

Ops: `stateInfo`, `stateVisit`, `stateBookmark`, `stateUnbookmark`,
`stateSettings`, `stateSession`, `stateRead`, `statePage`, `stateMerge`,
`stateSync`, `stateFetchAllowed`.

## 3. Resources and vocabulary

All paths are under `/foafnaut/` in the storage. The media type is
`application/ld+json`. Factoidal's JSON writer (`L4Factoidal.JSON.Serialize`)
writes the text, with one fixed `@context`: `@vocab` is `https://schema.org/`,
and `foafnaut:` is `https://danbri.github.io/factoidal/ns/foafnaut#` (not yet
published as a document).

| Resource | Path | Type | Members |
| --- | --- | --- | --- |
| a bookmark | `/foafnaut/bookmarks/<FNV-1a 64 of the URL, hex>.jsonld` | `schema:BookmarkAction` | `object` (a `WebPage` with `url`, `name`), `keywords` (tags), `startTime` (added), `dateModified`, `foafnaut:deleted` |
| one UTC day of history | `/foafnaut/history/YYYY-MM-DD.jsonld` | `foafnaut:HistoryDay` | `foafnaut:day`, `foafnaut:visit` (a set of `schema:ViewAction`: `startTime`, `object` `WebPage`, `foafnaut:from`) |
| settings | `/foafnaut/settings.jsonld` | `foafnaut:Settings` | `foafnaut:theme`, `foafnaut:textZoom`, `foafnaut:font`, `foafnaut:fontFallback`, `foafnaut:remotePod`, `dateModified` |
| open tabs | `/foafnaut/session.jsonld` | `foafnaut:Session` | `foafnaut:tab` (a list of `WebPage` with `foafnaut:scroll`), `foafnaut:activeTab`, `dateModified` |

Times are `xsd:dateTime` in UTC with milliseconds, all the same width, so their
texts sort as the times do. Only web and file pages go into the history; the
`foafnaut:` pages and view-source tabs do not.

## 4. Merge and sync

- **History:** a day's visits are a set. The set is the list of canonical visit
  texts (each node read and written again) in `compare` order. Merge is the
  union of the two lists (`WebState.union`). Proved in `WebState.lean`, with no
  `sorry`, `axiom` or `native_decide`:
  - `union_comm`: `union xs ys = union ys xs`, for every two lists;
  - `union_self`: `union xs xs = xs`;
  - `mem_union`: a visit is in the union if and only if it is in one side;
  - `merge_history_comm`: the merge of two copies of a history day is the same
    in either order.
- **Bookmarks and settings:** last writer wins per resource, by
  `dateModified`, then by the text, so both sides choose the same copy
  (`lww_comm`, `lww_self`). A removed bookmark stays as a resource with
  `foafnaut:deleted true` and a newer `dateModified`, so a removal also syncs.
- **Open tabs** belong to one device and do not sync (`syncs`).
- **Sync** (`syncPlan`): for each path either side has, the merged text, sent
  to each side that does not have it. A second sync sends nothing. The test
  checks this.

The clocks of two devices are not compared for history (a set has no winner).
For bookmarks and settings a device with a wrong clock can win or lose a
conflict. A version vector per resource would remove that; it is not done.

## 5. The local server (native browser)

Folder: `~/Library/Application Support/foafnaut/` on macOS
(`$XDG_DATA_HOME/foafnaut` elsewhere); `--state-dir DIR` changes it.

- `agent.json`: the `did:key` and its private key, made by the engine
  (`lwsClientNewKey`), mode 0600. No log line or page shows the private key.
  The `did:key` itself is public; the log shows it so that a person can give it
  access on a pod.
- `lws-port`: the port. It is chosen once and then fixed. The storage's access
  tokens name its origin: a restart on another port answered 403 in a probe.
- `pod/`: the storage (`lws-serve --storage files`).
- `pod-authz/`: the signing keys of the authorization server on the same port
  (`lws-serve --authz`).

Command: `factoidal lws-serve DIR/pod --authz DIR/pod-authz --owner DID
--host 127.0.0.1 --port PORT`. The LWS server code is not changed. When another
Foafnaut window runs the server on the same folder (`lws.lock`), the second
window uses it.

The server starts in the background. The window does not wait for it. A failure
gives one log line (`browser-state`, `state: off`) and the browser works without
state. Sweeps, checks and `--no-state` do not start it.

Commands in the address bar: `:bookmark [tag, tag]`, `:unbookmark`,
`:bookmarks`, `:history`, `:pod URL`, `:sync`. Theme and text zoom are saved
when they change and applied at the next start. `--restore-session` opens the
tabs of the last run.

## 6. Remote pod and network policy

`:pod https://pod.example/` saves the storage root URL. Lean refuses a pod that
is not https (http only on loopback) or that does not end in `/`. `:sync` uses
the same `did:key` (self-issued credentials, lws10-authn-ssi-cid). The owner of
the pod must give that `did:key` access to `/foafnaut/`.

Every request of a sync goes through `guardedFetch`. Lean
(`stateFetchAllowed`) allows only the pod's origin and loopback. A pod whose
authorization server is on another origin is refused; that is intended for now.

Each request gives one JSON line (`browser-state-fetch`): method, origin, path,
status, time, size. No header, query or body is logged. This is less than the
evidence record of the 2026-10-25 rule (TLS details, certificates, addresses).
That rule is for pipeline retrievals; state sync to a pod the person names is
not a pipeline step. To record sync requests as evidence too is open work.

Tests use only servers on 127.0.0.1 in temporary folders, never a live pod and
never an account.

## 7. The Hub

An https page cannot rely on a loopback server, so the Hub keeps the resources
in IndexedDB (`indexedDbStore`), in the same format and through the same calls.
Without IndexedDB it keeps them in memory for the tab. `:sync` on the Hub says
that sync runs in the native browser: the Hub does not load the LWS client
engine (`l4factoidal.wasm`, about 32 MB) or keep a private key yet.

The published Hub engine was built before `WebState`, so the Hub has state only
after the next engine build.

## 8. Tests

- `#guard`s in `WebState.lean`: dates, FNV-1a, paths and kinds, the write plan,
  the fetch rule.
- `labs/demos/foafnaut/browser_state_test.ts` (`test.sh` runs it when
  `web-state` is built and `factoidal` is on PATH):
  1. the ops through `web-state`: paths, merge in both orders, last writer wins
     with a removal, the sync plan, the fetch rule, page escaping, and the same
     API over a memory store;
  2. a local server in a temporary folder: write, restart, read back the same
     state; 401 without the key; key file mode 0600; then two devices with the
     same key sync through a second local server, and a second sync sends
     nothing; the log has no token and no private key;
  3. the window's view: an engine without the state ops falls back to
     `web-state`; commands, pages and the pod rule.
- Not tested: IndexedDB in a real browser (the same code runs over the memory
  store in the test); the native window end to end with a GPU.

## 9. Open

- Hub sync (load the LWS client and keep a key in IndexedDB).
- Evidence records for sync requests.
- A version vector for bookmarks and settings.
- History retention: days are kept for ever; a limit is a setting to add.
- `visitSet` inserts one visit at a time (quadratic in the visits of one day).
