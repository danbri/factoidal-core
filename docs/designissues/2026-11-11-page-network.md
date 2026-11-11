# Page requests: XMLHttpRequest and fetch (issue 374)

Status 2026-11-11: on `wip/xhr`, not merged.

## Where the decisions are

- `formal/lean4/L4Factoidal/Net/PageFetch.lean`: what a page may reach, CORS, preflight,
  redirects, the address of a name, `data:` URLs, the response the page reads.
- `formal/lean4/L4Factoidal/Net/Xhr.lean`: the `XMLHttpRequest` object (state, events,
  response text and types), the `multipart/form-data` body of a `FormData`.
- `tools/wasmvm/quickjs/prelude.js`: the classes (`XMLHttpRequest`, `fetch`, `Headers`,
  `Response`, `Blob`, `File`, `FormData`); each method calls the engine.
- Hosts move bytes only: `labs/demos/foafnaut/native_net.ts` (desktop window),
  `docs/web/hub/foafnaut/browser-worker.mjs` (Hub), `tests/browser-wpt/testharness-run.ts`
  (wptserve).

Network is off unless the embedder starts a page session with `network:true`; then
`XMLHttpRequest`, `fetch`, `Headers` and `Response` are defined.

## The rules

- Schemes: `http` and `https` go to the host. A `data:` URL is answered by the engine, and
  only as the first URL of a request (a redirect to one fails; mode "same-origin" refuses it).
  No `file:`, `about:` or other scheme.
- Local addresses (`localhost`, `*.localhost`, special-purpose IP literals in any form the
  URL parser accepts) only for a page that is itself local (its URL, or the address the
  host loaded it from, `pageAddress`).
- DNS rebinding: on a native host, for a page that is not local, a request to a name is
  first a resolve-only request (nothing reaches the server). `Egress.choose` refuses the
  name when any address it resolves to is special-purpose, else pins one address; every
  request of that transfer to that host (preflight, request, a redirect back) carries the
  address, and the host connects to it without resolving again (`https` through a
  one-connection loopback tunnel, so TLS still checks the certificate against the name).
  Theorems: `onAnswer_reach`, `onAnswer_resolve_special`, `plan_send_allowed`.
- Mixed content: an `https` page reads `https` only.
- CORS: a request outside the CORS-safelist has a preflight on each hop; a cross-origin
  response is withheld unless the CORS check of that answer passes; only safelisted and
  exposed header fields reach the page. Theorems `deliver_cross_origin_needs_cors`,
  `plan_cross_unsafe_is_preflight`.
- No credentials: no cookies, HTTP authentication or client certificates are sent; a URL's
  user and password are removed; `Set-Cookie` never reaches the page
  (`responseOf_no_set_cookie`). `withCredentials` changes only the CORS check.
- Forbidden request fields and methods (Fetch §2.2.2) never reach the wire
  (`plan_wire_forbidden`), including a method-override field that names a forbidden method.
- Redirects are the engine's (the host fetches with redirect "manual"): at most 20; an
  `Authorization` field is dropped on a redirect to another origin; a redirect to another
  origin's URL with credentials fails.
- The Hub (`hostCors`): the browser that runs the Hub makes the request for the Hub's
  origin and enforces its own CORS; it follows redirects and preflights itself. The scheme
  and local-address rules apply to the first URL and to the final URL it reports. DNS is
  that browser's: no pin there.

## Security review, 2026-11-11

Checked: the Lean decision code above and the three hosts. Fixed on `wip/xhr`:

1. DNS rebinding (a public name resolving to a private address) was open: now pinned.
2. A method-override field naming a forbidden method (`X-HTTP-Method-Override: TRACE`)
   reached the wire: `setRequestHeader` ignores it, and `mainWire` drops it as well.
3. `Authorization` was kept on a cross-origin redirect: dropped (Fetch §4.4 step 13).
4. A cross-origin redirect to a URL with credentials was followed: now a network error.
5. On the Hub, a final URL outside the policy (a redirect to a local address) was read:
   now withheld. The request itself was made by then; the Hub browser's own rules decide
   whether it can be.

Open:

- Hub, sync requests: the Hub's sync path uses the Hub browser's `XMLHttpRequest`, which
  sends the Hub origin's cookies on a request to the Hub's own origin (no way to omit
  them on a sync request). The Hub's origin is a static site with no session cookies; a
  page can also read the Hub's own public files, since that browser sees the request as
  same-origin and the engine's CORS is off there.
- Hub, a response body is read whole before the 64 MiB check (memory only).
- Desktop: `Deno.resolveDns` asks the system's name servers, not the hosts file, so a name
  only in the hosts file does not resolve for a page that is not local (fails closed).
- The pin is per transfer: two requests to one name may get different public addresses.
