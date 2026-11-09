# Foafnaut developer proxy

**This is a development tool for tests. It is not a user feature and not part of the browser.**

EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.

The proxy saves a real page and its resources once (WARC 1.1, ISO 28500) and then replays them offline. Tests are fast, repeatable and independent of live sites. Tracking: https://github.com/danbri/factoidal-core/issues/375 (developer proxy).

Node standard library only, plus the `openssl` command. Files: `devproxy.mjs` (the proxy), `services.mjs` (the response services), `foafnaut-through-proxy.sh` (run the browser), `devproxy.test.mjs` (tests: `node --test tools/devproxy/devproxy.test.mjs`).

## Use it

    # Record, then replay, with the browser (the binary needs no change)
    B=.../native-webgpu-html-darwin-arm64
    tools/devproxy/foafnaut-through-proxy.sh --record example-com -- "$B" --offscreen --no-state --url https://example.com/
    tools/devproxy/foafnaut-through-proxy.sh --replay example-com -- "$B" --offscreen --no-state --url https://example.com/

    # The proxy alone
    node tools/devproxy/devproxy.mjs --record NAME --port 8899
    node tools/devproxy/devproxy.mjs --replay NAME --port 8899
    node tools/devproxy/devproxy.mjs --passthrough --port 8899

A `NAME` with no slash is `~/.foafnaut-devproxy/recordings/NAME`. A recording directory holds `recording.warc` and `manifest.json`. `--record` refuses a recording that exists; `--append` adds to it. In a replay the first response to a method and URL is the one served.

The browser reads `HTTP_PROXY`, `HTTPS_PROXY` and `DENO_CERT` in the Deno runtime, so the compiled binary needs no `--allow-env` for them and no change. Measured on 2026-11-09 with the build of `dd0b3ac2f`.

A page that the browser refuses stops the run, and its resources are then not requested. Record such a page at the service you will replay it at: the recording still holds the unchanged page.

    tools/devproxy/foafnaut-through-proxy.sh --record gov-uk --default-service text-css-links -- "$B" --offscreen --no-state --url https://www.gov.uk/

## Replay

Replay matches on the method and the URL (with credential values replaced by `REDACTED`). A miss answers 504 with the header `X-Devproxy: miss` and logs a line. Replay makes no outbound connection and no DNS lookup; a test proves that by trapping `net.Socket.connect` and `dns.lookup` in the proxy process.

A response is stored with its body decoded of chunked framing and with hop-by-hop headers removed, so a record run and a replay give the same status, end-to-end headers and body. The content coding (gzip, br) is stored as received. Set-Cookie is absent from a replay.

## Response services

The request header `X-Foafnaut-Devproxy: <service>` chooses a service. With no header the page is unchanged and there is no added header. `--default-service NAME` sets the service for a client that sends no header. The browser has no Setting for this header yet; a later browser change adds it, and until then `--default-service` chooses the level for the browser.

The ladder is the table `SERVICES` at the top of `services.mjs`:

- `full`: no change.
- `no-scripts`: removes script elements and `on*` event attributes.
- `text-css-links`: keeps document structure, text, links and stylesheets; removes scripts, iframes, objects, embeds, video, audio, images (with `srcset`, `background`, `poster`), canvas, svg, `javascript:` URLs, `on*` attributes, `meta` refresh and every `link` that is not a stylesheet. It answers 204 for script resources.

Other content types pass unchanged. A service runs at serving time on a copy, so a recording is never changed. The answer carries `X-Foafnaut-Devproxy-Applied: <service>`, and the log gives the counts removed per kind. An unknown service answers 400 with `X-Devproxy: unknown-service`.

The HTML tokenizer follows the WHATWG tokenization rules for comments, tags, attributes, raw text, RCDATA and script data escapes. It does not construct a tree. **It is a test aid. It is not a sanitiser and not a security boundary.** Its output is not safe content. UTF-16 pages pass unchanged with `X-Devproxy: transform-failed`.

## Trust rules

- The proxy binds to 127.0.0.1 only and refuses any other address.
- HTTPS is terminated with a private CA, created on first use in `~/.foafnaut-devproxy/ca/` (directory 0700, key 0600). Its name is `Foafnaut devproxy (pseudo-trusted, development only)` and it is valid for 30 days; a new one is made when less than 2 days remain. Leaf certificates are valid for 7 days. Name constraints are not used because the CA must sign for any host.
- Give this CA only to the process under test (`DENO_CERT`). It is pseudo-trusted: do not put it in any other trust store.
- The key never enters git or a recording. A recording directory inside a git tree is refused, and a recording directory that overlaps the CA directory is refused.
- Upstream connections in record mode verify real certificates with Node's normal trust store. `rejectUnauthorized` stays true, and the proxy refuses to start with `NODE_TLS_REJECT_UNAUTHORIZED=0`. A failed certificate check answers 502 with `X-Devproxy: upstream-tls-failure` and writes a failure record.
- Recordings are private (directory 0700, files 0600) and stay outside the repository. Never commit a real recording.
- `Authorization`, `Cookie`, `Set-Cookie` and similar headers are removed before storage and are not hashed. Token query parameters have their values replaced in stored URLs, in `Location`, `Referer` and `Content-Location` values, in manifests and in the log. Request bodies are not stored; only their length is. Response bodies are stored as received and may hold personal data or tokens, so record only public pages with no login.

Each response record has a `WARC-Payload-Digest` (SHA-256), and replay checks each record's block digest. The manifest gives the URL, status, time, SHA-256 and a TLS summary per exchange; `metadata` records hold the remote address, timing and, once per leaf certificate, the certificate chain in DER. `Foafnaut-*` WARC fields are extension fields.

## Not supported

The first three items have expected-failure tests in `devproxy.test.mjs` that turn the run red when they start to pass; see https://github.com/danbri/factoidal-core/issues/375 (developer proxy).

- WebSocket and other upgrades (answer 501).
- Origins that speak only HTTP/2. The proxy speaks HTTP/1.1 on both sides.
- Replay that distinguishes requests by body: the match is the method and URL only.
- Other limits, with no test: 64 MiB per body; responses are buffered, so streaming media is not suited; a failed upstream at record time is a miss at replay; no upstream proxy; 103 Early Hints and trailers are dropped.

## Feature combinations (https://github.com/danbri/factoidal/issues/1120)

Answers to the gate in section 5 of `docs/designissues/2026-10-28-feature-combination-safety.md`. The proxy is a listener and an outbound requester, off by default in the sense that nothing starts it except a developer. The invariants are enforced in JavaScript in this tool and no Lean theorem covers them; the tests below are the check.

- I3 (a credential goes only to its destination): a client's credential headers go to the origin of the request URL only. No stored form holds them. Test: "credentials are absent from the WARC and the manifest".
- I5 (outbound URLs chosen by a remote party): the page under test chooses URLs. In record and passthrough modes a private, loopback or link-local target is refused with 403 and `X-Devproxy: refused-private` (literal addresses and DNS answers), unless `--dangerously-allow-private-upstream` is given, which warns at start. Replay has no outbound path. Tests: "the CA is private ...", "a miss is 504 ...".
- I7 (a listener without authentication): the listener takes only absolute-form `http://` targets and `CONNECT`. A request as a web page can send it (origin form) answers 400. There is no login on the listener; any local process can use it while it runs. Test: "a request that is not a proxy request is refused", "refuses a non-loopback bind".
- I10 (records hold no credentials): as for I3; also the recording directory rules above. Tests: "credentials are absent ...", "a recording in a git tree is refused".
- I13 (limits per requester): the listener is local and has one kind of requester. The body limit is global and has no test.
- I1, I2, I4, I6: do not apply; the proxy has no storage access decision, login, identity or bearer scope of its own.

Records (gate item 8): the retrieval details are those of CLAUDE.md "Network retrieval goes into the evidence record, as high-risk data": headers without credentials, remote address, timing, TLS version and cipher, key exchange, ALPN, SNI, the certificate chain in DER. No session keys, no client certificates, no local address.
