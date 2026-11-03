# 2026-11-03 — LWS with large bodies: how bulky, and under pressure

Owner, 2026-11-03, verbatim: "Give me guidance on how bulky we can get (per item, per storage)
and how it may perform under pressure. I'm concerned that folk will start stashing media files
there until everything suddenly crumbles."

Issue: https://github.com/danbri/factoidal/issues/1240 (the limits, quotas and streaming to build).

## Measured

`node tests/lws/large-bodies.mjs`, macOS, wasm in Node, `storage: "files"`, sealed under a
storage key, in-process `step`:

| Body | PUT | GET | Process memory (RSS) during |
|---:|---:|---:|---:|
| 1 MiB | 24 ms | 7 ms | +2 MiB |
| 10 MiB | 97 ms | 57 ms | +110 MiB |
| 50 MiB | 422 ms | 303 ms | +480 MiB |
| 100 MiB | 1.2 s | 0.7 s | +1.2 GiB |
| 200 MiB | 6.1 s | 1.8 s | +1.3 GiB |
| 100 × 1 MiB | 67 ms each | | flat |

Small resources: `docs/designissues/2026-10-22-lws-storage-on-disk.md`, stage 2 (4.4 to 5.8 ms
per PUT at 1,000 to 16,000 resources; memory flat).

## Limits today

- No maximum body, no quota, no 413 or 507.
- A whole body goes through the wasm heap, which is capped at 4 GiB per engine and does not shrink.
- One engine is one thread: a large request stalls every other request on that engine (about 1 s
  per 100 MiB).
- The default mode is `snapshot`, which rewrites the whole storage on every write; use
  `storage: "files"` for anything persistent.

## Guidance

- Per item: about 1 MiB or less; up to about 10 MiB now and then; not media.
- Per storage: tens of thousands of resources in files mode (measured flat to 16,000).
- Media: a blob store, with metadata and a link in LWS, until issue 1240's streaming bodies exist.

## 2026-11-03 (evening): a maximum per write (built)

- `L4Factoidal/LWS/Operations.lean`: `Config.maxBody` (default 16 MiB; `"maxBody"` in the storage
  configuration, `openLwsStorage({ maxBody })`). A PUT, POST or PATCH whose content is larger is
  answered 413 and changes nothing: theorem `step_tooLarge`.
- `npm/factoidal/lws/server.mjs`: the HTTP host refuses a declared `Content-Length` over the limit
  without reading the body, and stops reading a chunked body once it passes the limit; 413 either
  way. So an oversized upload never reaches memory whole.
- Tests: `npm/factoidal/test/lws-maxbody.test.mjs` (in-process over and at the limit, the default,
  HTTP declared and chunked). `tests/lws/large-bodies.mjs` sets `maxBody` to 1 GiB, as a measurement.
- Not done (issue 1240): a quota per storage and per agent (507), the files-mode default, chunked
  sealing for media (the LFS-style blobs in the issue), and isolation under pressure.
