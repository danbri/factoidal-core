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
