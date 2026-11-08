# WASI Preview 1 witx

Source: https://github.com/WebAssembly/WASI at commit
`9ea0e7534f46f0c39f28b386fa2becf00923a857` (2025-10-28), files
`legacy/preview1/witx/wasi_snapshot_preview1.witx` and
`legacy/preview1/witx/typenames.witx`, and `LICENSE.md`. This is the last commit
on the default branch with these files; the next commit (ce149c9f7, 2025-12-18) moved
the Preview 1 documents to the `wasi-0.1` branch.

| File | sha256 |
|---|---|
| `wasi_snapshot_preview1.witx` | `30e31a9b830d3fad998701fc9439a5506af4dbb8f01202854c8af46d436de679` |
| `typenames.witx` | `e06e9545a1797120b48a666a4ee78c0760ecbc60789690e22d735f0467cb92ed` |
| `LICENSE.md` | `0416590f3f47381bb5b9b467c27824d1228fac58b8031d693130865273ffefcb` |

Licence: `LICENSE.md`. The WASI specification is published by the WebAssembly
Community Group under the W3C Community Contributor License Agreement. These files
are a specification, read by people; nothing is generated from them yet.

Used by: `formal/lean4/L4Factoidal/WasmVM/Wasi.lean` (the WASI Preview 1 host of the
WasmVM engine, issue https://github.com/danbri/factoidal/issues/1244). Its errno
values, the `$fdstat` layout, the `$rights` bit of `fd_write` and the core Wasm type
of each of the 46 functions follow these files. Record:
`docs/designissues/2026-11-07-wasmvm-engine.md`, "WASI Preview 1".
