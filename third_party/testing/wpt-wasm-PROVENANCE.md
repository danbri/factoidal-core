# web-platform-tests for the WebAssembly JavaScript API: provenance

- Source: https://github.com/web-platform-tests/wpt, branch `master`, commit
  `ce5ca39646886a9349fc42913f843ec6e1c8a36f` (2026-10-28), the same commit as
  `third_party/testing/wpt-scripting`.
- Copied unchanged into `third_party/testing/wpt-wasm/`, at their WPT paths:
  - `wasm/jsapi/` (all files and subfolders);
  - `wasm/resources/load_wasm.js`;
  - the repository `LICENSE.md`.
- Not copied: `wasm/core/` (45 MB of the WebAssembly spec tests as JavaScript). The runner
  reads it from a WPT checkout given with `--wpt-root`; the same files come from the
  WebAssembly spec tests that `third_party/wasm-spec` already holds as JSON.
- Copied on 2026-11-08.
- Licence: 3-Clause BSD (`LICENSE.md`).
- Runner: `tests/browser-wpt/testharness-run.ts --wpt-root third_party/testing/wpt-wasm`
  (record `docs/designissues/2026-11-08-page-wasm.md`).
