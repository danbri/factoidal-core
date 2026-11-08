# web-platform-tests web API tests: provenance

- Source: https://github.com/web-platform-tests/wpt, branch `master`, commit
  `ce5ca39646886a9349fc42913f843ec6e1c8a36f` (2026-10-28), the same commit as
  `third_party/testing/wpt-scripting`, `wpt-encoding` and `wpt-url`.
- Copied unchanged into `third_party/testing/wpt-webapis/`: the directories
  `WebCryptoAPI/`, `html/webappapis/atob/`, `html/webappapis/structured-clone/` and
  `user-timing/`; the helpers their tests load from `common/` that the other pinned
  copies do not have (`common/gc.js`, `common/performance-timeline-utils.js`); the
  repository `LICENSE.md`. Not copied: the `WEB_FEATURES.yml` metadata files.
- Copied on 2026-11-08.
- Specifications under test: Web Cryptography API (W3C), HTML (WHATWG) section 8.3
  (base64 utility methods) and section 2.7 (safe passing of structured data), User
  Timing (W3C).
- Licence: 3-Clause BSD (`LICENSE.md`).
- Runner: `tests/browser-wpt/testharness-run.ts --dirs WebCryptoAPI,...`; the runner
  reads all pinned copies as one tree (a path is in the first copy that has it).
