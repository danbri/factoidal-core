# web-platform-tests encoding tests: provenance

- Source: https://github.com/web-platform-tests/wpt, branch `master`, commit
  `ce5ca39646886a9349fc42913f843ec6e1c8a36f` (2026-10-28).
- Copied: the directory `encoding/` unchanged, into
  `third_party/testing/wpt-encoding/encoding/`; the two helper scripts that its
  tests load, `common/sab.js` and `common/subset-tests.js`, into
  `third_party/testing/wpt-encoding/common/`; the repository `LICENSE.md`.
  Not copied: `resources/testharness.js` and the rest of the repository. The
  runner gives its own testharness.js-compatible functions.
- Copied on 2026-10-29.
- Specification under test: Encoding Standard (WHATWG Living Standard),
  commit `be17ac5c49881336538acfc7b40dba3c8009144b` of https://github.com/whatwg/encoding
  (the resources of that commit are in `third_party/whatwg-encoding/`).
- Licence: 3-Clause BSD (`LICENSE.md`).
- Runner: `tests/whatwg-encoding/run.sh` (builds `lake exe l4whatwg-encoding`,
  then `tests/whatwg-encoding/run.mjs`). Files that need surfaces the runner
  does not give: https://github.com/danbri/factoidal/issues/1184.
