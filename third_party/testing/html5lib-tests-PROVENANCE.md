# html5lib-tests: provenance

- Source: https://github.com/html5lib/html5lib-tests, branch `master`, commit
  `c777c408b61078ea2eb4acefc2535f54dbc8b28a` (2026-10-01, "Add tokenizer tests for
  processing instructions").
- Copied unchanged into `third_party/testing/html5lib-tests/`: `tokenizer/` (the
  14 `.test` files and `README.md`), `LICENSE`, `AUTHORS.rst`. The tree
  construction tests left this repository on 2026-06-26 (commit `224991ec`,
  "Tree construction tests have moved to WPT"); they are vendored from
  web-platform-tests: `third_party/testing/wpt-html-parsing-PROVENANCE.md`.
- Copied on 2026-10-29.
- Specification under test: HTML Living Standard, whatwg/html commit
  `939677714df7379fee3667040113b41c91c851e7` (2026-10-26), §13.2.
- Licence: MIT (`LICENSE`).
- Runner: `tests/html5lib/run.sh` (`lake exe l4html5lib tokenizer`).
