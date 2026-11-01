# web-platform-tests HTML tree construction tests: provenance

- Source: https://github.com/web-platform-tests/wpt, branch `master`, commit
  `ce5ca39646886a9349fc42913f843ec6e1c8a36f` (2026-10-28), the same commit as
  `third_party/testing/wpt-encoding` and `third_party/testing/wpt-url`.
- Copied unchanged into `third_party/testing/wpt-html-parsing/html/syntax/parsing/resources/`:
  the 62 `.dat` files and `README.md` (the html5lib tree construction format);
  the repository `LICENSE.md`. The `html5lib_*.html` wrappers that run the
  same files in a browser are not copied; `tests/html5lib/run.sh` reads the
  `.dat` files directly.
- Copied on 2026-10-29.
- Specification under test: HTML Living Standard, whatwg/html commit
  `939677714df7379fee3667040113b41c91c851e7` (2026-10-26), §13.2 and §13.4.
- Licence: 3-Clause BSD (`LICENSE.md`).
- Runner: `tests/html5lib/run.sh` (`lake exe l4html5lib tree`).
