# web-platform-tests css/css-tables, with the support files it references

- Source: https://github.com/web-platform-tests/wpt, commit
  `28c152b74f8679534e558745fe83312c8dcca8c8` (committed 2026-11-07T12:23:16Z).
  Directory: https://github.com/web-platform-tests/wpt/tree/28c152b74f8679534e558745fe83312c8dcca8c8/css/css-tables
- Copied on 2026-11-07, file by file from raw.githubusercontent.com at that commit.
  Each file was checked against the Git blob SHA-1 in the upstream tree.
- Files are unchanged and keep their WPT paths, so that root-relative links in the
  tests (`/fonts/ahem.css`, `/resources/testharness.js`, `../reference/...`) resolve
  inside this directory when it is served as the root.
- 474 files from WPT, 2.3 MB:
  - `css/css-tables/`: all 456 files of the directory (685,939 bytes).
  - 17 files outside it that the tests link to: `common/blank.html`,
    `common/reftest-wait.js`, `common/rendering-utils.js`,
    `css/reference/ref-filled-green-100px-square-only.html`,
    `css/reference/ref-filled-green-100px-square.xht`,
    `css/reference/ref-filled-green-200px-square.html`,
    `css/support/blue32x32.ico`, `css/support/cat.png`,
    `css/support/computed-testcommon.js`, `css/support/inheritance-testcommon.js`,
    `css/support/interpolation-testcommon.js`, `css/support/parsing-testcommon.js`,
    `fonts/ahem.css`, `fonts/Ahem.ttf`, `resources/check-layout-th.js`,
    `resources/testharness.js`, `resources/testharnessreport.js`.
    Files that those scripts load at run time are not copied (the runner does not run scripts).
  - `LICENSE.md`, the repository licence.
- `SHA256SUMS` lists the SHA-256 of each of the 474 files (`shasum -a 256 -c SHA256SUMS`).
  This README and `SHA256SUMS` are ours, not WPT's.
- Tests: 356 by WPT's manifest rules (files named `-ref`, `-notref`, or in
  `support/`, `tools/` or `reference/` folders are not tests): 169 reftests,
  4 print reftests, 141 testharness.js tests, 42 crash tests.

## Licences

- WPT: 3-Clause BSD, `LICENSE.md` ("Copyright © web-platform-tests contributors").
- `fonts/Ahem.ttf`: the font's own name table (name ID 0, copyright) says: "The Ahem
  font belongs to the public domain. In jurisdictions that do not recognize public
  domain ownership of these files, the following Creative Commons Zero declaration
  applies: http://labs.creativecommons.org/licenses/zero-waive/1.0/us/legalcode".
  Its licence URL (name ID 14) is http://dev.w3.org/CSS/fonts/ahem/COPYING. WPT has no
  separate licence file for Ahem at this commit; `fonts/README.md` and
  `docs/writing-tests/ahem.md` describe the font but do not state a licence, and the
  docs point to https://www.w3.org/Style/CSS/Test/Fonts/Ahem/README. Version 1.50,
  SHA-256 `b719ecb31c5b21fc573c03f6421c74ac63c271a5a3ff841e34f9705fb94b8448`.

## Use

- `tools/render-dashboard/wpt_tables_classify.py` lists the tests, their kinds and
  the CSS features each reftest uses (`tools/render-dashboard/wpt-tables-classes.json`).
- `tools/render-dashboard/wpt_tables.ts` renders each reftest and its reference with
  the Foafnaut engine at 800x600 and compares the GPU pixels.
