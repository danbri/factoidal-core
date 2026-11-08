# web-platform-tests for page scripts: provenance

- Source: https://github.com/web-platform-tests/wpt, branch `master`, commit
  `ce5ca39646886a9349fc42913f843ec6e1c8a36f` (2026-10-28), the same commit as
  `third_party/testing/wpt-encoding`, `wpt-url` and `wpt-html-parsing`.
- Copied unchanged into `third_party/testing/wpt-scripting/`, at their WPT paths:
  - the files of `html/webappapis/timers/`, `html/webappapis/microtask-queuing/`,
    `dom/events/`, `dom/nodes/` and `html/webappapis/scripting/event-loops/`, with
    their `resources/` and `support/` folders (not other subfolders, such as
    `crashtests/` or `moveBefore/`);
  - `resources/testharness.js`, `resources/testdriver.js`,
    `resources/testdriver-actions.js`, `resources/testdriver-vendor.js`;
  - `dom/common.js`, `dom/constants.js`, `common/dummy.xml`, `common/dummy.xhtml`;
  - the repository `LICENSE.md`.
- Added on 2026-11-08 for the DOM breadth work (Range, Selection, traversal, markup
  setters, reflection, getComputedStyle), from the same commit `ce5ca396`, unchanged:
  - `dom/ranges/` (without `crashtests/` and `tentative/`), `dom/traversal/` (without
    `unfinished/`, with `support/`);
  - the files of `selection/` (not its subfolders);
  - from `html/dom/`: `reflection-*.html`, `reflection.js`, `elements-*.js`,
    `original-harness.js`, `new-harness.js`;
  - the files of `domparsing/`, with `domparsing/resources/`;
  - from `css/cssom/`: `getComputedStyle*` and `support/`.
- Not copied: WPT's `resources/testharnessreport.js`. The runner serves this
  repository's own `tests/browser-wpt/testharnessreport.js` in its place, as every WPT
  runner supplies its own.
- Copied on 2026-11-08.
- Licence: 3-Clause BSD (`LICENSE.md`).
- Runner: `tests/browser-wpt/testharness-run.ts` (page scripts run by Lean in the
  Foafnaut engine; record `docs/designissues/2026-11-08-page-scripts.md`).
