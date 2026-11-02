# 0.29 release: public version pins

Date: 2026-11-02.

Review of https://github.com/danbri/factoidal-core/pull/294 (0.29 release)
found that the candidate changed public CDN references to 0.29.0 before npm
publication. Public pages must continue to load the published 0.28.0 package
until the release manager confirms publication.

The following five files are restored to their `origin/main` content
(`a1f74d74430b`), including all current pipeline support:

- `docs/_data/factoidalRelease.js`
- `docs/_includes/hub-app.njk`
- `docs/web/hub/data-compositor/app.mjs`
- `docs/web/hub/data-compositor/index.njk`
- `docs/web/hub/data-compositor/worker.mjs`

Package metadata, version constants and the changelog stay at 0.29.0.
Stamped `npm/*/version.json` files from the checked build installation stay
unstaged, as required by `skills/npm-release/SKILL.md`.

Validation: Node 22 ran `node --test tests/hub/compositor_page_test.mjs`:
1 pass, 0 fail, 0 skipped. This test performs a real bounded Eleventy build
and checks the published package URL, worker version guard, pipeline files,
FOAF pod controls, runtime passthroughs and Pages prefix. The existing test
expects 0.28.0 and passes with these public pins.

A separate local patch, `/tmp/factoidal-029-postpublish-pins.patch`, restores
the five public files to 0.29.0 and changes the page test to read the expected
version and browser URL from `docs/_data/factoidalRelease.js`.
`git apply --check` passes against this checkout. The patch is prepared only;
it must be applied after the release manager confirms npm publication.
The test change removes the stale 0.28.0 literals that otherwise fail the
next site build. This patch does not claim to test CDN delivery.
