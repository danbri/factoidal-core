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

## Prepared publication update

The isolated branch `codex/release-0.29.0-public-pins`, based on
`8fcf8d787a55cf26ab8e561798a5662e0f40e7d7`, contains the prepared update.
Its five public files name 0.29.0; the page test reads the expected version
and browser URL from `factoidalRelease.js`. The release candidate keeps the
published 0.28.0 pins. This branch waits for actual npm registry availability
of `@factoidal/core@0.29.0` before its changes can reach the public site.

Validation on this branch: Node 22 ran the actual
`tests/hub/compositor_page_test.mjs`, including its bounded Eleventy build:
1 pass, 0 fail, 0 skipped. The build uses the candidate checkout's installed
Eleventy dependencies through a temporary `docs/node_modules` symlink, removed after the test. No
CDN request or npm publication is part of this test.
