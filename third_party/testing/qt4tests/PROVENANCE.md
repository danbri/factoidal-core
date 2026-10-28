# qt4tests (partial copy)

Source: https://github.com/qt4cg/qt4tests
Commit: b39c4bc027a56c82407f479709bc59e2122be5fc (committed 2026-10-27T11:18:42+01:00)
Copied: 2026-10-27, from a `git clone --depth 1` of that commit, files unchanged.

What was copied (and nothing else):

- `catalog.xml` (the test-set list and the shared environments)
- `README.md`
- `prod/`, `op/`, `fn/`, `map/`, `array/`, `math/` (the test-set families that
  Stage 1 of https://github.com/danbri/factoidal/issues/1101 scores)
- `docs/` (the source documents and schemas that the catalog environments
  refer to)
- `bin/` and `file/` (the EXPath Binary 4.0 and EXPath File 4.0 test sets,
  with the `file/sandpit` directory), copied 2026-10-28 from the same commit
  for https://github.com/danbri/factoidal/issues/1101 (EXPath stage)

Added 2026-10-28 for the XQuery 4.0 mode of the runner
(https://github.com/danbri/factoidal/issues/1101), from a
`git checkout` of the same commit, files unchanged:

- `app/` (use cases, FunctX, the specification examples, XMark, ...)
- `misc/` (keyword, error-code, focus, higher-order, JSON, HTML,
  JSONPath, JMESPath and collation suites)

Added 2026-10-28 for the XQuery Update Facility
(https://github.com/danbri/factoidal/issues/1101), from a `git checkout` of
the same commit (b39c4bc0; `upd/` is the same at b1616b79):

- `upd/` (40 test sets, 825 test cases, with `TestSources/` and
  `LibraryModules/`). The upstream `upd/TestSources/CVS/` directory (CVS
  metadata, no test data) is not copied; every other file is unchanged.

Not copied: `ft/`, `ser/`, `xs/`, the drivers, tools, viewer and
guide. A catalog test set whose file is not
present is not run by `lake exe l4qt4` unless its family is selected.

Licence: the suite is published by the W3C QT4 Community Group under the
W3C test-suite terms that govern its parent qt3tests
(https://www.w3.org/copyright/test-suites-licence/); see the upstream
repository.

The files are test data. The runner (`formal/lean4/Harness/Qt4Run.lean`)
parses them and evaluates their XPath expressions with the project's own
evaluator; nothing in this directory is executed.
