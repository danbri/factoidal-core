# qt4tests (partial copy)

Source: https://github.com/qt4cg/qt4tests
Commit: b1616b79c7300167c79a8b0790ba79b5e0b7080d (committed 2026-10-28T14:34:07Z,
the deploy of qtspecs 3e9f3bddd38f39f8953750306f0c574a2fbd0387)
Copied: 2026-10-27 from b39c4bc027a56c82407f479709bc59e2122be5fc (committed
2026-10-27T11:18:42+01:00), from a `git clone --depth 1` of that commit, files
unchanged; updated 2026-10-28 to b1616b79: the 19 test-set files that changed
between the two commits were copied unchanged (the simple and labeled record
types of qtspecs PR 2979, the options of fn:collection and fn:uri-collection of
PR 2918, order by with empty greatest, and the specification examples).
`catalog.xml` and `docs/` are the same at both commits.

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

Added 2026-10-28 for Serialization 4.0 and the XSD type tests of the XPath
mode (https://github.com/danbri/factoidal/issues/1101), from a `git checkout`
of the same commit, files unchanged:

- `ser/` (Serialization 4.0)
- `xs/` (XML Schema types: `xs:numeric`, `xs:error`, constructors)

Not copied: `ft/` (Full Text) and `upd/` (XQuery Update), which are separate
specifications that https://qt4cg.org/ does not publish; the drivers, tools, viewer and
guide. A catalog test set whose file is not
present is not run by `lake exe l4qt4` unless its family is selected.

Licence: the suite is published by the W3C QT4 Community Group under the
W3C test-suite terms that govern its parent qt3tests
(https://www.w3.org/copyright/test-suites-licence/); see the upstream
repository.

The files are test data. The runner (`formal/lean4/Harness/Qt4Run.lean`)
parses them and evaluates their XPath expressions with the project's own
evaluator; nothing in this directory is executed.

Added 2026-10-28 for the `fn:update` tests of `fn/update.xml` (they read
their source documents from `../upd/TestSources/`), from
`https://raw.githubusercontent.com/qt4cg/qt4tests/b1616b79c7300167c79a8b0790ba79b5e0b7080d/upd/TestSources/`,
files unchanged; only the 11 files that `fn/` names (the XQuery Update
Facility test sets of `upd/` are not copied: that specification is out of
scope, https://github.com/danbri/factoidal/issues/1101):

- `upd/TestSources/`: `TopMany.xml`, `books.xml`, `books2.xml`,
  `employeesNIST.xml`, `emptydoc.xml`, `grant.xml`, `items.xml`,
  `part-tree.xml`, `users.xml`, `users2.xml`, `works-mod.xml`
