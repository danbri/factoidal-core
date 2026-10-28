# xslt40-test (vendored subset)

- Source: https://github.com/qt4cg/xslt40-test (the QT4 Community Group
  XSLT 4.0 test suite, forked from https://github.com/w3c/xslt30-test).
- Commit: `91328fbf0fed4a5d2813eb3661808ee53cb961ba` (2026-10-13), cloned
  2026-10-28.
- Licence: the terms of the upstream repository (W3C test suite terms, as
  for `w3c/xslt30-test`). `readme.md` is the upstream file, unchanged.

## What was copied

- `catalog.xml`, unchanged.
- `tests/attr`, `tests/decl`, `tests/expr`, `tests/fn`, `tests/insn`,
  `tests/misc`, `tests/sandp`, `tests/type`, unchanged, EXCEPT these
  directories, which were not copied:
  - `tests/strm` and `tests/attr/streamable`: XSLT Streaming tests; this
    processor does not stream (the streaming dependency makes them
    unsupported). Seven files under `tests/strm` that non-streaming test
    sets read are copied: `docs/books.xml`, `docs/ot.xml`, `docs/recursive.xml`, `docs/transactions.xml`,
    `si-value-of/si-value-of-100.xml`, `si-value-of/si-value-of-101.xsl`,
    `su-absorbing/su-absorbing-901.xsl`.
  - `tests/misc/docbook` (52 MB) and `tests/misc/unicode-90` (117 MB):
    size.
  - `tests/fn/json-to-xml` (24 MB) and `tests/strm/docs/city-list.json`
    (19 MB): size.

The runner (`formal/lean4/Harness/Xslt4Run.lean`, `lake exe l4xslt4`)
skips a test set whose file is not present, so the scores cover the copied
test sets only. Size of the copy: about 70 MB, 10,700 files.

## Use

    cd formal/lean4
    ulimit -s 65520
    lake build l4xslt4
    .lake/build/bin/l4xslt4 --isolate 120

The data is untrusted input: stylesheets are run only by the Lean XSLT 4.0
processor, which does no I/O; the runner reads files under this directory
only.
