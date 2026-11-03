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
  `tests/misc`, `tests/sandp`, `tests/type`, unchanged, with these
  exceptions:
  - `tests/strm` and `tests/attr/streamable` were first left out
    (XSLT 4.0 stage 1, https://github.com/danbri/factoidal-core/pull/208).
    They were copied on 2026-10-28 from the same commit `91328fbf`, for
    XSLT Streaming 4.0 (branch `claude/qt4-xslt-streaming`), unchanged,
    except `tests/strm/docs/city-list.json` (19 MB; no streaming test set
    reads it). Size: 27 MB (`tests/strm`) and 14 MB
    (`tests/attr/streamable`).
  - `tests/misc/docbook` (52 MB) and `tests/misc/unicode-90` (117 MB):
    size.
  - `tests/fn/json-to-xml` (24 MB) and `tests/strm/docs/city-list.json`
    (19 MB): size.

The runner (`formal/lean4/Harness/Xslt4Run.lean`, `lake exe l4xslt4`)
skips a test set whose file is not present, so the scores cover the copied
test sets only. Size of the copy: about 110 MB.

## Use

    cd formal/lean4
    ulimit -s 65520
    lake build l4xslt4
    .lake/build/bin/l4xslt4 --isolate 120

The data is untrusted input: stylesheets are run only by the Lean XSLT 4.0
processor, which does no I/O; the runner reads files under this directory
only.
