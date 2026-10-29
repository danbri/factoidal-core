# XQuery 4.0 merge validation (2026-10-29)

Task: merge the current `origin/main` into the XQuery 4.0 branch without
losing either implementation. Tracking: https://github.com/danbri/factoidal/issues/1101
(QT4 staged implementation). The baseline is in `PR-INFO.md`.

Resolved the eight conflicted files. Kept both runner imports, feature sets,
provenance entries and recursion allow-lists. The six Update namespace
exclusions became stale: the branch's indentation-aware XML assertion
comparison accepts them. They now count as ordinary passes. Kept the branch's namespace
tracking through the parser context: it already carries the enclosing direct
constructor declarations that main passed as an extra argument.

Combined rich function annotations and lazy defaults with updating-function
metadata. The Update query entry point also needs imported-type loading,
function lookup and post-binding context-type checks from the XQuery entry
point. Its static checker must inspect the function inside the annotation
wrapper.

Only `l4qt4` is built. Commands and final measurements are recorded in
[MERGE-REPORT.md](../MERGE-REPORT.md). No commit, push or network command is used.

The runner writes progress files named only by test set under `TMPDIR`.
Initial runs reported interrupted sets; a direct repeat of `fn-path` gave
69 pass, 0 fail and 3 unsupported. Final runs use separate temporary
directories to avoid collisions with other runner processes. A collision
was a possible cause, not confirmed by process inspection (sandbox denied it).

The completed family measurements give 45858 pass, 618 fail, 1148 unsupported
for the 12 original families (25 excluded), and 798 pass, 0 fail,
27 unsupported for Update. Each original family matches or exceeds its PR
baseline. Isolated runs still had intermittent interruptions with separate
temporary directories; the report includes their raw totals and the direct
production-family repeat. The interruption cause remains unresolved.
