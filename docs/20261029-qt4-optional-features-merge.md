# QT4 optional features: merge validation, 2026-10-29

Tracking: https://github.com/danbri/factoidal/issues/1101 (QT4 specifications and tests).

Resolved the source conflicts in `Harness/Qt4Run.lean` and
`L4Factoidal/XQuery4/Grammar.lean`. The runner keeps both sets of imports,
feature support, per-test settings, update query sequences, and unsupported
diagnostics. The grammar configuration keeps both XML 1.1 and revalidation.

The merged runner evaluates XQuery through `XQueryUpdate.evalUpdQuery`.
That entry point must pass `env.xml11` to `parseModule`. Added that argument
and two build-time checks: a control-character reference is accepted with
XML 1.1 and rejected with XQST0090 with XML 1.0.

Only `l4qt4` was built. The final build succeeded (283 jobs).
The allow-list contains every line from both parents. The runner contains
every import from both parents. The provenance record keeps the earlier
entries and adds the Update fixtures; its old “not copied” list correctly
no longer names `upd/`. The dataflow inventory had no conflict.

See [MERGE-REPORT.md](../MERGE-REPORT.md) for commands, measured totals,
comparison limits, and the sandbox restriction on staging. No commit,
push, or network command was run.
