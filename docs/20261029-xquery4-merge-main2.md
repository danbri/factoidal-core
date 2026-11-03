# XQuery 4.0 merge against updated main — 2026-10-29

Merge inputs: HEAD `1b764885907f9fda7444bdecc7fa534f1854687c`, incoming
`2cca3c2455aa8442e31cd2235cda8143bb4ae9f7`.
The comparison baseline is `MERGE-REPORT-1.md`, including its improved
`fn` score and its Update score. Every family is measured separately,
with a new TMPDIR for every invocation. No network or Git index writes.

Resolved 13 files. Kept both Full Text and Update support, imported item
types and schema declarations, both XML comparison paths, and both
provenance and allow-list additions. Kept the earlier removal of six
Update exclusions because those tests pass with the XML comparison fix.
The two FnSchemas source texts were identical; both APIs use one copy.
`docs/dataflow-inventory.md` has no conflict and needs no regeneration.

Build and final measurements: see [merge report](../MERGE-REPORT.md).

The first build found that Full Text added a dispatch condition ahead of
FLWOR evaluation. The existing bridge proof now uses
`String.startsWith_string_eq_false_iff` to prove that `flwor` does not use
that branch. The theorem statement is unchanged. A direct Lean check
passed; the subsequent `lake build l4qt4` passed (353 jobs).

The module reachability gate passed: all 1327 modules are reached from
188 Lake roots. The hygiene audit passed: 0 sorry, user axioms,
native_decide, unsafe, or implemented_by; 163 partial definitions,
unchanged. This source audit does not check imported theorem axioms.

All 13 baseline XQuery families completed separately: 46,681 pass,
593 fail, 1,175 unsupported (48,449 total); 25 excluded. This is 25 more
passes than `MERGE-REPORT-1.md`; no family loses passes. `prod` gains 7,
`fn` gains 14, `app` gains 2 and `xs` gains 2. Other baseline families
are unchanged. Full Text adds 675 pass, 0 fail; 10 excluded. Its XPath
mode has 685 unsupported. The two baseline interruptions (`op-same-key`
and `app-Demos`) remain counted as failures. No other set was interrupted.
Raw TOTAL lines and commands are in the merge report.
