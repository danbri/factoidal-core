# Processor feature settings — 2026-10-29

Task: implement the settings and measurements in `CODEX-BRIEF-SWITCH.md`.
Baseline source: `2210bacb5c67b7b5144469132049dc776c6f60d0`.
No commit or push is authorised for this task.

The input list has 34 dependency entries for 33 distinct test cases.
`fn-transform-902` occurs twice, for the XSLT and XSLT30 features.
The baseline `l4qt4` build passed. Before measurements use that executable,
with one fresh TMPDIR per invocation and `--isolate 60`.
Logs and full command records are in `/tmp/switch-measure/`.

The `fn-load-xquery-module-903` through `914` tests require `FOQM0006`
when dynamic module loading is disabled. The implementation follows these
expectations rather than the brief's general `XPST0017` example.
[F&O 4.0, fn:load-xquery-module](https://qt4cg.org/specifications/xpath-functions-40/#func-load-xquery-module)
specifies `FOQM0006` when use of the function has been disabled.

Implementation and final measurements are recorded in
[SWITCH-REPORT.md](../SWITCH-REPORT.md).

Design and API: [processor feature settings](designissues/2026-10-29-processor-feature-settings.md).

The final build passes all 60 focused checks. Review added checks for
partial applications of disabled callable functions and for XSLT version
restrictions. The Lean hygiene audit reports no new proof escape hatches.
The full-set measurements retain the same failure names. Final family
measurements are recorded in the report.

Final results: all 33 selected cases pass, with no fail or unsupported case.
XQuery fn gains 29 passes, prod gains 4, misc is unchanged; XPath fn gains
29. Every family and full set has the same failure lines as the baseline.
Final build log: `/tmp/switch-measure/implementation-build-6.log`.
No commit or push was made.
