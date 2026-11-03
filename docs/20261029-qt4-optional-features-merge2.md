# QT4 optional features merge against updated main — 2026-10-29

Parents: HEAD `ff33c0499acf18d2ca386de354c49c72025866d5`,
MERGE_HEAD `3309fbee0b811cee5df26a3d65e15d63fe7cc0aa`.

Resolved eight conflicted files, retaining the optional-feature settings
and main's XQuery, schema, Full Text, and Update support. The module parser
now takes both schema-loading arguments and the XML version setting.
Every environment-aware call passes that setting, including dynamic module
loading and the runner's serialization-parameter and file-sandbox parses.
The runner applies both configureFor and configureUpd. XML parsing retains
XInclude, DTD whitespace handling, and schema validation; document identity
includes the parsing options from both parents.

Kept both parents' runner imports and tail-recursion allow-list entries.
Kept all provenance additions; corrected the historical fn:update paragraph
so it no longer says that the now-present Update family is absent.
The dataflow inventory did not conflict and was not regenerated.

Compare each XQuery family with the better pass count of the previous merge
and current main. Main has the higher count in all 13 families. Also check
Full Text in both modes and the six XPath families from the previous report.
Run each family separately, with a new TMPDIR for every invocation.

Build result, commands, per-family scores and remaining failures:
[merge report](../MERGE-REPORT.md). No index write, commit, push or network
command is authorized for this merge task.

Continuation: the first 21 family runs completed. XQuery `op` and `misc`
fell below the baseline because `op-same-key` and `misc-HtmlTestSuite`
stopped early. Their unfinished cases remain failures in the first logs.
The function comparison also found a merge interaction: main registers
source documents by absolute URI, which caused `fn:doc` to reject DTD
validation before reading the available source text. Non-default parsing
options now read that text; ordinary reads still use the registered
document, including Update changes. The runner registers scanned resources
under their absolute URI as well, so XInclude can retrieve resolved hrefs.
The existing QT4 DTD-property and parse-xml cases exercise these repairs.
Final family runs and the initial interruptions are recorded in the report.

Final result: `lake build l4qt4` passed (361 jobs). All 13 XQuery families
meet the better baseline: 46744 pass, 596 fail, 1109 unsupported out of
48449; 25 excluded. Full Text adds 675 pass, zero fail; 10 excluded.
The six XPath families give 29358 pass, 94 fail, 9222 unsupported out of
38674; 5 excluded. Each invocation used a separate TMPDIR. The final
whole-family op repeat gave 4672 passes (main: 4671); earlier timed-out
runs remain in the report, with their failures counted.

Additional audits: source hygiene passed; module reachability failed on
the incoming XProc UtilitySteps module; the generated-C recursion audit
failed on 39 declarations missing from the allow-list. These broader
failures remain recorded, not waived. The first recursion audit ran while
Lake was replacing generated C and failed to read a file. It was repeated
after the build, and the Lean skill now states that ordering requirement.
No Git index write, commit, push or network command was run.
