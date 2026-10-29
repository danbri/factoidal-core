# Full Text and XQuery Update merge (2026-10-29)

The merge keeps both implementations and their runner support. The runner
imports both theorem modules, enables both feature lists, combines the
existing defective-test exclusions, and selects both `ft` and `upd` in
XQuery mode. The runtime imports both Full Text evaluation and Update
revalidation. Both fixture provenance records and all tail-recursion
allow-list entries are retained.

`python3 tools/dataflow-inventory.py` regenerated the inventory from the
merged sources. Its generated `StageKinds.lean` did not change.

`lake build l4qt4` passed. The Full Text XQuery run retains the PR baseline:
675 pass, 0 fail, 0 unsupported (out of 675); 10 excluded (defective test
data). XPath mode reports 0 pass, 0 fail, 685 unsupported (out of 685).

The full XQuery run gives 43946 pass, 1718 fail, 1776 unsupported (out of
47440); 16 excluded. After removing the added Update family, the run has
230 more passes and 23 fewer failures than the PR baseline.

Commands, complete TOTAL lines, and the final comparison are in
[MERGE-REPORT.md](../MERGE-REPORT.md). No commit, push, or network command
was run.
