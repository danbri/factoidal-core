# Static typing configuration — 2026-10-29

Task: `CONFIG-BRIEF.md`, stream S2, and the 104 cases in `TARGETS.txt`.
Baseline source: `f4c005efc9104d9b733ff3942f6dadc23b1710ac`.
No commit, push or network command is authorized by the brief.

The baseline `lake build l4qt4` passed. All 17 target sets and the `fn`,
`prod` and `upd` families were measured in XPath and XQuery modes before
edits to the executable. Each run used `--isolate 60` and its own TMPDIR.
All 104 selected cases were unsupported in the baseline.

The implementation adds an opt-in static analyser in Lean, shared by XPath,
XQuery and XQuery Update. It reuses the sequence types, subtype relation,
function signatures, schema hooks and existing name checks. The host passes
declared document types; analysis does not infer them from document contents.
Explicit broad annotations remain broad. The default evaluation path has a
definitional agreement theorem.

The soundness theorem connects inference and evaluation for a stated
syntactic fragment. See the [design record](designissues/2026-10-29-static-typing.md)
for its exact coverage and the unproved rules. Full measurements, commands,
test dispositions and remaining failures are in [REPORT.md](../REPORT.md).

Raw measurement logs and command records are in
`docs/test-results/2026-10-29-static-typing/` (generated and ignored by Git).
Build logs are `/tmp/cfg-S2-baseline-build.log` and
`/tmp/cfg-S2-implementation-build*.log`.

The read-only `tools/ensure-test-env.sh --check` reports missing unrelated
W3C, XSD, Xalan, Wycheproof and Solid fixture sentinels. It does not check
QT4. The QT4 catalog and all 104 target test expressions were read directly
from this worktree. No missing fixture was replaced or fetched.

Final result: all 104 targets pass in XQuery mode. XPath passes 48 targets;
the other 56 retain their XQuery-only dependencies and pass in XQuery mode.
The final build checks 84 new guards and the soundness fragment. All 40 final
set/family runs completed. No set or family lost passes, and all pre-existing
failure lines are identical to the baseline. XQuery `upd` is now 819 pass,
0 fail, 0 unsupported (out of 819), with six unchanged defective-data exclusions.

The first target run passed 103 cases. It exposed `XQuery4.runP` resetting
the parser settings, so `stf-delete-001` lost its explicit broad let type.
The grammar now passes `Cfg.features` through that boundary. A public-API
regression guard and the final corpus run both check the repair. The relevant
Lean skill records this failure and the required setting propagation.
