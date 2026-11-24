# Consensus build localisation — 24 November 2026

Tracking #872, #844, #848, #868, #725. New owned branch from #869 at
2f6818100fddae970d77bddd7ddaa3aadb84a491, retaining all executable Lean source.

## Observed blocker

Specialised CI on #843 passed. Runs 45246430698 (#845),
45255171564 (#849) and 45324130597 (#869) cancelled during compilation.
Latest job 138209490228 reported successful BasicTypes and StoredHead
builds at 04:07:46 and 04:07:51 UTC, respectively. No ContainerRoots
completion appeared. It was cancelled at 04:27:23 UTC (20-minute job cap).
No container/signing/attestation native or axiom result was produced.
The first blocking declaration is not yet identified.

## Change

The new diagnostic builds BasicTypes, ContainerRoots, SigningDomains and
AttestationData individually with a 120-second wall-time cap, in the same
pinned standalone Lake project. On failure, a 45-second direct check and
bounded prefix search report the last successful and first failing cuts,
command exit status, elapsed time and logs. The diagnostic never converts
a prefix pass or timeout into a theorem pass. A prefix timeout can include
cumulative work; it localises a candidate range, not necessarily a unique
cause. All previous full gate steps remain in place. Existing source,
manifest, Lean toolchain and native implementations are unchanged.

The fixed-container axiom inventory now requires ten actual distinct
printed names, permits only the three foundational axioms, checks the
actual source print declarations, checks 14 source/config paths against
the checkout's HEAD blobs and records the actual printed sets and tree.
It does not predict axiom sets. Existing strict ledgers remain unchanged.

## Local evidence

No Lean runtime or shared Mac worktree is present here. The following
Python script tests ran locally and passed, and the published blob IDs
match the locally tested files exactly:

* check-container-build.py: 5,049 synthetic monotone cut cases and one
  command-boundary case; blob 12c41eb64abb6331a28bf8c0133afd1a39018cb5.
* check-container-root-axioms.py: two synthetic accepted inventories and
  six deliberately corrupted inventories refused; blob
  22634e5b22231de4b4720074fdfe5dd731dff0fb.
* Both scripts passed Python py_compile.

These are diagnostic and comparator tests, not Lean proof results.
Actual module build, printed axiom sets, native differential tests,
and retained regression results remain pending fresh hosted CI.
No dependency changes, main merge, releases or conformance claim.
