# Periodic independent kernel checking

Owner preference, 2026-11-01: make external checking routine, preferably
nightly when resources permit, rather than on every commit, build or release.
This is an advisory maintenance cadence, not a new mandatory release gate.
A skill entry does not itself install or run a scheduler.

## Availability first

The [Lean FRO roadmap](https://lean-lang.org/fro/roadmap/y4-1/#trust)
announces `lake check`, `lake check <kernel>` (for example nanoda), and
`lake check --paranoid`, plus distribution of comparator. These are roadmap
interfaces: inspect the pinned toolchain's help and documentation before use.
On 2026-11-01 this checkout pins Lean 4.33.1; its `lake --help` does not list
`check`. `check-build`, `check-test` and `check-lint` are different commands
and are not substitutes. Do not upgrade the project or invent a wrapper
merely to make the example commands run.

## Recommended cadence once supported

- Aim for one nightly audit of a recent mainline revision when it changed
  since the last successful audit. Use a separate scheduled CI job or an
  idle machine, not competing heavy jobs on the laptop. Record deferrals;
  sleeping/offline machines and missed nights do not become success.
- Use `lake check --paranoid` if its documented cost fits the budget and
  the intended independent kernels are installed. Otherwise run the official
  recheck nightly and rotate supported alternative kernels, with a periodic
  full check. Record the actual checker set; do not call a one-kernel run
  independent or claim unavailable kernels ran.
- Run Lake commands with explicit working directory `formal/lean4/`.
  Confirm command syntax and export coverage from the installed version.
  Include dependencies and the comparator prelude checks supported by that
  version. Inventory any separate lab modules omitted from the project export.
- Capture source revision (and dirty diff if any), toolchain/checker versions,
  command, covered modules/declarations, omitted scope, UTC time, duration,
  exit status and log location. Ensure a successful run checked nonempty
  intended scope. Preserve diagnostics for failed or incomplete exports.
- Distinguish passed, failed, unavailable, timed out and deferred. A timeout
  or a missing command is not a proof failure, nor a successful check. Investigate
  checker disagreements on the fixed revision before changing dependencies.

Independent checking strengthens evidence that proof terms satisfy the stated
logic. It does not establish that specifications express user intent, that
undeclared assumptions are absent, or that compiled native/WASM/GPU code and
FFI match the proved semantics. Keep axiom audits, semantic tests and artifact
checks; do not disable ordinary kernel checking in builds as a side effect of
this maintenance recommendation.

## Findings must reach people (owner, 2026-11-01)

Non-blocking CI must not mean invisible findings. For a reproducible checker
rejection, disagreement, unexpected axiom/prelude mismatch or missing intended
export scope, search existing issues and file/update a tracked issue in
`danbri/factoidal`. Include exact revision, affected declarations/modules,
checker/toolchain versions, reproduction command, expected/actual result,
coverage and redacted logs. State severity and a concrete next action; link
an upstream Lean issue if one is needed. Do not label an unexplained mismatch
a confirmed kernel vulnerability before triage.

Surface new serious findings promptly in development commentary and the final
report, with the issue URL and affected assurance claim. Put a visible warning
and issue link in the audit job summary even when the job is advisory. Suspend
claims that the affected scope has passed independent checking; do not silently
remove the checker, weaken the theorem, or accept a green build as resolution.
Ordinary missing tools/timeouts get a distinct infrastructure notice; open or
update a deduplicated issue when persistent or when intended coverage is lost.
Avoid nightly duplicate issues and repeated unchanged alerts.

If issue creation fails, retain a local finding with reproduction details and
explicitly tell the user that it is not filed. For potentially exploitable
security defects, redact secrets and use the appropriate private reporting
channel rather than publishing exploit details. This instruction authorizes
issues for findings from these audits; it does not request an issue merely
because the pinned toolchain predates the planned commands.
