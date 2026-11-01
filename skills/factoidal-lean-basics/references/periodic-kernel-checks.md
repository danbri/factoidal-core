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
