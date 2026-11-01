# Periodic independent Lean checking

Added nightly, resource-aware checking advice to `factoidal-lean-basics` and
linked it from `lean4-proof-patterns`. The shared reference distinguishes
roadmap commands from available tools and requires coverage/version/log evidence.

Read-only availability probe from `formal/lean4/`: `lake --help` reports Lake
5.0.0-src+819816b, Lean 4.33.1, with no `check` command advertised.
No kernel audit, scheduler installation, toolchain upgrade or release gate
change was performed. Scheduling remains future work when supported tools and
an appropriate runner are available.

Follow-up: audit findings must generate visible development messages and
tracked, deduplicated GitHub issues even when CI is advisory. Infra failures
remain distinct from proof rejection. No new checker finding was observed
while making this guidance change, so no incident issue was opened.
