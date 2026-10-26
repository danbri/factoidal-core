CI recursion-control fixture repair, 2026-10-22

The reported failure in CI job `120002130666` was reproduced locally:
the recursion audit's self-test passed 10 cases and failed 2. Its temporary
repository omitted `tools/lean-csimp-reach.py`, although the production
recursion gate now invokes that companion. Cases that correctly passed
the first gate therefore failed because the second tool was absent.
[Original local output](ci-tail-selftest-before.log)

Each fixture now includes the actual companion tool and an independent
replacement theorem/caller positive control. The positive control meets
the companion's nonempty-inventory checks. A new stale-caller fixture
passes the recursion classification but must fail the companion gate.
Neither production audit was disabled or edited.

The repaired self-test passes 13 cases with 0 failures. Replacing the
production subprocess call with `rc = 0` in a disposable mutant makes the
new control fail: 12 pass, 1 fail, exit 1. This checks that success cannot
come from bypassing the companion.
[Repaired output](ci-tail-selftest-after.log),
[mutation output](ci-tail-bypass-mutant.log),
[exact mutation and command](ci-tail-bypass-mutant.json)

The real-build compiler-replacement test also requires
`QlvrTool.runSideIndex`, declared in `Harness/Qlvr.lean`. The library and
`l4wasm` build targets do not include that harness. CI now adds
`+Harness.Qlvr` to the existing build command, generating its Lean and C
artifacts without linking the native `l4qlvr` executable. The real caller
assertions remain intact. Missing required modules now produce an
explicit NOT RUN result with exit 2 and the required build command.

Local verification ran no Lean or Wasm build. The compiler-replacement
suite passed 28 synthetic cases with 0 failures. Its default invocation
on this checkout, whose build cache was removed, returned exit 2 and
reported the real-build cases as NOT RUN. CI still has to execute those
cases after the expanded build.
[Synthetic controls](ci-csimp-synthetic-after.log),
[missing-build control](ci-csimp-missing-build-after.log)

[Commands and outcomes](commands.json) and [evidence hashes](sha256.json)
are preserved alongside the logs. Future composed-gate fixtures must
include their subprocess dependencies and a control that rejects bypass;
real emitted-code assertions must name modules present in the CI build.
