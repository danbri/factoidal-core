# ORIGIN and CALLER through actual nested EVM calls — 22 November 2026

Issue: https://github.com/danbri/factoidal-core/issues/760. Execution goal: https://github.com/danbri/factoidal-core/issues/652. Full EL+CL goal: https://github.com/danbri/factoidal-core/issues/725.

Core.step now executes 0x32 ORIGIN and 0x33 CALLER through the same two-gas Core.commit path. World.frameInput accepts explicit origin and caller after its existing profile argument; zero defaults are *synthetic* and not authenticated. The real CallOpcode.beginCall gives the child its immediate caller from active.address and preserves txOrigin from the parent at each depth. Precompiles, CREATE, unimplemented CALL variants and complete transaction signing and environment remain open.

Existing beginCall_entered_context is strengthened by two executable-frame field equalities. New source-connected theorems: step_origin, step_caller and World.frameInput_participants. Expected axiom sets are [propext], [propext], [] respectively; these are not verified until actual Lean 4.33.1 #print axioms on this commit. Four direct guards check exact gas and output; two actual parent→child SSTORE guards check CALLER and inherited ORIGIN in the CALL dispatcher.

The independent pinned EthereumJS Cancun call-context matrix adds 32 CALLER child cases to 128 existing cases. Assert all 160 observed status, child slot0, remaining gas, parent result stack and account balances. The outer reference caller is synthetic; no claim of tx-signature-derived ORIGIN or authenticated prestate is made. Retained independent gates (EELS selected real state roots, Frontier witness replay, 10,000 raw corpus) must re-run after this code change; old passes cannot be counted.

Commands (in correct project workdirs with the repository build lock and Lean 4.33.1): formal/lean4: lake build; formal/lean4/evm-cleanroom: python3 scripts/check-active-ledger.py; python3 scripts/check-axiom-output.py; node scripts/differential/call-context.mjs (with pinned npm dependencies and executable). There is no local Lean compiler or timing runner in the authoring environment. The measured CALL latency tail is still open: https://github.com/danbri/factoidal-core/issues/739.

This is a narrow frame-environment increment, not a claim of full Ethereum execution or consensus conformance.
