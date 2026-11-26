# Cancun EIP-7516 BLOBBASEFEE — 22 November 2026

Issue: https://github.com/danbri/factoidal-core/issues/790
Full Ethereum goal: https://github.com/danbri/factoidal-core/issues/725
Base: `f541d27f8d88da96269ce2a0833e111aa6728821` (draft PR #783).

The new `cancunPlus` opcode profile separates Cancun-gated BLOBBASEFEE from the coarse `shanghaiPlus` profile. It is NOT a fork-complete Cancun interpreter. Actual `Core.step` handles opcode `0x4a` with a two-gas commit under Cancun/Osaka, or explicitly refuses historical profiles. `World.frameInput` projects the transaction world's synthetic blob fee into nested child execution. The actual dispatcher theorems are `step_blobBaseFee_cancun`, `step_blobBaseFee_osaka`, `step_blobBaseFee_unknown_fork`; world projection is `World.frameInput_blobBaseFee`.

The fee is externally supplied; there is no verified `fake_exponential` (EIP-4844), excess blob gas, BPO pricing, authenticated header, transaction signature or beacon state. These four local theorem claims do not prove normative Ethereum equivalence. The new differential feeds the same synthetic 7 wei fee to EthereumJS 10.1.3 Cancun via its header hook and to the Lean CLI, observing stack, gas, status and memory for 42 programs, with fake-fee/fake-gas controls and an old-profile refusal. Status is conditional on exact-head CI; do not count it as passed until logged.

Reproduction from the `formal/lean4/evm-cleanroom` Lake project (pinned Lean 4.33.1):
```sh
lake build
lake exe evm-subset --blobbasefee 4a00 100 60 7 cancun
lake exe evm-subset --blobbasefee 4a00 100 60 7 shanghai
npm ci --prefix scripts/differential --ignore-scripts --no-audit --no-fund
node scripts/differential/blob-base-fee.mjs
python3 scripts/check-active-ledger.py
python3 scripts/check-axiom-output.py
```

Remaining: fork-exact pricing and spec refinement, BLOBHASH/KZG, all envelopes, CREATE, all precompiles, block/state-trie verification, Engine API, persistence and Lean beacon consensus. The measured legacy performance regression remains https://github.com/danbri/factoidal-core/issues/739. No native before/after timing was possible in the source-editing environment.
