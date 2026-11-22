# EVM GASPRICE and post-Merge PREVRANDAO — 22 November 2026

Issue: https://github.com/danbri/factoidal-core/issues/781
Execution-client goal: https://github.com/danbri/factoidal-core/issues/652
Full Ethereum goal: https://github.com/danbri/factoidal-core/issues/725

## Source contract

This update is stacked on draft PR #775, not merged into main. The actual
`Core.planStep` instruction dispatcher reads these additional supplied fields:

- `GASPRICE (0x3a)` reads `State.effectiveGasPrice`. It is the **effective**
  transaction gas price; it must not be confused with a type-2 transaction's
  `maxFeePerGas`. The runner does not decode/sign/recover any transaction
  to derive this field. It charges two gas through ordinary `commit`.
- `DIFFICULTY/PREVRANDAO (0x44)` returns the supplied 256-bit post-Merge
  `State.blockPrevRandao` and charges two gas on Shanghai+ and Osaka
  profiles. The old `preShanghai` selector covers both sides of the Merge
  and therefore returns `unsupportedFork` instead of emitting a potentially
  wrong historical value.

`World.frameInput` passes both fields from `TxWorld` into ordinary and
nested-call frames. The synthetic `--tx-env` CLI takes
`HEX GAS FUEL EFFECTIVE_GAS_PRICE PREVRANDAO`; both values must be
less than 2^256. This CLI does not authenticate input provenance.

Normative references: [EIP-1559](https://eips.ethereum.org/EIPS/eip-1559)
requires GASPRICE to return the effective gas price, not the fee cap.
[EIP-4399](https://eips.ethereum.org/EIPS/eip-4399) retains opcode 0x44,
changes its return value at the PoS transition to the header mixHash, and
leaves the gas cost unchanged. The current coarse preShanghai profile is
not precise enough to select either historical branch of that transition.

## Intended machine-checked statements

- `EVMCleanroom.step_effectiveGasPrice`: for a running state at GASPRICE,
  the actual `step` equals the common `commit` with the field value and 2 gas.
- `EVMCleanroom.step_prevRandao`: for a running Shanghai+/Osaka state
  at opcode 0x44, the actual `step` equals that commit with prevRandao.
- `EVMCleanroom.step_prevRandao_unknown_fork`: for the ambiguous old
  selector the same reached opcode refuses `unsupportedFork`.
- `EVMCleanroom.World.frameInput_feeAndRandao`: the executable frame
  projection preserves both supplied fields for all arguments.

These are **local implementation theorems**. They do not establish correctness
of effective gas-price calculation, canonical block header selection,
beacon-generated randomness, fork choice, consensus, or normative EELS
refinement. The compiler's actual `#print axioms` output is a separate
pass/fail gate; the expected new sets are `[propext]`, `[propext]`,
`[propext]` and `[]`. They are *not* claimed as checked until
the current-head Linux job actually passes.

## Tests and independent evidence

`EVMCleanroom/Tests.lean` adds seven executable guards for the 256-bit
boundary, gas threshold and old-fork refusal. The independent differential
script `scripts/differential/tx-env.mjs` executes 9 small programs at 5
gas limits each against pinned EthereumJS v10.1.3 Shanghai. It compares
status, error classification, exact remaining gas, complete stack and
allocated memory bytes. It also falsifies price and RANDAO independently:
altering either injected Lean input must be noticed.

Run from `formal/lean4/evm-cleanroom` with pinned Lean 4.33.1 and the
repository's single-build lock:

```sh
lake build
python3 scripts/check-active-ledger.py
python3 scripts/check-axiom-output.py
npm ci --prefix scripts/differential --ignore-scripts --no-audit --no-fund
node scripts/differential/tx-env.mjs
```

The EVM workflow separately requires the full retained 10,000-program
corpus, all earlier differential suites and six Prague/six Cancun EELS
roots. The Frontier workflow requires the authenticated block-46147
intermediate and final roots through two independent checkers. Both suites
must be re-executed on this exact source. No previous green run is
automatically inherited.

## Remaining limits

The real transaction envelopes, signed secp256k1 sender recovery,
EIP-1559 effective-price computation, authenticated header/MPT,
pre-Merge DIFFICULTY activation, CREATE, precompiles, receipts,
full block validation, Engine API, node security and Lean beacon
consensus remain open. The measured performance-tail regression
continues under https://github.com/danbri/factoidal-core/issues/739.
No local before/after timing can be established from this GitHub-only
authoring environment.
