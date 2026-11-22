# EIP-1344 CHAINID in the executable Lean EVM — 22 November 2026

Tracking: [#767](https://github.com/danbri/factoidal-core/issues/767), execution-client [#652](https://github.com/danbri/factoidal-core/issues/652), full EL+CL [#725](https://github.com/danbri/factoidal-core/issues/725).

## Scope of the change

* `Core.State.chainId` is an explicit externally supplied natural number, default zero in synthetic contexts. `Core.planStep` handles opcode `0x46` with a two-gas checked commit and `word chainId` stack result.
* The coarse `Profile.preShanghai` cannot distinguish pre-Istanbul from Istanbul; it refuses CHAINID as `unsupportedFork`. It does **not** report the instruction as an invalid EVM opcode. `shanghaiPlus` and `osaka` admit the instruction. This is an opcode gate, not a historically complete fork schedule.
* The actual world-aware `frameInput` uses `TxWorld.chainId` to initialize `State.chainId`. Call child entry uses this same projection, so nested code sees chain selection even when invoked through the real world-aware execution dispatcher. A dedicated nested execution guard executes CHAINID followed by SSTORE in a child contract.
* The standalone `--chainid HEX GAS FUEL CHAIN_ID` CLI injects the supplied value and executes the real Lean interpreter. It does not infer network identity, parse a transaction envelope, or validate consensus.

## Lean theorem obligations

The source contains `EVMCleanroom.step_chainId`, `EVMCleanroom.step_chainId_unknown_fork`, and `EVMCleanroom.World.frameInput_chainId`. The first is an equality between the *actual Core.step* and its paid `Core.commit` path; the second is an actual dispatcher refusal under the deliberately coarse older profile; the third establishes actual frame projection from a `TxWorld` input.

The active evidence manifest records their expected axiom sets. **Do not mark them checked until the exact current source is compiled with Lean 4.33.1 and `#print axioms` is compared to the manifest.** The visible statement is limited to the supplied chain context, not an independently authenticated chain identity.

## Reproduction

From `formal/lean4/evm-cleanroom`, with the pinned Lean 4.33.1 toolchain and repository build lock:

```bash
lake build EVMCleanroom
lake exe evm-subset --chainid 4600 20 5 1
lake exe evm-subset --chainid 4600 20 5 31337
python3 scripts/check-active-ledger.py
python3 scripts/check-axiom-output.py
npm ci --prefix scripts/differential --ignore-scripts --no-audit --no-fund
node scripts/differential/chain-id.mjs
```

The JavaScript oracle uses pinned `@ethereumjs/evm@10.1.3` with a synthetic Mainnet Shanghai context (chain ID 1). It compares execution status, the full EVM operand stack, allocated memory bytes and size, and remaining gas across 30 cases with varying thresholds and instruction contexts. A false chain-ID negative control must be observed as different. The Lean source also contains direct guards for chain ID zero, one and values above `2^256`, out-of-gas, and preShanghai refusal; a real parent–child CALL guard stores the child's observed chain ID.

## Assurance and outstanding work

The source pins in `evidence/active-claim-manifest-v2.json` are Git blob SHA-1 drift detectors, **not** cryptographic evidence of deployed-chain identity. No transaction signatures, EIP-155 chain-ID extraction, block header authentication, Engine API or beacon-consensus execution are implemented here. CHAINID does not establish the authenticity of top-level ORIGIN/CALLER. The retained EELS fixtures and Frontier replay are selective, not complete fork validation. Official state/block/engine suites, Hive, adversarial replay, client operations, persistence and independent reviews remain required.

The earlier CALL tail-latency regression is separately recorded in [#739](https://github.com/danbri/factoidal-core/issues/739). No new native performance numbers were measured in this authoring environment; no median or percentile parity is claimed. The prior 10,000-program baseline shows median 154.794 to 163.367 ms and maximum/p95/p99 181.091 to 199.809 ms on paired batches. The current PR's historical and performance claims must come from exact-source CI and native measurements, not inherited checks.
