# EVM block-environment opcode slice — 22 November 2026

## Scope and intended theorems

Parent: [full Ethereum goal](https://github.com/danbri/factoidal-core/issues/725).
[Execution client](https://github.com/danbri/factoidal-core/issues/652).
[Implementation issue](https://github.com/danbri/factoidal-core/issues/774).

Implement COINBASE (0x41), TIMESTAMP (0x42), NUMBER (0x43),
GASLIMIT (0x45), and BASEFEE (0x48) through the existing Lean
`Core.planStep → commit → step` path, each charging two gas.
The new `World.frameInput_blockEnvironment` theorem connects the five
supplied transaction-world fields to the actual frame projection used by
nested CALL. Six actual opcode dispatcher/refusal theorems connect the
instruction to the charged commit, stack and fork selection.

The EELS/Frontier-to-Osaka fork-specific block-header validity relation is
**not proved**. In particular, BASEFEE is defined since London; the coarse
`preShanghai` profile includes both pre- and post-London blocks, so it
refuses to interpret BASEFEE. DIFFICULTY/PREVRANDAO (0x44) and
BLOCKHASH (0x40) remain unimplemented and will require fork-specific rules,
authenticated historical headers and/or consensus context.

## Reproduction

Using pinned Lean 4.33.1 and the repository build lock:

```sh
cd formal/lean4/evm-cleanroom
lake build
python3 scripts/check-active-ledger.py
python3 scripts/check-axiom-output.py
npm ci --prefix scripts/differential --ignore-scripts --no-audit --no-fund
node scripts/differential/block-environment.mjs
lake exe evm-subset --block-env 414243454800 200 60 4660 1700000000 19000000 30000000 1234567890
```

The `--block-env` command accepts a synthetic header, not a block RLP or
network provider. It refuses input above a 160-bit beneficiary or 256-bit
header fields. The differential uses an independent EthereumJS Shanghai
execution of the same bytecode with a synthetic header. Compare status,
gas, full stack, memory and return category. An intentionally changed
timestamp must be detected. All underlying source files and theorem
axiom lists are pinned by the active evidence ledger.

## Proof and trust limits

The new dispatcher theorems state exactly how the executable Lean code
uses supplied context. They cannot authenticate that context, reproduce
canonical chain selection, establish an EELS independent semantic
refinement theorem, check a block hash, validate signatures or replay
general mainnet transactions.

Existing call, witness, Prague/Cancun state-root, RPC and differential
gates must all be rerun on this exact source. No earlier CI run proves
this change. Remote hosted results and any observed performance change
are recorded separately. The previously observed tail latency remains
under [issue #739](https://github.com/danbri/factoidal-core/issues/739).
