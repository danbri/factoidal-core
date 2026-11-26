# EIP-7939 CLZ: first explicit Osaka-only opcode in the Lean EVM

## Exact scope

Ethereum mainnet activated Fusaka (execution-layer fork **Osaka**) on 3 December 2025. The existing official state-root tests in this branch are **Prague empty-code (4/6)** and **Cancun nonempty-code (6/6)**; neither demonstrates Osaka compatibility.

This increment implements precisely **EIP-7939's CLZ opcode (0x1e)** with five gas, using full 256-bit Lean words. The implementation returns 256 for an all-zero word and 255 minus the integer base-2 logarithm otherwise; no JavaScript number conversion is used by Lean. Opcode 0x1e is **only** enabled by an explicit `Profile.osaka` choice, exposed through `--osaka` and `--osaka-batch`. The default `Profile.shanghaiPlus` retains its earlier subset and returns a non-authoritative `unsupportedFork` error on opcode 0x1e.

The word-level theorems `Word.leadingZeros_le` and `Word.leadingZeros_zero` concern the **local mathematical definition**, not independent refinement to Ethereum EELS.

## Run

From `formal/lean4/evm-cleanroom`:

```sh
lake build
# PUSH32 0; CLZ; STOP — result 256, 92 remaining gas from 100
lake exe evm-subset --osaka 7f$(printf '%064d' 0)1e00 100 3
# Without --osaka this opcode is deliberately unsupported.
lake exe evm-subset 7f$(printf '%064d' 0)1e00 100 3
npm ci --prefix scripts/differential --ignore-scripts --no-audit --no-fund
node scripts/differential/osaka-clz.mjs
```

The separate differential runner checks **1,022 distinct full-width operands** (21 hand-chosen boundaries, every bit position 0–255, values immediately below and above powers of two, plus 256 deterministic SHA-256-generated values) under **EthereumJS 10.1.3 `Hardfork.Osaka`** executing actual bytecode `PUSH32 word; CLZ; STOP`. It independently compares the complete result word, exact gas, PC, memory, and an independently written binary-length reference formula. It checks that the default Lean profile does not accept the opcode, that an empty CLZ stack underflows, and that exactly 8 gas succeeds while 7 gas fails. It deliberately falsifies a gas expectation to test the comparator. Every row is a real instruction execution, not a mock of `CLZ`.

## Explicit non-claims

Not an Osaka/Fusaka-complete EVM: no Osaka-wide transaction cap (EIP-7825), secp256r1 precompile (EIP-7951), ModExp repricing, PeerDAS, BPO blob settings, historical fork selection, authenticated tries, full receipts, execution/consensus APIs, general CALL, or mainnet replay. Future **Glamsterdam** repricings must not be silently applied to the currently specified Osaka profile: its Hoodi activation was postponed 22 October 2026 and further security review continues.

The active v2 manifest pins exact new source blobs but keeps its earlier reference CI URL explicitly **historical**, not evidence for this source. The 1,022-case evidence is valid only when **fresh current-head CI** runs green.

## Pinned normative references

- https://eips.ethereum.org/EIPS/eip-7939
- https://eips.ethereum.org/EIPS/eip-7825
- https://blog.ethereum.org/2025/11/06/fusaka-mainnet-announcement
- https://blog.ethereum.org/2026/10/22/glamsterdam-hoodi-delay
- https://blog.ethereum.org/2026/11/06/glamsterdam-8037-8038
