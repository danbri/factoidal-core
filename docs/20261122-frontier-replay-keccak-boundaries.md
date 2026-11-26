# Frontier replay: Keccak boundary correction

Tracks [real-chain replay](https://github.com/danbri/factoidal-core/issues/650)
and [assurance evidence](https://github.com/danbri/factoidal-core/issues/654).

## Verified baseline

[PR 723](https://github.com/danbri/factoidal-core/pull/723), commit
`e59416f5c5cc2a08f7d76e288571e1c28465094c`, passed the
[authenticated replay](https://github.com/danbri/factoidal-core/actions/runs/44995444984)
and [combined EVM workflow](https://github.com/danbri/factoidal-core/actions/runs/44995444945).
The latter includes the signed transaction and target-header commitment gate.
The two state roots for the restricted Frontier transfer at block 46147 were
reconstructed through Lean plus EthereumJS and independently in Python.

## Defect and correction

Review found that the existing Python diagnostic Keccak function padded inputs
of length 135 modulo 136 incorrectly. The domain suffix and final padding bit
must share a single `0x81` byte at that boundary. The original code instead
added another rate block. This did not change the pinned historical replay's
two roots, but it made the oracle incorrect for other input lengths.

The correction fills the final rate block and ORs its last byte with `0x80`.
There is no new crypto dependency or vendored implementation. The 24 committed
known-answer vectors were generated using the authors' [XKCP reference](https://github.com/XKCP/XKCP/blob/master/Standalone/CompactFIPS202/Python/CompactFIPS202.py),
Git blob `0b9608fc01852ea94182139890beca21b61b677a`, SHA-256
`0b731097a4dfcf33fdaf395ac0bee81c6a6ebff2975590c35ad8cd8d6f3c204f`.
The call is `Keccak(1088, 512, inputBytes, 0x01, 32)`, using Ethereum's
domain suffix. The upstream source is not copied into the repository.

The dedicated workflow now executes the existing signed transaction, header,
transaction-root and receipt-root checks before authenticated account replay.
It retains that report as an artifact. Both replay jobs explicitly select Bash,
including pipeline failure propagation. The standalone account verifier reports its
separate commitment-gate dependency instead of asserting that the other gate
has already run.

## Validation

- The old checker, loaded from the baseline commit, fails the new 135-byte
  `ascii-a` vector. The corrected checker passes all 24 vectors, covering
  two input patterns around the first three rate boundaries.
- A separate local comparison with the byte-verified XKCP source agrees for
  all 545 byte-ramp lengths from 0 through 544.
- The decoded witness matches its pinned SHA-256; the corrected checker
  reproduces both historical roots and rejects all six witness mutations.
- Both workflow files parse; the dedicated shell steps pass Bash syntax
  checks; the commitment assertion matches the existing combined workflow.
- Both workflows require `keccakVectorsChecked == 24`. Changed implementation
  files and the new vector fixture are pinned in the active manifest.

The local environment has no Lean toolchain. Fresh CI on this revision must
execute the Lean-backed commitment and witness steps and check the manifest.
The baseline CI links above validate their recorded revision only.

## Claim boundary

These are executable regression and replay results, not a proof that the Python
cryptographic and trie code refines a Lean specification. The source chain's
canonical selection and proof of work remain trusted. One simple historical
transfer, even with authenticated prestate and both roots reproduced, does not
establish general transaction, fork, client or consensus conformance. Neither
tracking issue is closed by this correction.
