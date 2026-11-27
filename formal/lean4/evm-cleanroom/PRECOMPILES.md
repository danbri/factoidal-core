# Precompiled contracts

Addresses 0x01 to 0x11 are implemented in repository-owned Lean and are reached through
the actual CALL family and the transaction frame. No other Ethereum implementation is
imported, copied, translated or wrapped; published vectors and the Python standard library
are used only as test oracles in CI.
[Acceptance epic #725](https://github.com/danbri/factoidal-core/issues/725)

## What runs where

| Address | Contract | Module | Price | Source |
| --- | --- | --- | --- | --- |
| 0x01 | ECRECOVER | [`Ecrecover`](EVMCleanroom/Precompiles/Ecrecover.lean) on [`Secp256k1`](EVMCleanroom/Precompiles/Secp256k1.lean) | 3000 | Yellow Paper appendix E |
| 0x02 | SHA-256 | [`Sha256`](EVMCleanroom/Precompiles/Sha256.lean) | 60 + 12 per word | FIPS 180-4 |
| 0x03 | RIPEMD-160 | [`Ripemd160`](EVMCleanroom/Precompiles/Ripemd160.lean) | 600 + 120 per word | Dobbertin, Bosselaers, Preneel 1996 |
| 0x04 | identity | [`IdentityPrecompile`](EVMCleanroom/IdentityPrecompile.lean) (unchanged) | 15 + 3 per word | Yellow Paper appendix E |
| 0x05 | MODEXP | [`ModExp`](EVMCleanroom/Precompiles/ModExp.lean) | EIP-2565; EIP-7883 and EIP-7823 under `osaka`; EIP-198 available, not routed | EIP-198, 2565, 7823, 7883 |
| 0x06 | alt_bn128 add | [`BN254`](EVMCleanroom/Precompiles/BN254.lean) | 150 | EIP-196, EIP-1108 |
| 0x07 | alt_bn128 mul | `BN254` | 6000 | EIP-196, EIP-1108 |
| 0x08 | alt_bn128 pairing check | `BN254` on [`Pairing`](EVMCleanroom/Precompiles/Pairing.lean) | 45000 + 34000 per pair | EIP-197, EIP-1108 |
| 0x09 | BLAKE2b F | [`Blake2f`](EVMCleanroom/Precompiles/Blake2f.lean) | 1 per round | EIP-152, RFC 7693 |
| 0x0a | KZG point evaluation | [`KZG`](EVMCleanroom/Precompiles/KZG.lean) | 50000 | EIP-4844 |
| 0x0b–0x11 | BLS12-381 G1 add, G1 MSM, G2 add, G2 MSM, pairing check, map Fp to G1, map Fp2 to G2 | [`BLS12381`](EVMCleanroom/Precompiles/BLS12381.lean) | 375; discounted 12000 per item; 600; discounted 22500 per item; 37700 + 32600 per pair; 5500; 23800 | EIP-2537, RFC 9380 |

[`Precompiles.run`](EVMCleanroom/Precompiles.lean) is the single entry. `CallOpcode.precompileStep`
(CALL, CALLCODE, DELEGATECALL, STATICCALL) and `CallTransaction.runFrame` call it for every
active address other than 0x04.

Fork gating follows the opcode profiles of `Core`, which are coarser than forks:

- `preShanghai` and `shanghaiPlus` execute 0x01–0x09. `shanghaiPlus` cannot tell Shanghai from
  later forks, so 0x0a–0x11 stay refused there (`unsupportedFork`, an indeterminate result), as before.
- `cancunPlus` adds 0x0a.
- `osaka` adds 0x0b–0x11 and prices MODEXP by EIP-7883 with the EIP-7823 length bound. There
  is no separate Prague profile, so the EIP-2537 set is reachable only under `osaka`.
- 0x100 (P256VERIFY, EIP-7951) is not implemented and stays refused.

Three outcomes are kept apart: success (output and unspent gas), exceptional halt (too little
gas or input the specification rejects: the caller loses the forwarded gas), and refusal (a
local bound of this implementation, never reported as an Ethereum result).

ECRECOVER needs the package's explicit Keccak opt-in, like the KECCAK256 opcode. The other
precompiles have no opt-in. Their function values are tested, not proved; whether the whole set
should sit behind an opt-in is an open decision.

## Local bounds and refusals

Every loop runs on a count that is fixed by the input length or proved bounded.

- Input above 1 MiB is refused before any byte is read (`run_oversize`), the same local bound as identity.
- MODEXP consumes the exponent byte by byte: eight steps per declared exponent byte. After the
  gas check it refuses a declared exponent above 1 MiB or a base or modulus above 128 KiB
  (`ModExp.run_refuses_over_bound`, `run_success_bounded`). Under `osaka` a declared length above
  1024 bytes is an exceptional halt (`run_osaka_length_bound`).
- BLAKE2f reads a round count below 2³² (`roundField_bound`), needs one gas per round, and refuses
  more than 2³⁰ rounds after the gas check (`run_refuses_over_bound`).
- Pairing and multi-scalar operations run one step per whole item of the input, which the price pays for.

## Proved, and only tested

Proved (no `sorry`, no user axioms, `native_decide`, `unsafe`, `implemented_by` or `partial`; CI
reads the actual `#print axioms` output of 16 modules and admits only `propext`, `Classical.choice`
and `Quot.sound`):

- MODEXP computes the modular power: for a non-zero modulus and lengths within the local bounds
  the output is the big-endian encoding of `base ^ exponent % modulus` on the natural numbers
  ([`ModExpProofs`](EVMCleanroom/Precompiles/ModExpProofs.lean): `powByte_spec`, `powBytes_spec`,
  `powBytes_eq_pow_mod`, `body_eq_pow_mod`);
- gas admission and exact accounting for every precompile (`charge_underfunded`, `charge_success`,
  the `run_success` theorems, `Precompiles.run_gas_le`);
- output lengths and input-length rules (fixed lengths, whole items, empty-input failure, prefix-only
  reads for ECRECOVER and alt_bn128 add and mul);
- the bounds and refusals above;
- the routing contract: `CallOpcode.callStep_native_success`, `callStep_native_failure`,
  `callStep_native_refusal`, `dispatchCall_native`, `unimplementedPrecompile_iff`,
  `CallTransaction.runFrame_native_success`, `runFrame_native_failure`, and the fork-gating facts
  `Precompiles.run_inactive` and `active_range`;
- representation facts: field results stay canonical, the division-free addition and subtraction
  equal the residues on canonical values, MODEXP accumulators stay below the modulus, and every
  point returned by the shared secp256k1 API satisfies the curve equation (checked at run time).

Only tested: every other function value. That is the digests, recovered addresses, group
operations, pairings, map-to-curve results and the KZG verdict. Group laws, bilinearity and primality
of the moduli are not proved. They are exercised by build-time guards (generator orders, the curve
polynomials at the curve parameter, Frobenius as a `p`-th power, bilinearity in both arguments on
both pairing curves, the SHA-256 constants against their definition) and by the vectors below.
Nothing is constant-time: the precompiles handle public data only.

## Vectors and controls

[`scripts/precompiles/run-vectors.py`](scripts/precompiles/run-vectors.py) runs the compiled
`evm-precompile` binary (the router, with no `Lean.*` import) and compares exact output and exact gas.

- 28 published vector files of go-ethereum v1.16.7, pinned by commit and SHA-256 in
  [`sources.json`](scripts/precompiles/sources.json), downloaded at test time and not vendored;
- 122 `verify_kzg_proof` cases of the consensus specification tests, vendored with provenance under
  [`third_party/ethereum-kzg-vectors`](../../../third_party/ethereum-kzg-vectors/PROVENANCE.md),
  turned into point-evaluation calls (54 valid, 68 invalid or rejected);
- 3000 generated cases for SHA-256, RIPEMD-160, BLAKE2f and MODEXP against the Python standard library.

In total 2351 published cases and 3000 generated ones. Negative controls: every priced vector is
re-run with one gas unit less and must fail (2574 cases), one expected output per file is altered and
the comparison must report it (19 of 19), every valid KZG case is re-run with a wrong version byte,
and the published failure files (malformed lengths, non-canonical coordinates, points off the curve
or outside the subgroup) must fail.

## Time per call

Measured by [`scripts/precompiles/bench.py`](scripts/precompiles/bench.py) on the shared development
Mac (Apple silicon, under other load), five calls per case; CI repeats the report on Linux as an
artefact. Clients that execute about 100 million gas per second spend about 10 ns per gas unit.

| Contract | p50 | p95 | max | ns per gas (p50) |
| --- | ---: | ---: | ---: | ---: |
| ECRECOVER (valid signature, 100 calls) | 2.3 ms | 2.4 ms | 2.5 ms | 750 |
| SHA-256 | 2 µs | 26 µs | 1.7 ms (64 KiB) | 58 |
| RIPEMD-160 | 2.5 µs | 37 µs | 2.2 ms (64 KiB) | 8 |
| MODEXP | 128 µs | 715 µs | 0.8 ms | 122 |
| alt_bn128 add | 2.6 µs | 111 µs | 127 µs | 21 |
| alt_bn128 mul | 0.75 ms | 3.0 ms | 3.1 ms | 317 |
| alt_bn128 pairing | 50 ms | 66 ms | 182 ms | 443 |
| BLAKE2f | 5.8 µs | 5.8 µs | 128 ms (8 million rounds, 16 ns per round) | 486 at 12 rounds |
| KZG point evaluation | 64 ms | | | 1280 |
| BLS12-381 G1 add | 189 µs | 199 µs | 208 µs | 507 |
| BLS12-381 G1 MSM | 4.9 ms | 79 ms | 86 ms | 405 |
| BLS12-381 G2 add | 291 µs | 312 µs | 324 µs | 488 |
| BLS12-381 G2 MSM | 14 ms | 250 ms | 327 ms | 631 |
| BLS12-381 pairing | 50 ms | 200 ms | 213 ms | 696 |
| map Fp to G1 | 1.5 ms | 1.5 ms | 1.5 ms | 269 |
| map Fp2 to G2 | 20 ms | 21 ms | 216 ms | 840 |

The hashes are within an order of magnitude of the gas ballpark. Everything built on 256-bit and
381-bit field arithmetic is 30 to 130 times slower than it: each field operation is a general
big-integer operation of the Lean runtime (about 0.2 µs), where native clients use fixed-width
assembly. The largest single costs are the definitional subgroup checks (multiplication by the group
order), the final exponentiation, and one field inversion per affine result. None of these changes
an answer; they are the next places to spend effort (membership tests by endomorphism, cyclotomic
squaring, windowed and bucketed multi-scalar multiplication), each of which needs its own evidence.

## Sharing code between packages

- The field, curve, tower and pairing modules import nothing outside `EVMCleanroom/Precompiles`.
  [`Secp256k1`](EVMCleanroom/Precompiles/Secp256k1.lean) with `Curve`, `Field` and `Basic` is the one
  shared secp256k1 module: another package takes those four files through a `srcDir` library
  (the wallet package does). The same route is open to the consensus package for BLS12-381
  (`BLS12381`, `Pairing`, `Tower`, `Curve`, `Field`, `Basic`); its own experimental pairing modules
  were left untouched. No package imports the EVM, and the EVM imports no other package, so there
  is no cycle and no broad import.
- SHA-256 is a local module, not an import of `L4Factoidal.Crypto.SHA2`. The package's source gates
  (`check-witness-axioms.py`, `check-blobhash-axioms.py`) admit only `EVMCleanroom` imports, and every
  lakefile is pinned in the evidence; a `srcDir` library for the shared SHA-256 built and passed, but
  it would have changed eight pinned lakefiles and two gate scripts. If one SHA-256 source for both
  Ethereum packages is preferred, that is the change to make.
- ECRECOVER does not use `SecpRecovery.lean` (transaction admission): that module enforces the
  low-`s` rule and inverts once per step. A guard checks that both recover the same key.

## Evidence pins

The precompile modules are now in the import closure of `CallOpcode`. They are pinned in
[`active-claim-manifest-v2.json`](evidence/active-claim-manifest-v2.json) (170 to 185 sources) and
listed in [`witness-source-manifest.json`](evidence/witness-source-manifest.json) (32 to 47 modules);
the counts in `evm-cleanroom.yml`, `evm-identity-precompile.yml` and `evm-witness.yml` follow. The
generated C of the whole package has no non-tail recursion (`tools/lean-tail-recursion-audit.py`).
The library root and the reviewed lakefiles are unchanged; the runner has its own
[`lakefile-precompiles.toml`](lakefile-precompiles.toml).

## Open

- P256VERIFY (0x100, EIP-7951) is not implemented.
- A Prague profile, so that 0x0b–0x11 are reachable without the Osaka MODEXP price.
- EIP-198 pricing is implemented and tested but no profile selects it (the profiles start at Berlin rules).
- The official state-test fixtures for precompiles run through the scoreboard, not here.
- Proofs of the arithmetic itself (group laws, pairing properties, refinement to a specification).
- Speed, as above.
