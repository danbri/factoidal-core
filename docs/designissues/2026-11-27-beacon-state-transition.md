# Independent beacon state transition (Fulu)

2026-11-27. Acceptance epic: https://github.com/danbri/factoidal-core/issues/725.
Code: [`formal/lean4/ethereum-beacon`](../../formal/lean4/ethereum-beacon).
Workflow: [`ethereum-beacon.yml`](../../.github/workflows/ethereum-beacon.yml).

## Scope and pins

The beacon chain `state_transition` for the fork that is live on mainnet,
Fulu (active since epoch 411392), written in repository-owned Lean 4.33.1.

- Specification: [ethereum/consensus-specs v1.6.1](https://github.com/ethereum/consensus-specs/tree/v1.6.1),
  commit `5fa6edcca8ab4cf548653e6680b17b9d3e04d225`: the `beacon-chain.md` documents of phase0, altair,
  bellatrix, capella, deneb, electra and fulu, the SSZ documents, and the preset and configuration tables.
- Test vectors: the same release's assets, `minimal.tar.gz`
  (sha256 `e1d0c9dc3d09fb74a98b324c40b2587a17dc555e6149d3f9741601fffcf43901`) and `mainnet.tar.gz`
  (sha256 `8401c58700c461154db2050c2a982af7aca259bd016c2184ec39c454edf6f1c5`). The workflow checks the
  digest before unpacking.

The specification's Python, the reference clients and BLS libraries are not imported, copied, translated or
wrapped. The vectors are an oracle in development and CI: the runner compares answers with them and never
copies an expected answer into a result.

## Layout

A separate Lake package, so that the consensus package's lakefile and its audits stay as they are. It selects in
place the pure SHA-256 module (`L4Factoidal.Crypto.SHA2`) and the BLS12-381 modules of
`formal/lean4/ethereum-consensus` (`G1PublicKey`, `G2Signature`, `PairingTarget`, `HashToField`, `BLSVerify`).
The only other import is `Std.Data.HashMap` from the toolchain.

| Module | Role |
| --- | --- |
| `Beacon/Preset.lean` | `minimal` and `mainnet` presets and configuration |
| `Beacon/SSZ.lean` | `Codec`: serialise, deserialise, `hash_tree_root`; the `ssz_container` command |
| `Beacon/Types.lean` | the 59 Fulu containers that `ssz_static` covers |
| `Beacon/Helpers.lean` | accessors, shuffling, committees, proposer selection, domains, churn, BLS calls |
| `Beacon/Epoch.lean` | `process_epoch` and its 15 sub-steps |
| `Beacon/Block.lean` | `process_block` and its operations |
| `Beacon/RootCache.lean` | incremental roots of the nine large state fields |
| `Beacon/Transition.lean` | `process_slot`, `process_slots`, `state_transition` |
| `Beacon/Theorems.lean` | the theorems listed below |
| `Beacon/Snappy.lean`, `Beacon/Harness.lean`, `BeaconSpecTestsMain.lean` | vector reader and runner (test tooling) |

## Decisions

**Arithmetic on `Nat`.** `uint64` fields are `Nat`, so sums never wrap. Where the specification's `uint64`
arithmetic would raise, the transition refuses: `BeaconState.inRange` is checked at the end of every slot step
and every block. Subtractions that the specification guards are guarded the same way; `decrease_balance` is
`Nat` subtraction, which stops at zero as the specification requires.

**Refusal.** A failed assertion of the specification is `Except.error` with a reason and no state. The reason
strings are diagnostics, not consensus data.

**Resource limits (implementation limits, not consensus rules).**

| Limit | Value | At the limit |
| --- | --- | --- |
| `maxSlotAdvance` | 2^24 slots per `processSlots` call | refused before the first step (`processSlots_refuses_over_limit`) |
| `proposerSearchLimit` | 2^20 candidates | `compute_proposer_index` refused (the specification loops without a bound) |
| `syncCommitteeSearchLimit` | 2^22 candidates | sync committee selection refused |
| `Snappy.maxOutput` | 256 MiB declared output | vector file refused |

Loops over the registry run for a count fixed on entry (`registryLoop_size`, the `mapIdx` steps); the pending
deposit walk takes at most `MAX_PENDING_DEPOSITS_PER_EPOCH + 1` steps; the withdrawal sweep visits at most
`min(registry, MAX_VALIDATORS_PER_WITHDRAWALS_SWEEP)` validators. The walk over pending partial withdrawals is
bounded only by the queue length, as in the specification.

**Execution payload.** Header-level checks only (parent hash, `prev_randao`, timestamp, blob commitment count
against the blob schedule). The execution engine is not linked; its verdict is an input (`Ctx.executionValid`),
which the vectors supply.

**BLS.** Signature checks call `EthereumConsensus.BLS.Verify.verifySigningRoot`. Every failure of that function
(malformed key or signature, infinity, mismatch) is the verdict "invalid". Key lists above that module's limit of
2048 are summed in groups, which refuses a list in which one group sums to the point at infinity although the
whole list does not; that case is recorded as open. `eth_fast_aggregate_verify` accepts the point at infinity for
an empty participant list as the specification says. The vectors' three modes are kept apart in every count:
required (`bls_setting: 1`), off (`2`), and unmarked. Unmarked cases are run with real checks in CI; two unmarked
`deposit` cases (`key_validate_invalid_*`) only pass with real checks, which shows the unmarked cases do depend on
them. In BLS-off mode the next sync committee's aggregate key is the reference suite's stub value, as the
vectors expect.

**Fast paths.** `shuffledIndexWith` (pivot hashes computed once per seed) is proved equal to `shuffledIndex`
(`shuffledIndexWith_eq`). `shuffleList` (whole-list swap-or-not, one hash per 256 positions) and the incremental
state root (`cachedStateRoot`) are tested, not proved: the runner compares the cached root with the plain root on
every transition case, and the `sanity` vectors check the incremental path through block state roots and the
`state_roots` of expected post-states.

## What is proved, and what is only tested

Proved in `Beacon/Theorems.lean` (axioms: `propext`, `Quot.sound`, and `Classical.choice` for
`shuffledIndexWith_eq`; the workflow checks the inventory and the axioms on every run):

- Slots: `slotStep_slot`, `iterateSlots_succ`, `iterateSlots_add`, `iterateSlots_slot`,
  `processSlots_eq_iterate`, `processSlots_slot`, `processSlots_slot_lt`.
- Refusals: `processSlots_refuses_not_after`, `processSlots_refuses_over_limit`,
  `stateTransition_refuses_old_block`, `processBlockHeader_refuses_slot`, `u64_decode_wrong_width`,
  `bool_decode_wrong_width`, `bitlist_decode_empty`, `bytesN_decode_wrong_width`, `byteList_decode_over_limit`.
- Effective balance hysteresis: `effectiveBalanceUpdate_le_max`, `effectiveBalanceUpdate_stable`,
  `effectiveBalanceUpdate_changed_le_balance`, `effectiveBalanceUpdate_changed_multiple`.
- Balances: `increaseBalance_size`, `decreaseBalance_size`, `increaseBalance_get`, `decreaseBalance_get`,
  `transfer_conserves`.
- Registry loops: `initiateValidatorExitWith_size`, `registryStep_size`, `registryLoop_size`,
  `processRegistryUpdates_size`, `processRewardsAndPenalties_size`, `processSlashings_size`,
  `processInactivityUpdates_size`, `processEffectiveBalanceUpdates_size`.
- Fast path: `foldl_congr_mem`, `shuffledIndexWith_eq`.

These theorems are about the executable definitions. None of them relates a definition to the specification:
agreement with the specification is tested by the vectors, not proved. Also only tested: SSZ round trips and
roots, SHA-256 values, all BLS arithmetic, the Snappy reader, `shuffleList`, the root cache, and every reward,
penalty, churn and withdrawal computation. The Lean compiler and runtime, the C toolchain and the host are
trusted.

## Measured (GitHub-hosted Linux runner, 4 workers)

Run 45930370360 on commit `e619b1431`. Signatures were really checked in every case whose metadata allows it
(all but the three `bls_setting: 2` cases per preset; `ssz_static` and `rewards` have no signatures).

| Preset | Suite | Cases | Pass | Fail | Unsupported | BLS required (pass) | BLS off (pass) | unmarked (pass) |
| --- | --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| minimal | `ssz_static` | 7,257 | 7,257 | 0 | 0 | 0 | 0 | 7,257 (7,257) |
| minimal | `epoch_processing` | 157 | 157 | 0 | 0 | 15 (15) | 0 | 142 (142) |
| minimal | `rewards` | 34 | 34 | 0 | 0 | 0 | 0 | 34 (34) |
| minimal | `operations` | 378 | 378 | 0 | 0 | 68 (68) | 3 (3) | 307 (307) |
| minimal | `sanity` | 107 | 107 | 0 | 0 | 5 (5) | 0 | 102 (102) |
| minimal | `finality` | 5 | 5 | 0 | 0 | 0 | 0 | 5 (5) |
| minimal | `random` | 16 | 16 | 0 | 0 | 16 (16) | 0 | 0 |
| mainnet | `ssz_static` | 295 | 295 | 0 | 0 | 0 | 0 | 295 (295) |
| mainnet | `epoch_processing` | 142 | 142 | 0 | 0 | 10 (10) | 0 | 132 (132) |
| mainnet | `rewards` | 34 | 34 | 0 | 0 | 0 | 0 | 34 (34) |
| mainnet | `operations` | 342 | 342 | 0 | 0 | 62 (62) | 3 (3) | 277 (277) |
| mainnet | `sanity` | 95 | 95 | 0 | 0 | 5 (5) | 0 | 90 (90) |
| mainnet | `finality` | 5 | 5 | 0 | 0 | 0 | 0 | 5 (5) |
| mainnet | `random` | 16 | 16 | 0 | 0 | 16 (16) | 0 | 0 |

Totals: minimal 7,954 of 7,954 in 35 min 53 s, peak memory 46 MB; mainnet 929 of 929 in 1 h 20 min, peak
memory 134 MB. Per-handler counts are the committed ratchet baseline
(`formal/lean4/ethereum-beacon/evidence/beacon-spec-tests-baseline.json`); p50 / p95 / max per handler are in
each run's job summary. Transition time on the mainnet preset, per case, with signature checks (about 3.4 s
each on that runner) included: epoch sub-steps p50 at most 0.3 ms except `proposer_lookahead` (761 ms) and
`historical_summaries_update` (97 ms), max 3.6 s (`pending_deposits` with a deposit signature);
`sanity/slots` p50 3.9 s, max 425 s (8,192 slots); `sanity/blocks` p50 9.1 s, max 433 s; `finality` max 1,610 s.

The mainnet-preset vectors have small registries (256 to 2,048 validators). For scale, the runner's
`--bench-epoch` mode grows a vector's registry to a chosen size and times each epoch sub-step once (run
45928096381, commit `ea503d6ea`; the step times there include a pass over the registry made by the benchmark):

| Registry | Epoch sub-steps, total | of which `proposer_lookahead` | `hash_tree_root(state)` plain | from the cache after one slot's changes | Peak memory |
| ---: | ---: | ---: | ---: | ---: | ---: |
| 100,000 | 0.62 s | 0.55 s | 4.7 s | 0.12 s | 71 MB |
| 1,000,000 | 1.35 s | 0.58 s | 44.5 s | 1.03 s | 358 MB |

Each registry-sized step is linear in the registry (0.41 s for rewards and penalties at one million); proposer
selection does not grow with it. One run each, so no spread is claimed.

## Open

- No fork choice link, no execution engine link, no networking, no genesis or fork-upgrade functions; the
  `rewards`, `finality`, `random`, `fork`, `transition`, `genesis`, `light_client`, `kzg`, `networking` and
  `ssz_generic` vector suites are not run yet.
- Committee shuffling is recomputed per attestation (linear in the active set per attestation); a per-epoch
  shuffling cache is the next step for mainnet-size registries.
- The registry root cache compares every validator with its cached copy each slot (linear, no hashing); it does
  not yet track dirty indices from the mutators.
- The pairing in `PairingTarget` takes about 1.3 s, so one signature check costs about 2.8 s; this dominates the
  vector run time.
- Grouped key aggregation above 2048 keys (see BLS above).
- Constant-time behaviour is not claimed anywhere.
