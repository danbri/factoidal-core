# CALL-family execution evidence — 23 November 2026

This phase adds actual `CALLCODE` (`0xf2`), `DELEGATECALL` (`0xf4`)
and `STATICCALL` (`0xfa`) execution to the Lean world-aware interpreter.
All three use the existing continuation stack, memory-window pricing,
child result handling and ancestor rollback. The work advances
[issue #826](https://github.com/danbri/factoidal-core/issues/826), within
[execution #652](https://github.com/danbri/factoidal-core/issues/652) and
[full Ethereum #725](https://github.com/danbri/factoidal-core/issues/725).
It is stacked on [draft PR #798](https://github.com/danbri/factoidal-core/pull/798).

[Published source checkpoint `3b04b0f`](https://github.com/danbri/factoidal-core/commit/3b04b0f88dbe53fee84fcb67c8f6f26d31e851f7)
has exactly the checked local evidence tree
`00f7b6e09f2e5204bb92e645b9571230162495f9`. Its native sources are byte-identical
to local runtime commit `b7e5c44e`; its harness matches local `b63ee290`.
Hosted CI is a separate gate, pending at publication. The branch remains
unmerged; the exact-head builds-repository Linux gate and full premerge
verification have not been claimed.

The semantic reference is
[EELS Cancun `system.py` at `1da5a11`](https://github.com/ethereum/execution-specs/blob/1da5a11ca8cd3a4ad00fd1821c27ef01a4b18653/src/ethereum/forks/cancun/vm/instructions/system.py).
The implementations and tests do not establish complete fork-indexed
EVM conformance or independent formal refinement to that specification.

## Executable changes

| Property | CALLCODE | DELEGATECALL | STATICCALL |
| --- | --- | --- | --- |
| Code | Target account | Target account | Target account |
| Execution account and storage | Current account | Current account | Target account |
| Child caller | Current account | Inherited caller | Current account |
| Child value | Explicit operand | Inherited value | Zero |
| Funds check | Explicit value against current balance | None | None |
| Inter-account transfer at entry | None | None | None |
| Child static flag | Inherited | Inherited | True |
| Value surcharge and stipend | For nonzero explicit value | None | None |
| New-account surcharge | None | None | None |

The code target is masked to 160 bits, warmed and checked for account
coverage independently of the execution/storage address. Child state is
first projected from its execution account; only then is its code replaced
with the code target's bytes. This retains the correct original/current
storage, slot warmth, balance and log emitter.

Nonzero CALLCODE is permitted from a static parent. Its child remains
static, so a subsequent SSTORE, LOG or positive-value CALL fails there.
DELEGATECALL receives inherited message value separately from the zero
value supplied to scheduling, preventing an invented surcharge, stipend
or funds check. Missing witnesses, unsupported precompiles and exhausted
simulation fuel remain indeterminate.

The fixture CLI now accepts optional decimal `ENTRY_CALLER` and `TX_ORIGIN`
after `PREWARM_PARENT`. Both retain the legacy zero default and must fit in
160 bits. The new differential harness explicitly supplies `0xc2` for both,
matching its reference-client entry context. This fixes the initial test
setup mismatch without changing old invocations.

## Compiler and proof evidence

Official Lean 4.33.1 built the EVM library and both native entry points in
64 jobs. The CLI-only follow-up rebuilt the affected graph in 43 jobs.
There are **12 new public theorem selections**, three new private printed
lemmas, and **33 executable regression guards**. The active inventory is
184 selected public axiom reports across 20 source files and 103 pinned
source blobs.

Fresh elaboration matched all 184 exact declared axiom sets. All 103 source
pins and the fresh Cancun replay passed the ledger, all five ledger test
groups passed without skips, and three altered axiom reports were rejected.

The public statements concern decoded operand existence, zero scheduling
value for six-operand variants, entered code/execution address, caller and
value context, account journal projection, entry balance preservation,
depth, paid output windows, input-byte correspondence, and missing witness
refusal. `execute_missing_variant_code` connects refusal to the public
executor; a private theorem connects the three opcodes to the actual
continuation loop. Existing rollback and resumption statements remain.

Nine of the twelve new public statements print only `propext`; two print
`propext` and `Quot.sound`; the public dispatch-refusal statement prints
`propext`, `Classical.choice` and `Quot.sound`. These are actual compiler
reports, not inferred dependency lists. They are model-relative properties,
not proofs that the EELS semantics, compiler or runtime are correct.

An independent source review read the implementation, all twelve public
statements, all 33 guards and the differential harness, and found no blocking
defect. That review did not execute the compiler or replace the axiom audit.
The scoped hygiene check found no banned constructs or dependencies in 40
EVM Lean files and 270 printed declarations; a compiled-C scan found no
non-loop recursion in that slice. This is distinct from the full repository
recursion and compiler-replacement gate.

[Active ledger](../formal/lean4/evm-cleanroom/evidence/active-claim-manifest-v2.json)
· [Actual selected-axiom audit](../formal/lean4/evm-cleanroom/evidence/2026-11-23-call-family/axiom-audit.json)

## Independent execution comparisons

Both references execute real bytecode. EthereumJS is `@ethereumjs/evm@10.1.3`
under the committed dependency lock. Geth is `1.17.10`, source
`1df30b18d9ed35ee9d28ffd4648442c2204554ad`; its executable is independently
SHA-256 checked by the existing oracle helper.

| Variant | EthereumJS matches | Geth matches |
| --- | ---: | ---: |
| CALLCODE | 82 / 82 | 76 / 76 |
| DELEGATECALL | 70 / 70 | 64 / 64 |
| STATICCALL | 61 / 61 | 54 / 54 |
| Total | **213 / 213** | **194 / 194** |

The two references also agree on all 194 shared fixtures. Coverage includes
context and self-code reads, memory and return-data windows, storage-owner
selection, inherited value, static descendants, explicit-value CALLCODE,
refunds and log emitters, ancestor rollback, depth, stack arity, cold/warm
access, ten overhead boundary groups and EIP-150 rounding boundaries.

The Geth lane excludes 3 direct static entries, 1 Osaka case, 9 nonzero-depth
entries, 3 cold-parent entries and 3 zero-entry-gas cases. These 19 still
run against EthereumJS. Nested STATICCALL is included in the Geth lane.
Geth compares status, gas, returned bytes, available stack/memory/return-data,
account balances/storage and available refunds. It does **not** independently
compare log records, access warmth or exact exception categories. EthereumJS
adds those observations where the harness exposes them. Every compared field
and per-case result is present in the raw report.

Nine separate boundary controls require indeterminate results: identity
precompile and unchecked Keccak for each variant, plus simulation-fuel
exhaustion for each. They are not counted as implemented-case matches.
Eight CLI controls cover default/explicit context and input refusal. Four
altered-observation controls establish that the comparator rejects changes
to gas, storage owner, context and returned bytes; they do not mutate the
Lean implementation.

Missing account/storage coverage is checked by Lean guards and theorems;
the client comparisons supply complete synthetic state. The new oracle
fixtures start with zero storage. Nonzero original/current storage is
covered by the Lean guards and retained suites. The Osaka example checks
propagation of the selected CLZ behaviour only.

[Complete comparison report](../formal/lean4/evm-cleanroom/evidence/2026-11-23-call-family/call-family.json)
· [Same-argument baseline opcode controls](../formal/lean4/evm-cleanroom/evidence/2026-11-23-call-family/baseline-opcode-controls.json)

## Retained execution and transaction checks

The old interpreter is built separately at public `d1005fb7a009e9c8942f5f74517e068b66fb5f48`.
With identical legacy CLI arguments, it refuses each new opcode as
`indeterminate/invalidOpcode`; the new interpreter completes each of the
three simple baseline controls.

The new executable retains 330/330 CALL, 450/450 value-CALL, 160/160 call
context, 122/122 CALL-data and 124/124 byte-copy EthereumJS matches. The
CALL-data/byte-copy Geth subsets still pass at 112/112 and 124/124.
Hash/log comparisons retain 80/80 matches and 24 XKCP known answers.
The unchanged generated raw corpus passes 10,000/10,000 comparisons,
comprising 9,733 unique execution inputs.

The 60 signed synthetic transactions retain matching receipt and state
roots, with eight signed admission rejections, one preserialisation rejection
and eleven indeterminate boundaries. The authenticated Shanghai 1CAT replay
still matches Lean, EthereumJS and Geth at 33,987 gas, 4,800 refund and one
Transfer log. Its intermediate world root remains
`4ec90276be487d2567d41039696e1bb75b3fa8cb796fc9705f5d83c606a17000`;
the authenticated target storage root remains
`4fb8888e09be2dd7e1b31f7e39e670b7820adf8d179f382c34481a632ba0a08a`.
The intermediate root is not the final block world root.

All six selected Prague roots and all six selected Cancun contract roots
were replayed successfully with the new binary. The Cancun fixture's other
18 fork cases remain unexecuted and are not counted as passes.

[Transaction report](../formal/lean4/evm-cleanroom/evidence/2026-11-23-call-family/retained-call-transaction.json)
· [Authenticated replay](../formal/lean4/evm-cleanroom/evidence/2026-11-23-call-family/retained-authenticated-shanghai.json)
· [Raw corpus report](../formal/lean4/evm-cleanroom/evidence/2026-11-23-call-family/raw10000.json)

## Timing observations

The existing runner measured 160 alternating pairs after 12 warm-up pairs
for each legacy path, under the shared build and timing locks. Each sample
includes native process launch, execution, JSON output and exit. All legacy
output fields remained identical.

| Legacy path | p50 before → after (ms) | p95 before → after (ms) | p99 before → after (ms) | Maximum before → after (ms) |
| --- | ---: | ---: | ---: | ---: |
| ABI frame | 5.112 → 5.087 | 7.262 → 7.438 | 17.013 → 10.890 | 25.028 → 11.337 |
| CALL with storage | 4.857 → 4.750 | 7.894 → 8.469 | 16.087 → 16.715 | 24.736 → 38.005 |

Median paired differences were −0.168 ms and −0.093 ms respectively.
The CALL tail and maximum worsened in this sample. These measurements do
not establish a speedup or tail-latency parity; performance investigation
[issue #739](https://github.com/danbri/factoidal-core/issues/739) stays open.
The raw report includes every sample, executable digest and machine details.

[Paired timing samples](../formal/lean4/evm-cleanroom/evidence/2026-11-23-call-family/legacy-cli-timing.json)

## Reproduction and remaining boundaries

Build with the official pinned toolchain, from `formal/lean4`:

```sh
lake -d evm-cleanroom build EVMCleanroom evm-subset evm-call-transaction
```

This Linux session used `LEAN_STACK_SIZE_KB=65536`,
`MIMALLOC_ARENA_RESERVE=67108864`, an 8 GiB address-space cap, a 600-second
CPU/time bound and `/tmp/foafnaut-lean-build.lock`. Initial 2–4 GiB attempts
failed from runtime thread reservation or process memory limits before a
complete build; they were environment failures, not passing proof runs.
The official runtime and its initialisation were not modified.

From `formal/lean4/evm-cleanroom`, install the committed differential lock
and run the new actual-bytecode comparisons:

```sh
npm ci --prefix scripts/differential --ignore-scripts --no-audit --no-fund
EVM_GETH_EXE=/absolute/path/to/pinned/geth/evm \
  node scripts/differential/call-family.mjs "$PWD/.lake/build/bin/evm-subset"
python3 scripts/check-active-ledger.py
python3 scripts/check-axiom-output.py
```

The selected axiom checker itself invokes `lake -d evm-cleanroom` from
`formal/lean4`. Run it with the same toolchain, bounds and build lock.
The source/fixture pins, per-case categories and Geth exclusions are gates
in `.github/workflows/evm-cleanroom.yml`.

CREATE/CREATE2, concrete precompiles, complete historical/fork rules,
EIP-7702-aware code resolution, broad authenticated block execution,
cryptographic refinement, persistent state, operational RPC/Engine API,
networking and complete Lean consensus remain open. The optional Keccak
acceptance, host envelope/signature/header/MPT/receipt operations and provider
canonical-chain selection retain their earlier trust boundaries. This phase
does not satisfy the full Ethereum acceptance epic or authorise a main merge.
