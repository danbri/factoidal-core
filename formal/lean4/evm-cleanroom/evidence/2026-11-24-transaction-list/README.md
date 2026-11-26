# Ordered Cancun transaction-list evidence

Implementation: `91cae62479cbd3a13775b3dd15f502646c11db41`, tree
`7d8ef4d75ef64e634574ee4a313294e9072e4f4f`. Tracking:
[issue 867](https://github.com/danbri/factoidal-core/issues/867).
The [worknote](../../../../../docs/20261124-evm-transaction-list.md) explains
the transition, proof boundaries, observed parser crash, oracle corrections,
timings and remaining full-client work.

`provenance.json` binds each retained report to its SHA-256 and size, records
the native/compiler/reference identities, and distinguishes observed results
from assumptions. `SHA256SUMS` also covers this index and the provenance file.
Run `sha256sum --check SHA256SUMS` from this directory to check the bundle.

## Reading the results

| Evidence | Meaning |
| --- | --- |
| `list-execution.json` | 36 primary lists: 30 complete execution matches, five matched admission rejections and one explicit local unsupported boundary; 25 mutations and 16 separate controls |
| `audit-list-transport-published-head.json`, `axioms-list-transport-published-head/` | 46 actual Lean axiom reports, two theorem files, 47 implementation/support pins required to match the published source |
| `head-source-binding.json` | All 146 reviewed active source pins also match that published commit |
| `audit-active-local.json`, `root-build.log` | Complete active selection: 292 statements in 27 files; the active selection includes the dedicated subsets |
| `json-resource-guards-and-baseline-parity.json` | 90 guarded JSON cases, 42 exact lexical refusals, plus nine safe comparisons with retained development binaries |
| `json-resource-guards-ci-default.json` | The same 90 guarded cases under the default CI invocation, with zero old-binary invocations |
| `parser-crash-before.json`, `parser-before-control-and-smaller-depth.json` | Deliberate development failure and controls; raw records are preserved, and missing embedded hash/limit metadata is qualified in provenance |
| `transport-schema.json`, `codec-existing-path-parity.json`, `codec-parity-fixtures-and-before.json` | 22 list transport controls and 12 retained byte-parity checks, including complete captured inputs and baseline outputs |
| `retained-*.json`, `london-*.json` | Retained execution and London-fee checks; each keeps its own scope |
| `cli-timings.json`, `timing-blob-request.json` | Two process-inclusive paths, 12 warm-up and 160 measured pairs per path; complete output equality, raw times and both source/native identities |

The two separately counted resource lists contain 512 reference-executed
transactions. The exact 16 MiB output list matches all 256 native receipts;
one byte over produces an explicit native resource refusal at index 255.
That refusal is not a matching native execution. The 60-case retained
ordinary lane uses the unchanged `evm-subset` executable.

## Reproduce the source and native checks

Use the published checkout containing this bundle, whose executable and proof
sources match the implementation commit, Lean 4.33.1 on `PATH`, Python 3
and Node. All new production code is independent Lean; the package installs
below are reference clients and test tooling. Start at the repository root.
The local compiler commands run from `formal/lean4`, with an explicit package
directory. Coordinate the lock path with other work on the same machine.

```bash
cd formal/lean4
ulimit -v 8388608
export LEAN_NUM_THREADS=1
export LEAN_STACK_SIZE_KB=65536
export MIMALLOC_ARENA_RESERVE=67108864
flock /tmp/factoidal-lean-9833.lock lake -d evm-cleanroom build EVMCleanroom evm-call-transaction evm-subset
flock /tmp/factoidal-lean-9833.lock lake -d evm-cleanroom -f lakefile-blob-call.toml build evm-blob-call
flock /tmp/factoidal-lean-9833.lock lake -d evm-cleanroom -f lakefile-transaction-list.toml build evm-transaction-list
cd evm-cleanroom
python3 scripts/check-active-ledger.py
python3 scripts/test-active-ledger.py
python3 scripts/check-axiom-output.py --selftest
flock /tmp/factoidal-lean-9833.lock python3 scripts/check-axiom-output.py
python3 scripts/check-transaction-list-axioms.py --selftest
flock /tmp/factoidal-lean-9833.lock python3 scripts/check-transaction-list-axioms.py --require-head --out /tmp/list-claims.json --transcripts-dir /tmp/list-axioms
python3 scripts/check-blobhash-axioms.py --selftest
flock /tmp/factoidal-lean-9833.lock python3 scripts/check-blobhash-axioms.py --require-head --out /tmp/blob-claims.json --transcripts-dir /tmp/blob-axioms
python3 scripts/check-identity-axioms.py --selftest
flock /tmp/factoidal-lean-9833.lock python3 scripts/check-identity-axioms.py
python3 scripts/check-transaction-list-transport.py .lake/build/bin/evm-transaction-list
python3 scripts/check-transaction-json-guard.py
```

The default JSON suite invokes only guarded executables. The optional nine
old/new spelling comparisons require the separately retained development
binaries listed in provenance; they are not needed for the default CI gate.
Do not run the large attack against an unguarded parser to reproduce the
guarded regression: the default suite already checks its structured refusal.

The twelve codec-parity inputs and exact baseline stdout/exit/stderr are in
`codec-parity-fixtures-and-before.json`. For each row, write `inputText`
unchanged to a temporary file; run `evm-call-transaction` with
`--dangerously-enable-unverified-keccak --call-transaction FILE` for mode
`ordinary`, or `evm-blob-call` with
`--dangerously-enable-unverified-keccak --batch FILE` for mode `blob`.
Compare complete stdout, stderr and exit status to that row. The original
baseline capture does not embed a source/native identity, so this is a
recorded compatibility check, separately scoped from the source-bound paired
timing results.

Install the exact existing JavaScript dependencies and verify the lock hashes:

```bash
npm ci --prefix scripts/differential --ignore-scripts --no-audit --no-fund
npm install --prefix scripts/eels --ignore-scripts --no-audit --no-fund
printf 'cc95a62e125486d2de9a28cb5fc61c098b955aa22c2dd0b3dc0b19f2df770425  scripts/differential/package-lock.json\n' | sha256sum --check
printf '2f5caf7dd31ee1d2b36290788e509110955005c28302ed0f038dadbc2bf6c6c7  scripts/eels/package-lock.json\n' | sha256sum --check
```

Set `EVM_GETH_EXE` to the `evm` executable from Geth alltools
`1.17.10-1df30b18`. The archive SHA-256 is
`f991c32e5b7bb68db97a1b06d50c7c06f6aa9ae84d8f6f9b2301dc02cad2a7cf`;
the executable SHA-256 is
`d8cfddad15a8c601e7b069bc5973ad073dbc2d632b8c5ab50e513ef27c53d6da`.
The download and extraction commands are retained in
`.github/workflows/evm-blob-call.yml` at the repository root.

```bash
node scripts/differential/transaction-list.mjs .lake/build/bin/evm-transaction-list
node scripts/differential/blobhash-transactions.mjs .lake/build/bin/evm-blob-call .lake/build/bin/evm-call-transaction
node scripts/differential/identity-transaction.mjs .lake/build/bin/evm-call-transaction
node scripts/differential/blob-call.mjs .lake/build/bin/evm-blob-call
node scripts/eels/call-transaction-differential.mjs .lake/build/bin/evm-subset
```

These tests use full client execution and exact observations. Host signature
recovery, transaction/receipt encoding and trie construction are reference
operations; they do not authenticate the Lean runner's decoded input.

## London audit and formula lane

From `formal/lean4`, retain the compiler lock and environment above:

```bash
flock /tmp/factoidal-lean-9833.lock lake -d evm-cleanroom -f lakefile-london.toml build evm-header-fees
flock /tmp/factoidal-lean-9833.lock lake -d evm-cleanroom env lean evm-cleanroom/EVMCleanroom/HeaderFees.lean > /tmp/london-axioms.txt
python3 evm-cleanroom/scripts/check-london-claims.py --selftest
python3 evm-cleanroom/scripts/check-london-claims.py --report /tmp/london-axioms.txt
cd evm-cleanroom
python3 scripts/check-london-header-fees.py --generate /tmp/london-input.tsv /tmp/london-expected.jsonl
.lake/build/bin/evm-header-fees --batch /tmp/london-input.tsv > /tmp/london-observed.jsonl
python3 scripts/check-london-header-fees.py --check /tmp/london-expected.jsonl /tmp/london-observed.jsonl
```

The active London manifest is separate from the unchanged dated manifest.
Its six theorem/source pins and all four corruption controls must pass.

## Reproduce the paired measurements

Build the ordinary and blob executables from predecessor implementation
`85da2a6b307c0a0269257344d889051ce6902e82` in a separate checkout, using the
same toolchain and process environment. Do not share its `.lake` directory
with the new checkout. From the new `formal/lean4/evm-cleanroom` directory,
set `TRANSACTION_TIMING_BEFORE` to that predecessor's absolute
`.lake/build/bin` directory and run:

```bash
flock /tmp/foafnaut-timing.lock flock /tmp/factoidal-lean-9833.lock \
  node scripts/differential/transaction-cli-timing.mjs \
  "$TRANSACTION_TIMING_BEFORE" 85da2a6b307c0a0269257344d889051ce6902e82 \
  .lake/build/bin 91cae62479cbd3a13775b3dd15f502646c11db41 \
  evidence/2026-11-24-transaction-list/timing-blob-request.json
```

The script checks every full result while timing process launch through exit.
The recorded ordinary median rose from 31.84 to 33.37 ms and its maximum
from 60.40 to 114.71 ms; the blob median rose from 31.22 to 32.29 ms.
This is a local observation on two synthetic paths, not a throughput or
stable latency guarantee. The full distributions and paired differences
remain in the JSON report.
