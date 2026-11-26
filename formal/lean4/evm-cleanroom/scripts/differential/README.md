# Independent EVM differential laboratory

**Scope:** raw bytecode, one execution frame, Prague rules, no accounts or transaction
envelopes. This is **not** Ethereum mainnet replay and is not full EELS conformance.

The two implementations being compared are:

1. Our Lean 4.33.1 `EVMCleanroom.run` executable, built as `lake exe evm-subset`.
2. The independently maintained `@ethereumjs/evm@10.1.3`, configured with
   `Common({chain: Mainnet, hardfork: Hardfork.Prague})` and `runCode()`.

The npm package lock pins transitives and SHA-512 tarball integrity. Always use
`npm ci`, not a fresh dependency resolution.

## Repeat a test locally

From `formal/lean4/evm-cleanroom/`:

```sh
lake build
npm ci --prefix scripts/differential --ignore-scripts --no-audit --no-fund
mkdir -p .lake/differential
node scripts/differential/generate.mjs \
  --seed 20261119 --count 10000 \
  --out .lake/differential/corpus.jsonl
node scripts/differential/run.mjs \
  --corpus .lake/differential/corpus.jsonl \
  --out .lake/differential/report.json \
  --failures .lake/differential/failures.jsonl
```

The generator uses a reproducible xorshift32 PRNG and emits JSONL with a
stable test ID, bytecode, explicit fork, gas budget, fuel and category.
`generate.mjs` publishes the corpus SHA-256. No nondeterministic data,
network calls, timestamps, or random seeds enter the test corpus.

The runner converts the corpus into TAB-separated batch input. The Lean CLI
executes the entire corpus in **one process**, emits one result per case, and
the runner compares these directly to independently executed EthereumJS
results. Output contains the corpus SHA-256, per-category counts, matching
counts, mismatches, and the first complete counterexamples. All mismatches
are preserved as line-delimited JSON with original input and both outputs.

The tested observables are status, gas remaining, program counter, halted
flag, complete stack and memory allocation size, plus **the complete allocated
memory snapshot up to 4,096 bytes**. The CLI and oracle record the number
of observed bytes and a truncation flag. Any truncated snapshot is retained as **unsupported**, making the run
incomplete and failing CI; it is not a semantic mismatch or a pass.
All 256-bit numbers
are lossless decimal strings. This still does not prove behavior of larger
memory frames, exceptional rollback, storage or external calls.

### Strict reporting rules

- Every generated case counts. No hidden exclusions or skips.
- The corpus now includes deliberately exceptional outcomes: out-of-gas
  (including enormous offsets), stack underflow, invalid jumps and invalid
  opcodes. Both engines must agree with the declared **error category**.
  Exceptional gas burning and state rollback are **not compared**.
- A generator-side category-to-expected-error sanity check prevents
  a mislabeled exceptional case from masquerading as an EVM discrepancy.
- Exact duplicate execution inputs are reported; the runner refuses any
  corpus with over 5% duplicate inputs.
- Oracle errors (host/runtime failures) are separate from EVM disagreements.
- A missing result, non-JSON result, mismatched number of results or invalid
  corpus record makes the run fail.
- The runner does **not** count an EELS fixture merely parsed by the
  `eels-state-preflight.mjs` utility as an executed test.
- The Solidity compilation path, account/storage semantics, logs,
  revert/return data, precompiles, fork transitions and transaction validation
  remain entirely out of scope.
- Do not equate two-engine agreement with a mathematical proof of conformance:
  both engines could implement the same incorrect interpretation of a rule.

### Corpus taxonomy

The generator deliberately stratifies arithmetic, big integer PUSH cases,
memory reads/writes, 32-byte alignment/cross-boundary accesses, stack
manipulation, conditional/unconditional jumps, gas and program-counter
instructions, plus deliberately failing cases and an untaken JUMPI with
an invalid destination. The current gate uses **18 categories**, including
five exceptional categories. Error *classification* is checked independently;
exceptional gas/state behavior, EVM returndata and transaction-state effects
are not covered.

EthereumJS `step` events provide a separate **dynamic instruction coverage**
histogram. These are actual reference-EVM opcode executions, not merely
syntactic occurrences or generated-case categories, and not Lean-side traces.
CI validates histogram totals and minimum variety in the evidence manifest.

**High-priority extensions:** exceptional gas burn and rollback fidelity;
actual Lean-side instruction traces; real EELS-generated state test *execution*
with post-state-root comparisons; verified bytecode provenance for mainnet
samples; semantic coverage-driven generator expansion; review and retention of
minimised concrete disagreements as permanent regression cases.

### Latest checked evidence

[10,000-case CI run with dynamic coverage](https://github.com/danbri/factoidal-core/actions/runs/44627665734),
seed `20261119`, corpus SHA-256
`610012bd5b278c5e4d08545560beed11910e01c0233ad8f9c9a4c9a52e0a2efb`:

- 10,000 compared; **10,000 matched; 0 engine disagreements**.
- 9,733 distinct `(fork, bytecode, gas, fuel)` input combinations.
- 2,775 matching exceptional outcome *categories*.
- 40,289 dynamic EthereumJS opcode-step events across 24 different opcodes.
- Zero oracle execution errors and zero unsupported cases in the deliberately
  restricted corpus.

This evidence is stronger than the original 240-case smoke test, but it
remains *synthetic subset differential testing*. It is not a set of
10,000 official state-root comparisons, nor a proof of consensus soundness.

### Counterexample lifecycle and harness self-tests

The CI comparator has three independent negative controls: two cases with
deliberately falsified expected outcomes (which must fail and reproduce with
identical discrepancy reasons), plus a memory-access case whose successful
execution exceeds the 4 KiB snapshot limit (which must be **unsupported**,
never accepted as a pass). A bounded delta-debugger is also exercised on
a deliberately falsified case, requiring the same mismatch signature.

To re-execute any saved mismatch in isolation:

```sh
node scripts/differential/reproduce.mjs \
  --failures .lake/differential/failures.jsonl \
  --id synthetic-20261119-000017 \
  --out .lake/reproduced
```

To seek a smaller counterexample while preserving the same disagreement
signature, hard fork, gas and fuel:

```sh
node scripts/differential/minimize.mjs \
  --failures .lake/differential/failures.jsonl \
  --id synthetic-20261119-000017 \
  --out .lake/minimized --max-runs 64
```

The IDs above are examples; a real mismatch must exist in the supplied
archive. Neither a reduced input nor a synthetic negative control is an
independently confirmed Ethereum semantic bug. Human review is required.

### Evidence retention

CI archives the exact JSONL corpus, its SHA-256 manifest, the committed
dependency lockfile, machine-readable report, dynamic opcode histogram,
negative controls, minimisation/reproduction evidence and full mismatch
records as a GitHub Actions artifact. The `evidence-manifest.json` links
the source commit, Lean toolchain, npm dependency lock and report/input
files by hashes. CI verifies the full outcome partition and the dynamic
opcode histogram. The generator SHA-256 is pinned in the workflow; any
change to the 10k-case corpus requires an explicit reviewed hash update.
Artifacts are retained for 30 days. PR builds use a fixed seed and count, while larger
local runs can use new seeds and much higher counts. Generator count is
explicitly bounded to 100,000 records per invocation so resources and corpus
provenance remain manageable.

Upstream EthereumJS source: https://github.com/ethereumjs/ethereumjs-monorepo .
Proof trust and Ethereum/EELS boundaries:
[../../SOUNDNESS.md](../../SOUNDNESS.md) ·
[../../ROADMAP.md](../../ROADMAP.md).
