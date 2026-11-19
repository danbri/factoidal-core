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
  --seed 20261119 --count 4096 \
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
flag, complete stack and memory allocation size, plus the first 32 bytes of
memory interpreted as an unsigned big-endian word. All 256-bit numbers are
lossless decimal strings. **Memory outside those first 32 bytes is not directly
compared**, even if the program writes there. Add more observables before
claiming full memory-effect conformance.

### Strict reporting rules

- Every generated case counts. No hidden exclusions or skips.
- An independent-EVM exception in the current success-only corpus is
  classified as a failure, never silently accepted as a pass.
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
instructions. The initial corpus exercises *successful* execution paths,
and does not establish exceptional-halt, out-of-gas, gas-refund, or
transaction-state coverage.

**High-priority extensions:** independently checked exceptional outcomes;
dynamic opcode coverage (not merely generator categories); real EELS-generated
state test *execution* with post-state-root comparisons; verified bytecode
provenance for mainnet samples; automatic counterexample minimisation and
retention; continuous regression of all previously found divergences.

### Evidence retention

CI archives the exact JSONL corpus, its SHA-256 manifest, the committed
dependency lockfile, machine-readable report and full mismatch records as a
GitHub Actions artifact. PR builds use a fixed seed and count, while larger
local runs can use new seeds and much higher counts. Generator count is
explicitly bounded to 100,000 records per invocation so resources and corpus
provenance remain manageable.

Upstream EthereumJS source: https://github.com/ethereumjs/ethereumjs-monorepo .
Proof trust and Ethereum/EELS boundaries:
[../../SOUNDNESS.md](../../SOUNDNESS.md) ·
[../../ROADMAP.md](../../ROADMAP.md).
