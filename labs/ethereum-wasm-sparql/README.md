# Ethereum EVM bytecode → WebAssembly → Factoidal SPARQL

A reproducible demonstration of SPARQL 1.1 §17.6 invoking **actual WASM
generated from EVM runtime bytecode**, not simply a JS Ethereum package.

## What is executed

The source is valid, hand-authored EVM runtime bytecode, not deployed code or
claimed Solidity compiler output:

    6004356024359010155f5260205ff3

It expects two ABI-encoded uint256 arguments following a 4-byte selector:
account balance, proposed transfer amount. Its ABI Boolean output is
balance >= amount.

    PUSH1 0x04 ; CALLDATALOAD   # balance
    PUSH1 0x24 ; CALLDATALOAD   # proposed amount
    SWAP1 ; LT ; ISZERO        # !(balance < amount)
    PUSH0 ; MSTORE             # ABI bool at memory[0..31]
    PUSH1 0x20 ; PUSH0 ; RETURN

The compiler symbolically executes the EVM stack **with respect to the
program, not the query inputs**. It now emits two deterministic, import-free
WebAssembly modules from the same EVM source:

- **49 bytes**: a uint64-restricted evaluate(i64,i64)->i64, registered as
  urn:factoidal:ethereum-wasm#canTransfer.
- **91 bytes**: a full unsigned uint256 predicate with four i64 limbs per
  input word, i.e. evaluate(i64 x 8)->i64, registered as
  urn:factoidal:ethereum-wasm#canTransfer256. The generated WASM uses
  unsigned lexicographic comparisons rather than silently narrowing 256 bits.

Both are callable through the public Factoidal/Comunica-style
registerExtensionFunction API.

## SPARQL query

    PREFIX ex: <https://example.org/ethereum-demo/>
    PREFIX evm: <urn:factoidal:ethereum-wasm#>
    SELECT ?proposal ?balance ?amount ?allowed WHERE {
      ?proposal a ex:TransferProposal ;
                ex:balance ?balance ;
                ex:amount ?amount .
      BIND(evm:canTransfer(?balance, ?amount) AS ?allowed)
    }

A further query joins every calculated Boolean to RDF provenance triples
for the function IRI itself: the exact source EVM SHA-256, generated WASM
SHA-256, and an explicit assuranceStatus of
"differential-tested-not-proved". Query answers expose their computational
provenance without asserting a nonexistent proof.

The second query invokes evm:canTransfer256 over full-width values such as
2^255 and 2^200. In that mode the earlier 2^64 case is valid; a new
2^256 case remains an explicit SPARQL expression error.

The companion FILTER query returns three proposals: Alice, Carol, and a
uint64-boundary case. Bob proposes spending more than his sample balance,
and is rejected. A fifth row with a 2^64 balance is explicitly
outside the translation's domain: it becomes a SPARQL expression error,
unbound in BIND and excluded by FILTER. The data are illustrative
hypothetical transfer proposals, not actual Ethereum balances.

Changing a single source EVM opcode (remove SWAP1) changes the
generated WASM and the SPARQL query results. The module is not a table of
precomputed outputs.

## Reproduction

Node >=22:

    node --test labs/ethereum-wasm-sparql/evm-to-wasm.test.mjs
    node --test labs/ethereum-wasm-sparql/evm-to-wasm-256.test.mjs

This checks 400 input pairs against a separately implemented test-only EVM
uint256 bytecode evaluator, including 64-bit boundaries, plus negative
tests of unsupported opcodes and input-domain errors.

The separately gated, integrity-pinned EthereumJS 10.1.3 Cancun suite
executes the *actual source EVM runtime bytecode* against 400 uint64 and
400 full uint256 ABI input pairs (not the symbolic compiler tree):

    npm ci --prefix labs/ethereum-wasm-sparql --ignore-scripts --no-audit --no-fund
    node --test labs/ethereum-wasm-sparql/ethereumjs-oracle.test.mjs

The initial two 400-case uint64 gates passed in GitHub Actions run
44787504225. The expanded full-uint256 comparison runs in the same
independently pinned EthereumJS workflow; see the current PR checks.

To execute Factoidal queries as well, install Factoidal's normal Lean WASM
engine assets using the repository web-release mechanism (or an npm
package installation), then:

    node labs/ethereum-wasm-sparql/run.mjs
    node --test npm/factoidal/test/ethereum-wasm-sparql.test.mjs

The end-to-end npm test is also gated by the existing npm package suite; its
first execution passed both new SPARQL tests in run 44787504468 (2,144 total
npm tests passed, zero failed or skipped).

## Assurance boundaries

- EVM words are **256-bit**. The original emitter deliberately accepts
  uint64 inputs; the new full-width emitter uses four unsigned 64-bit
  limbs for each EVM word. Both refuse out-of-domain values. The latter
  does **not** turn this into a general EVM bytecode compiler: only the
  stated symbolic comparison/Boolean fragment is lowered.
- Supported source instructions: PUSH0, PUSH1..32 with bounded constants,
  CALLDATALOAD at static offsets 4/36, SWAP1, LT, ISZERO, one MSTORE(0),
  and RETURN(0,32). Unsupported opcode, dynamic offset, invalid ABI shape,
  noncanonical typed input or out-of-domain value is refused, never coerced.
- No gas, global state, storage, CALL, transaction or consensus semantics are
  represented by this pure predicate. It does **not** prove a real ERC-20
  transfer would succeed. The source is Ethereum-compatible bytecode for
  a deliberately simple test function.
- The generated WASM module has no imports. Host term marshaling, WASM
  execution and the SPARQL function registry remain trust boundaries.
- **No Lean EVM→WASM semantic-preservation theorem exists yet.** The
  differential tests are evidence, not a universal correctness proof.
  Source code/bytecode, WASM hash, input-domain and theorem status are
  reported separately. Query text cannot upload executable code.

## Substantive pure EVM computation: transfer eligibility

The original canTransfer(balance,amount) simply compared two numbers.
The new 45-byte EVM runtime examines **seven unsigned uint256 inputs**:

    eligible = balance >= amount
            && allowance >= amount
            && currentBlock >= unlockBlock
            && paused == 0
            && frozen == 0

These are explicit RDF-supplied state snapshots, not independently authenticated
live Ethereum account/contract state. Satisfying this illustrative policy
does not imply an actual ERC-20 transfer would succeed.

### Complete EVM bytecode and disassembly

    600435604435901015602435604435901015166064356084359010151660a435151660c43515165f5260205ff3

    60 04 35 60 44 35 90 10 15
      CALLDATALOAD(balance); CALLDATALOAD(amount); SWAP1; LT; ISZERO
      # Balance >= amount
    60 24 35 60 44 35 90 10 15 16
      CALLDATALOAD(allowance); CALLDATALOAD(amount); SWAP1; LT; ISZERO; AND
      # Allowance sufficient AND previous condition
    60 64 35 60 84 35 90 10 15 16
      CALLDATALOAD(currentBlock); CALLDATALOAD(unlockBlock); SWAP1; LT; ISZERO; AND
      # Block height >= unlock height AND previous
    60 a4 35 15 16
      CALLDATALOAD(paused); ISZERO; AND
    60 c4 35 15 16
      CALLDATALOAD(frozen); ISZERO; AND
    5f 52 60 20 5f f3
      PUSH0; MSTORE; PUSH1 0x20; PUSH0; RETURN

Offsets 0x04, 0x24, 0x44, 0x64, 0x84, 0xa4 and 0xc4 are the ABI
argument positions after the 4-byte selector. The runtime bytecode is
hand-authored, not deployed contract code or Solidity compiler output.

The EVM stack-symbolic compiler in evm-policy.mjs emits import-free
WebAssembly with signature (i64 × 28) → i64. Each EVM 256-bit word is
carried as four unsigned 64-bit limbs. Multi-limb unsigned comparisons
and zero tests preserve the complete 256-bit domain.

Run the complete wasmAdd-style example:

    node labs/ethereum-wasm-sparql/policy-like-wasmAdd.mjs

It compiles source EVM bytecode, instantiates the generated WASM,
registers the resulting predicate in Factoidal, runs the RDF/SPARQL query,
and prints the compiled opcode trace and computed results.

The independent suites compare 400 complete seven-word inputs against
a separate declarative Boolean policy and another 400 against the pinned
EthereumJS Cancun EVM executing the original 45-byte program.
Factoidal BIND/FILTER integration and source-opcode mutation are tested
separately; an EVM→WASM semantic-refinement theorem remains unproved.

More intrinsically Ethereum-specific future examples include an
AMM getAmountOut quote with uint256 fee arithmetic, vesting claims at a
specified block, and Merkle proof verification for an airdrop.
## Next demonstrations

1. RDF over official EELS fixture IDs, expected post-state roots, forks
   and execution evidence; use compiled EVM functions as query predicates.
2. ERC-20/721 log RDF joined to account history, with pure EVM-derived
   ABI decoders and explicit log-vs-state assurance limits.
3. SPARQL search for behaviour changes between two versions of actual
   deployed bytecode, returning reproducible counterexample inputs.
4. A proof-carrying extension-function catalogue linking source EVM hash,
   emitted WASM hash, supported domain, compiler revision, differential
   tests and a future Lean refinement theorem.

The Ethereum implementation remains separately under development in
draft PRs #642, #655–#669 and #676. This demo does not substitute for
complete contract execution, world-state replay or client interoperability.

Formal semantic-preservation proof work, including the 8-limb unsigned
comparison lowering, is tracked in issue #678.
