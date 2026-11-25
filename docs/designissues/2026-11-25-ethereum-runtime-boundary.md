# Ethereum: build-time proofs and native runtime execution

2026-11-25. Decision implemented for the Lean 4.33.1 witness and transaction
list executables. The [witness admission design](../20261125-evm-witness-admission.md)
records the protocol model, theorem scope and remaining execution gaps.

## Decision

Use Lean's elaborator, tactics and kernel during development and CI to
construct and check theorems about the implementation. Compile the protocol
functions ahead of time to native code. Account admission and transaction
execution must not invoke theorem search, elaboration or kernel checking.

At runtime, an Ethereum Merkle proof is input data. The compiled verifier
hashes bytes, decodes RLP and follows trie references. A successful hash
comparison still runs after compilation; the mathematical proof fields
connecting that computation to its specification are erased. The audited
`CheckedNode`, `Hop` and path result retain their computational data, without
storing those proof terms. Lean's ordinary arithmetic, arrays, I/O, task
support and reference-counted memory management remain runtime dependencies.
See the [generated-code and native audit](../../formal/lean4/evm-cleanroom/evidence/2026-11-25-mpt-witness/runtime-boundary.after-pruning.json).

## Startup dependency and repair

The original `Lean.Data.Json` umbrella import included JSON quotation
elaboration. Narrowing it to `Lean.Data.Json.Parser` and
`Lean.Data.Json.FromToJson.Basic` removed that direct import but left the
full proof-assistant startup in the executable. In the pinned compiler,
[`emitMainFn`](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Compiler/LCNF/EmitC.lean)
selects `lean_initialize()` when
[`usesModuleFrom`](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Compiler/LCNF/EmitUtil.lean)
finds any runtime `Lean.*` import. JSON data routines meet that condition.
The actual initializer called the full Lean library and C++ kernel. The
[intermediate audit](../../formal/lean4/evm-cleanroom/evidence/2026-11-25-mpt-witness/runtime-boundary.json-import-only.json)
preserves this unsuccessful import-only repair.

Keep the narrow JSON imports and explicitly select the ordinary runtime
initializer in the two reviewed configurations:
[witness](../../formal/lean4/evm-cleanroom/lakefile-witness.toml) and
[transaction list](../../formal/lean4/evm-cleanroom/lakefile-transaction-list.toml).

```toml
moreLeancArgs = ["-Dlean_initialize=lean_initialize_runtime_module"]
```

This is native startup build glue. It uses the same initializer as the
repository's existing [Wasm shim](../../formal/lean4/Wasm/l4_shim.c).
Generated module initializers, argument handling, task setup and protocol
functions remain in place. Build-time kernel checking remains unchanged.
The selection applies only to this reviewed runtime import closure, whose
`Lean.*` dependencies provide JSON data routines. Re-audit it when the
toolchain, import closure or startup configuration changes; do not extend it
to an executable that uses Lean frontend or expression-checking APIs.

## Measured result

The preserved x86-64 Linux binaries have these sizes:

| Executable | Before, bytes | After, bytes |
| --- | ---: | ---: |
| `evm-transaction-list` | 121,089,912 | 6,970,160 |
| `evm-witness-proof` | 120,632,352 | 6,505,840 |

The [before report](../../formal/lean4/evm-cleanroom/evidence/2026-11-25-mpt-witness/runtime-boundary.before-pruning.json)
and final audit retain full binary and source hashes. Actual final entry
objects import `lean_initialize_runtime_module`; disassembled `main` calls
it. The [native gate result](../../formal/lean4/evm-cleanroom/evidence/2026-11-25-mpt-witness/runtime-gate.json)
contains no elaborator, compiler, type-checker, kernel or full-bootstrap
symbols. Seven explicitly allowed `Init.MetaTypes` configuration defaults
remain as BSS data, with no callable Meta procedures.

All 189 witness/primitive responses and all 36 transaction-list outcomes
match their preserved pre-change outputs; see the
[complete output comparison](../../formal/lean4/evm-cleanroom/evidence/mpt-runtime-output-parity.json).
The [216-invocation benchmark](../../formal/lean4/evm-cleanroom/evidence/mpt-benchmark.json)
records two fixtures with process startup included. It does not establish
client throughput or general Ethereum execution performance.

## Trusted computing base and evidence limits

The Lean compiler and runtime, C compiler/linker, native startup selection,
operating system and hardware remain trusted. Source theorems do not certify
that toolchain or startup glue. The
[source/axiom checker](../../formal/lean4/evm-cleanroom/scripts/check-witness-axioms.py)
and [native dependency gate](../../formal/lean4/evm-cleanroom/scripts/check-witness-runtime.py)
bind the reviewed sources and allowed imports to actual executable hashes.
These controls must accompany future changes to this boundary.

The environment prohibited `ptrace`, so the audit obtained no dynamic
syscall trace. Its claims rest on source and generated-code inspection,
actual native symbols and dependencies, and complete output comparisons.
The verifier still depends on the supplied state root and the explicitly
opted-in, unverified Keccak implementation. This startup decision establishes
neither canonical-chain trust nor a complete Ethereum client.
