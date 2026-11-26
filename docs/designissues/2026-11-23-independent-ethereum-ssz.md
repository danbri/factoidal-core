# Independent Ethereum SSZ byte proofs

Design and proof task: https://github.com/danbri/factoidal-core/issues/834.
Full client acceptance: https://github.com/danbri/factoidal-core/issues/725.

## Implementation boundary

Ethereum protocol logic is implemented in repository-owned Lean 4. The
standalone consensus package stays on `leanprover/lean4:v4.33.1`, with no
external Lake packages. Specifications and published test vectors are
references. Test oracles do not supply the executable's answers.

The package selects three local source modules through a Lake library:

| Module | Role |
| --- | --- |
| `L4Factoidal.Crypto.SHA2` | Existing pure Lean hash algorithms |
| `L4Factoidal.Crypto.SHA2Theorems` | Existing digest-width and padding-size proofs |
| `L4Factoidal.Crypto.SHA2Tests` | Existing compiled test guards |

The library references the original files in place. It neither copies them
nor imports the broad `L4Factoidal` root, `SHA2Native`, HACL bindings or an
external cryptographic implementation. The selected files were identical
on consensus base `7c50781db078f03c573ee32c38551c4fba2ac015` and inspected
main `fd28e39ce51a83cf0c6e536fe214054171e242c0`.

## Byte verification

An SSZ chunk contains bytes and a proof that its size is 32. The pair
function hashes the left chunk followed by the right chunk with the
existing pure `sha256`. The existing digest-width theorem constructs the
result's width witness. No hash callback is exposed by the byte verifier.

A single branch must have a positive depth, the exact number of witnesses,
and 32-byte chunks throughout. Its executable calculation uses the
existing ordered `foldProof`, with the concrete pair hash.

A multiproof first checks claim count and depth, rejects empty, repeated
or ancestor-related claims, and computes the existing descending helper
positions. Exact leaf and witness counts bind the supplied bytes to those
positions. A frontier reducer repeatedly combines the greatest indexed
node with its sibling. Each successful step consumes both children and
inserts their parent. A missing sibling or an already present parent is an
error. Success requires exactly one remaining node, at root index 1.

The reducer receives fuel from the admitted frontier size. This bounds
the number of combination attempts. It does not establish a CPU deadline
or prove the runtime's memory behaviour. The helper calculation and list
frontier operations have quadratic cases within the configured bounds.

## Admission and protocol meaning

The API distinguishes three results:

- A well-formed proof whose calculated root matches the supplied root.
- A well-formed proof with a different calculated root.
- A malformed or out-of-budget request, reported as an error.

The current command-line policy allows at most 64 claims and depth 64;
callers may lower these limits. These are implementation resource limits,
not Ethereum consensus rules. A generalised index does not by itself
establish that a node exists in a particular BeaconState layout.

The expected root must also be 32 bytes. This is a stricter input-domain
check than the pinned Python reference's plain byte comparison, which
returns false for a wrong-width expected root. The difference is explicit
in the tests; it is not reported as complete API equivalence.

The JSONL interface parses and validates requests in Lean. The line limit
is applied after the standard input reader has allocated the line and
before JSON parsing. It does not protect the initial read allocation.
Hash requests have a separate 65,536-byte limit. Proof calculation calls
no host hashing service.

## What the evidence can establish

The structural model assigns each node a value and requires a parent's
value to be the ordered hash of its children. The proved conditional
reduction invariant preserves agreement with that assignment. This is distinct from
proving collision resistance or establishing that the caller's expected
root came from an authenticated beacon block.

The SHA-256 module's existing proofs establish output width and padding
size properties. They do not prove all compression rounds against an
independent FIPS specification. Known-answer and differential tests check
values; they do not turn that gap into a theorem. Constant-time behaviour
and compiler/runtime correctness also remain unproved here.

Tests construct complete binary trees independently in Python, obtain
roots before extracting proofs, and compare the actual Lean executable.
Sparse depth-boundary trees use precomputed zero-subtree roots. Tampering,
wrong widths, incorrect witness counts, claim overlap and resource limits
exercise rejection and mismatch paths. Comparator mutations check that
the test harness rejects forged outputs. Python `hashlib` is a test
oracle only.

Dependency checks inspect the package declarations, source imports and
compiled/link artefacts. These are audits of the inspected build, not
mathematical proofs of the compiler or of software supply-chain security.
The dated worknote records the exact executed checks and their results.

## Normative sources and remaining client work

The positional and proof contract is pinned to
`ethereum/ssz-specs@4c2f08805080c6b4b12ede7bf48ad6a80229f4b1`:

- `src/ssz/gindex.py`, blob `e520ac9f89b2eb114174a0c83bf7e6187ef40304`.
- `src/ssz/proofs.py`, blob `ed6c558390d2f5ca2b66d875089095dfc9b19a6e`.
- `src/ssz/verification.py`, blob `70fc895a596f600d4df18569043c3d180fb87a4d`.

Full SSZ codecs, type layouts and official fixture completeness remain
work under the client goal, together with beacon transitions, BLS,
finality, authenticated roots and EL/CL interoperability. This byte-proof
component does not close those requirements.
