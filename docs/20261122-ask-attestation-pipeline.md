# Checked ASK attestation computation

Work item: [Local ASK attestation, issue 745](https://github.com/danbri/factoidal-core/issues/745).

The implementation now has one deterministic computation from original
N-Triples bytes and a 32-byte salt to a public journal. It parses the
original bytes as strict UTF-8 and RDF 1.1 N-Triples, admits a bounded
policy, runs the selected checked inference phases, and calls the existing
SPARQL ASK evaluator. It hashes the original bytes rather than an RDF
canonicalisation. The internal graph has set identity; duplicate input
triples do not change its ASK answer but do change the byte commitment.

The public journal is an execution output. Producing it natively is not
producing a zero-knowledge proof. A proof backend must run this same
computation under a pinned guest identity; a verifier must check the proof
and authorise its policy and context. Backend build and receipt results
are recorded separately from the kernel properties in this note.

## Admitted profile

The query is SPARQL 1.1 ASK with basic triple patterns, empty patterns and
joins of those patterns. Prefix and base declarations use the existing
parser. SELECT, CONSTRUCT, DESCRIBE, dataset clauses, named graphs,
services, property paths, subqueries, filters, assignments, grouping,
solution modifiers and trailing VALUES are refused. The admission check
does not silently ignore unsupported clauses. It admits no expressions,
so host functions, time and random functions cannot affect its result.

The initial profile also rejects a query whose explicit variable name
collides with a variable introduced by the existing ASK blank-node
rewrite. For example, `_:x` and `?_bnode_x` must not become one variable.
Admission computes those introduced names using the actual rewrite
functions, then checks disjointness. A checked theorem covers this
condition. Ordinary blank-node ASK remains supported. The parser already
rejects user blank-node labels reused across nested group scopes; tests
cover both group orders, valid distinct labels and anonymous blank nodes.
The general query engine's naming convention is unchanged by this
restricted-profile guard.

SPARQL-RL uses the existing parser, validators, dependency analysis and
evaluator. The initial profile admits positive triple-only rules with
finite terms. Fresh blank nodes or quoted triple terms in heads,
assignments, aggregates, negation, filters, DATA blocks and imports are
refused. Body blank nodes which the existing parser rewrites to variables
keep that parser's semantics. The profile's shape implies every admitted
rule is a general rule and satisfies the existing `NegBlind` premise;
`AdmissionTheorems.lean` checks those implications.

Regime byte **0** runs rules over the input set. Regime **1** first runs
the complete checked `RDFS.FullClosure` rule and axiom table, then rules.
No other regime byte is accepted. The optional datatype map is empty.
The finite `rdf:_n` slice is collected from input and policy constants.
The existing full seed includes RDF 1.2 axioms; this profile names that
seed and does not claim to implement complete RDF 1.1 model-theoretic
entailment. Rules do not feed back into another RDFS phase.

The [checked saturation note](20261122-checked-saturation.md) describes
the real final convergence checks. Exhaustion never reaches ASK and never
becomes a successful false. SPARQL-RL returns the complete graph, including
the input; it does not query only the newly inferred triples.

## Exact protocol bytes

All domain strings below are UTF-8 followed by one zero byte. `U64(n)` is
an eight-byte unsigned big-endian integer; `LP(b) = U64(length(b)) || b`.

```text
graphMessage = "factoidal.ask.graph.v1\0" || salt32 || LP(originalBytes)
policyMessage = "factoidal.ask.policy.v1\0" || LP(encodedPolicy)
contextMessage = "factoidal.ask.context.v1\0" || LP(contextBytes)
```

`encodedPolicy` is the zero-terminated domain
`factoidal.ask.ordered-nt11-bgp11-positive-rl-fullseed-v1`, followed by the
one-byte regime, nine `U64` fields in the following order, `LP(queryUtf8)`
and `LP(rulesUtf8)`. Exact policy text is authenticated. Textually different
equivalent queries may have different policy hashes. A change to the
named semantics requires a new protocol version.

| Field | Fixed request profile |
| --- | ---: |
| maxInputBytes | 65536 |
| maxPolicyBytes, query plus rules | 16384 |
| maxContextBytes | 4096 |
| maxTriples, including retained inference state | 256 |
| maxPatterns per ASK or rule head/body | 4 |
| maxRules | 16 |
| maxRdfsRounds | 32 |
| maxRuleRounds per layer | 32 |
| maxIntermediate work estimate | 1000000 |

The typed library API permits other admitted limits, and includes all of
them in the policy encoding. The byte request/export API fixes the table
above. Original data and policy bytes must be bounded by the host before
it allocates Lean arrays; Lean validates their lengths again. The CLI
reads bounded chunks and refuses oversized files. Join candidate work is
checked conservatively before ASK or rule joins. Retained graph and
convergence bounds are checked by the actual runners. A universal peak
allocation or wall-clock theorem is not established by these checks.

The three 32-byte SHA-256 digests are followed by one Solidity ABI Boolean
word: 31 zero bytes and a final byte 0 or 1. The journal is therefore the
128-byte encoding of `(bytes32, bytes32, bytes32, bool)`.

The exported managed Lean result is `(UInt8, ByteArray)`:

| Status | Meaning | Output bytes |
| --- | --- | --- |
| 0 | Successful false | 128-byte journal |
| 1 | Successful true | 128-byte journal |
| 2 | Invalid input or policy | Empty |
| 3 | Exhausted inference budget | Empty |
| 4 | Resource limit | Empty |
| 5 | Hash refusal or wrong digest length | Empty |

`l4_ask_attest_native` takes five owned managed Lean ByteArrays in order:
original data, salt, query, rules, context; then an unboxed `uint8_t` regime.
The result has a boxed UInt8 in object field 0 and the journal ByteArray
in object field 1. The caller must initialise the generated module and
follow Lean ownership rules. Lake uses the package-qualified initializer
`initialize_l4factoidal_Harness_AskAttestationExports(uint8_t)`; inspect
the emitted C for other build modes.

## Checked statements and assumptions

The pipeline's 20 public theorem statements are in `Encoding.lean`,
`Policy.lean`, `Ask.lean`, `Theorems.lean` and `AdmissionTheorems.lean`.
They establish exact journal size, no public bytes on failure, ASK-only
admission, actual rule validation and general-rule properties, exact hash
message provenance, the result Boolean's connection to actual ASK on the
completed graph, and defined salt/context refusal. Each theorem has an
actual axiom report; allowed outputs are only `propext`,
`Classical.choice` and `Quot.sound`, or no axioms.

These statements do not prove universal parser or SPARQL conformance,
the Lean compiler/runtime, the native FFI, cryptographic collision
resistance, zero knowledge, the authenticity of graph facts, or salt
entropy. Runtime hashing uses the existing HACL* SHA-256 binding only.
The pure Lean hash is used for public test vectors. HACL*/specification
agreement is checked on the native fixture and padding-boundary cases;
it is not a theorem about the opaque FFI.

A deployment supplies fresh CSPRNG salt and an expected, authorised
policy. It defines the context bytes so that the verifier can bind the
beneficiary, action, deployment/chain and a replay-protected nonce or
expiry. This pipeline hashes arbitrary context bytes; it does not decide
those application rules. Proving a freely chosen ASK policy true would
not establish eligibility for a different policy.

## Reproduction and test evidence

The subsequent [private witness workflow](20261122-private-ask-workflow.md)
uses this unchanged admitted computation with fresh host OS salts, native/HACL
snapshot checks, independently authorised image/policy/context and a strict
public-only Groth16 package. Its worknote separates host lifecycle checks from
new proof evidence and records the local SDK transport trust boundary.

The source was checked with Lean 4.33.1, one build at a time, explicit
`formal/lean4` working directories and a 4 GB Lean memory cap. Small
module checks used `LEAN_NUM_THREADS=1`, `LEAN_STACK_SIZE_KB=16384`,
`lean -j1 -s16384 -M4000`; dependencies were initially reused from the
matching baseline `e0666850902b16471c3299bde30944aa389604ec`. This is
not described as a cold build of the entire repository. The integration
Lake build completed 241 jobs, including the native executable and the
changed import closure. The later proof-only admission module was also
checked with actual axiom reports.

`Attestation.Tests` has 78 passing guards: true, false, empty ASK,
duplicate set identity, byte commitment changes, valid trailing
whitespace/comments, malformed UTF-8/N-Triples, excluded query/rule
forms, real SPARQL-RL inference and base retention, RDFS then rules,
round exhaustion, resource refusal, strict regime bytes, policy/context
binding and the exact independent expected journal.
The additional ten policy-review guards cover blank-node name capture,
shared labels within one BGP and distinct scopes across admitted joins.

`l4-ask-attest --self-test` passed 28 native checks over the actual HACL*
export, including SHA-256 block/padding boundaries, the independent
fixture, successful false, malformed-input and no-journal failures,
actual rule inference and ordered RDFS composition. The file-input CLI
also produced a journal byte-identical to the independently computed
128-byte fixture (`cmp` passed). These are native execution measurements,
not ZK receipt results. From `formal/lean4`, run:

```sh
lake build l4-ask-attest
.lake/build/bin/l4-ask-attest --self-test
.lake/build/bin/l4-ask-attest --write-fixture /tmp/ask-fixture
.lake/build/bin/l4-ask-attest /tmp/ask-fixture/input.nt /tmp/ask-fixture/salt.bin /tmp/ask-fixture/query.rq /tmp/ask-fixture/rules.srl /tmp/ask-fixture/context.bin simple /tmp/ask-fixture/journal.bin
```

The fixture salt is fixed public test data, not a deployment salt. The
expected hex in `Attestation.Fixtures` was independently encoded and
hashed with Python's standard `hashlib.sha256`; no new cryptographic
primitive was implemented. Its four 32-byte words are:

```text
3714978ba3a9a0943c0daba1ccec95eaa7177b25f58768af7b7dac48807f7a92
b6eda070896dbba7e5dc4c703a7a2a93ed7c9e1af6bd52368e70fbf05de48cf5
7fbf63bf0092351a1381c010568ebbaf94b7ccb71f7a33b33584e194ac7e4bb2
0000000000000000000000000000000000000000000000000000000000000001
```

Existing ordinary execution has no new attestation import. The native
and proof build roots are opt-in; pages and queries which do not request
an attestation execute their existing path.

## Focused native CI and policy review

[`check-ask-attestation.yml`](../.github/workflows/check-ask-attestation.yml)
runs the Linux native check with the exact Lean 4.33.1 pin. It builds only
`AskAttestation` and `l4-ask-attest`, with their required dependency closure;
it does not build unrelated corpus targets. The fresh CI checkout uses no
Lean or package cache. The existing full-corpus workflow is unchanged.

[`tools/check-ask-attestation.py`](../tools/check-ask-attestation.py) also
works locally. Every Lean subprocess has an explicit `formal/lean4`
working directory, one Lean worker and a 6 GiB address-space cap; the fresh
axiom-report invocation additionally uses `-M4000`. Run from the repository
root, using the shared build queue when other agents use the same host:

```sh
python3 tools/check-ask-attestation.py --output-dir /tmp/ask-attestation-evidence
```

The exact-source local validation completed 242 targeted Lake jobs in
315.608 seconds. It then freshly printed and required all **55 theorem
axiom reports**: 35 checked-runner statements and 20 pipeline statements.
This fresh report step is retained even when a developer's local Lake
build can reuse compiled modules. The existing source/axiom hygiene audit
passed against the combined build and report log. No prohibited escape
was added; the source-wide partial-definition count stayed at 163.

The same check passed **28 native self-tests and 24 file-input CLI cases**.
For each successful CLI case, Python independently encoded every policy
field, computed SHA-256 with standard `hashlib`, and compared the complete
128-byte output and printed Boolean. False, duplicate RDF input, changed
salt/context, rule inference, base retention and ordered RDFS/rules were
covered. Failure cases required the expected nonzero exit, empty stdout
and no journal file. These included malformed UTF-8, trailing N-Triples
garbage, byte limits, excluded query forms, blank-node name capture and
blank-node scope reuse. The workflow preserves source hashes, the native
binary hash, logs, theorem inventory and public fixture evidence.

The policy review found a concrete name-capture defect in the general
query engine's existing rewrite: `_:x` becomes `?_bnode_x`, so an explicit
variable with that name could turn two independent matches into one join.
On separate `a/p/b` and `c/q/d` triples, the collision query was admitted
and returned false, while the independent-variable control returned true.
The added admission guard now refuses the collision. Its two checked
theorems establish name disjointness and that actual admission checked it.
The general engine's fresh-name repair remains a follow-up under issue 745.

The review also checked nested group scopes in both orders, shared labels
inside one BGP, distinct labels and anonymous nodes in separate groups,
finite positive rule terms, host-function exclusion and resource-check
placement. The parser already rejected cross-group label reuse; those
controls now enter both the guards and the native CLI check. No additional
resource or determinism defect was found in this review. Resource caps and
conservative join checks are implemented; a universal peak-allocation or
VM-cycle bound remains unproved.
