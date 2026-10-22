# OWL checked consistency: PR reconciliation and release blockers

Date: 2026-10-22. Status: draft for review, not ready to merge or release.
Reconciled onto core `dfecea9` (package version 0.12.0); the accompanying
builds draft starts at `c1c67e0`. The earlier repair checkout and handoff
archives remain unchanged. This note supersedes their integration status,
not their historical observations.

## What is proposed

The satisfiable annotation/domain-Nothing example could reach an unchecked
inconsistency verdict. The new consistency operation reads the original
default graph through `AtomicDirect`, checks a certificate against that
reading, and serializes the proved result. It does not use an RL fallback.
The proof chain covers independent source meaning, reader model preservation,
whole-input admission/coverage, checker acceptance, actual producer, field
meaning, explicit schema and unique JSON keys. Source adequacy to OWL prose,
parser correctness, serialization, extraction and runtime remain explicit
review/test boundaries. This is not complete OWL support.

The checker now substitutes merged individuals into pending equality pairs,
repairing the transitive-chain coverage failure while preserving models.
Generated certificate names use a reversible tagged encoding. Both definitive
verdict constructors require admission evidence. Search quiescence is not a
model. The public consistency operation returns false or null, never true.

The same file also makes legacy entailment conservative about unsupported
conclusions, quiescent search and detected punning. Its positive verdicts
remain unproved; its reader, closure and goal-reduction obligations are not
discharged by the consistency proof. Negative property assertions, imports,
restrictions and equivalentClass remain unsupported by the new consistency
reader. Its fixed 64-round checker ignores the compatibility fuel option.
These capability changes are now stated on the package README, in API docs
and in types. Named graphs do not contribute axioms/declarations to default-
graph reasoning; whole-dataset RDF 1.2 term preflight is retained.

The PR excludes the earlier SERVICE, RDF 1.2 type and query-wrapper repairs.
It includes their audit obligations/tooling, not their production patches.
The broad incident specification preserves graph-set versus solution-bag
semantics, term versus value equality, and the imported syntax definitions
needed to reason from RDF 1.1 Semantics. The original audit snapshot is
identified in [the archive index](audits/npm-0.11.0/README.md).

## Reconciliation found an error-code defect

Main now applies `ErrorModel.attachCode` at dispatch and exports
`FactoidalError`. The old fixture assumed raw producer/dispatch equality and
the old artifact adapter expected `ParseError`. Those assumptions were updated
without reverting the new error model. The source fixture preserves both raw
and dispatch responses; independent expected metadata is checked at each edge.

Actual artifact testing then found a product defect: the positioned message
`expected object (IRIREF, BLANK_NODE_LABEL, or literal)` was classified as
`term.invalid-iri` simply because it mentioned IRIREF. This names an allowed
alternative, not an offending IRI. The small separate fix classifies this
message family as `parse.syntax`. A public test covers missing objects in
N-Triples/N-Quads, in both RDF versions, including positions and spec URLs.
The error suite passes 43 tests. Its first added position expectation was
off by one; that failed iteration is retained, corrected to offset 16.

The raw OWL text operation still receives `reason.failed` for its parse-error
envelope, with no position/spec. The public API's preliminary parser supplies
the structured parse error. This pre-existing diagnostic difference is pinned
and recorded, not represented as a universal error-classification repair.

## QA checks and evidence

Raw reports and development failures are in
[the evidence directory](audits/owl-assurance-20261022/README.md). The directory
manifest hashes its files; hashes establish integrity, not correctness.

| Check | Result | Evidence filename |
| --- | --- | --- |
| Full Lean library | 837 jobs pass | `pr-core-library-build.log` |
| Escape-hatch audit | clean; 1,602 axiom outputs read, no new partial definitions | `pr-core-hygiene.log` |
| Restricted reader | 45 cases, 7 proof mutations pass | `pr-owl-reader-hardened.json` |
| Actual public producer | 20 cases, 3 proof mutations, 11 axiom audits pass | `pr-owl-public-error-fix.json` |
| W3C catalog | 266 selected; 246 executed: 232 unsupported, 14 unknown; 20 missing RDF/XML; zero definitive answers | `pr-owl-corpus-final.json` |
| Gate-parser controls | 20 unittest tests pass | `pr-owl-parser-controls-final.log` |
| Artifact-runner controls | 3 controls pass: baseline, missing envelope, SIGTERM-trapping hang | `pr-owl-artifact-controls-first.json` |
| Packed Wasm/JS | 20 dispatch cases including 19 public API checks pass | `pr-owl-artifact-final.json`, `pr-owl-artifact-node22.json` |
| Public error suite | 43 pass | `pr-npm-errors-final.log`, `pr-npm-errors-node22.log` |
| Unchanged broader OWL tests | 11 pass, 4 fail | `pr-owl-broader-regressions-final.log` |
| Broader artifact audit | 50 discovered: 32 pass, 11 fail, 7 error, no skipped/timeouts | `pr-npm-semantic-final.json` |

The first current-main artifact run was 19/20: it exposed the error-code
defect above. The later successful run follows a real Wasm rebuild and a new
pack/extract cycle. The tested draft retains version 0.12.0 and is not the
registry package. Final tarball SHA-256:
`7576d196b495c1f23cacb000fbfb05ea3188ce00123e69006534ff974f25d61f`.
Full Wasm SHA-256:
`29f45ff783544cd0895e953bab9d1cf896133a8ae9c541457ec12d0fe43f4db0`.
The package manifest records every packed-file hash. Tests ran on Node
26.7.0; the focused artifact/error checks also ran on Node 22.22.2, the CI
major version. Build products are excluded from the commits.

The normal build script used Lean 4.33.1, Emscripten 6.0.8 and a writable
task-owned cache. A copy-on-write Lake cache seeded the fresh worktree; Lake
rechecked its source dependencies. Builds retain tempfile/tempdir signature
warnings and HACL memzero platform warnings; the OWL tests do not validate
those IO/crypto paths. Selected source hashes are not a full compiler and
transitive source closure. The package was built from the dirty PR draft;
the recorded base commit alone does not identify its source. Reports and the
reviewed diff provide the additional evidence; CI must build the committed
revision before merge. Missing unrelated external suite fixtures are listed
in `pr-core-test-env.log`; no results from those absent suites are claimed.

Review found that the reader report parser accepted omitted null expectations
and duplicate keys. It now rejects them, extra fields and invalid Boolean
types. Durable tests cover these cases and resource-limit failures. The
artifact runner now uses SIGKILL: default SIGTERM can be trapped and defeat
`spawnSync`'s timeout. Its synthetic control demonstrates termination of that
case; its baseline executes all 20 cases. These are tests of the test tools,
not OWL conformance evidence.

## Merge and release blockers

1. Restore required negative-property coverage through a proved reader/checker
   extension, or explicitly agree the compatibility reduction. The unchanged
   regression expecting that contradiction to be detected still fails.
2. Resolve the other three preserved OWL regression expectations: budget and
   punning diagnostics, and legacy entailment's closure/refutation diagnostic.
   Do not silently weaken them into passes.
3. Complete/replace the legacy entailment and annotation/preprocessing paths.
   The old annotation preservation gate remains red. Legacy `applyRen` also
   needs to align its equality representatives with the repaired checker;
   rejected certificates must stay unknown. General equality completeness is
   a separate proof obligation.
4. Resolve the remaining broad audit findings. Five extra SERVICE errors here,
   compared with the earlier dirty repair artifact, reflect the excluded
   SERVICE repair, not a claimed OWL regression. Graph duplicates, XMLLiteral
   identity, nested blank nodes, SPARQL 1.2, XSLT and Solid findings remain.
5. Run required CI on the committed revision. Local workflow validation is not
   remote enforcement. The builds PR depends on the core tools and must not
   land first; missing tools fail closed. No automatic merge or release is
   requested. The separate npm publication workflow is outside this focused
   builds PR; its broader repair draft remains in the original handoff.

The next implementation should extend admitted coverage without reintroducing
an unchecked fallback, then connect entailment's source semantics, goal
reduction and public result through a corresponding proof chain.
