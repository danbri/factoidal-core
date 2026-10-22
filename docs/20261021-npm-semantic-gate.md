# Selected npm semantic regression gate

Current PR status: [2026-10-22 reconciliation and evidence](20261022-owl-pr-reconciliation.md).
The dated checkpoint below is retained as historical evidence.

`tools/npm-semantic-gate.mjs` runs self-contained product regressions against
an explicitly supplied installed or unpacked package. It uses Node built-in
modules only. It does not use a network service or an external test corpus.

```sh
node tools/npm-semantic-gate.mjs \
  --package /path/to/unpacked-package \
  --json /path/to/new-report.json
node tools/npm-semantic-gate.mjs --self-test
```

`--package` and `--json` are required for a package run. The report path must
be new; an existing file is not overwritten. Each package worker imports
that directory's `index.mjs`. The Solid cases additionally import that
directory's `solid/server/index.mjs`. Package-local loader, glue and wasm
files must exist. The worker removes inherited `NODE_OPTIONS` and selects
the supplied package's assets rather than an ambient asset override.

The report hashes `package.json`, `index.mjs`, `l4factoidal.js`,
`l4factoidal.mjs` and `l4factoidal.wasm` with SHA-256. It records package
name/version, npm engine/version, engine version string, ABI version and
operation count when available. Required public exports and engine
operations are checked. Missing package files or operations fail the gate.

## Scope

The current catalog has 50 unique case IDs. The first retained run used
48; the second adds two Direct Semantics counterexamples. There is no filter, skip or XFAIL
acceptance path. Each discovered case gets a result. A run exits zero only
when all discovered cases pass, the catalog is nonempty and all identity
checks pass. Reports give separate discovered, pass, fail, error, timeout
and skipped counts. Assertion mismatches count as failures; unexpected
public API exceptions count as errors. Both prevent a zero exit.

| Finding | Cases and observations |
| --- | --- |
| R01 | Run the gate against a nonexistent package and require exit 1 plus an error report. |
| R02 | Duplicate default triples through Turtle, N-Triples, N-Quads, JSON-LD and RDF/XML; duplicates in one named graph versus equal triples in distinct named graphs; identical IRI objects; numeric lexical forms `1` and `01`; different datatype IRIs; different language tags. Assert dataset size, iteration and SPARQL COUNT. Named graph cases also require an empty default graph. |
| R14 | Ingest two N-Quads XMLLiteral terms with lexical forms `<x a='1' b='2'/>` and `<x b='2' a='1'/>`; require size, iteration and COUNT to remain two. |
| R03 | Ordinary, JSON, CSV, RDFS, RDFS/JSON and RDFS/CSV queries with a registered endpoint, an absent endpoint and a cleared endpoint. RDFS cases require a local inferred type and a remote binding. |
| R04 | A variable SERVICE endpoint supplied by VALUES must produce its registered remote binding. This is a product interoperability test, not a normative W3C conformance claim. |
| R08 | A blank node shared by an asserted triple and an RDF 1.2 triple term must retain RDF/JS identity. |
| R09 | CONSTRUCT and INSERT of an RDF 1.2 triple term through Dataset methods with `{sparql12: true}` must produce one quad with the expected nested terms. |
| R10 | sameAs plus differentFrom must return inconsistent; either assertion alone must not return inconsistent. A quiescent search currently requires an indeterminate result. A fuel-truncated search and an unsupported negated conclusion must also remain indeterminate. Annotation-property domains and class/individual punning with valid Direct Semantics models must not return inconsistent. |
| R05 | A minimal XSLT attribute set must write `color="black"`. |
| R06 | The Solid library's default configuration and explicit `insecureNoAuth: false` must reject anonymous PUT with status 401. |

R10's quiescence case records the present assurance policy: search
quiescence does not establish a checked model. A future path that checks a
model certificate can legitimately change that expectation. Such a change
must update the case and its evidence; it cannot silently accept an
unverified candidate as a model.

The two added cases have category `owl-regime` and explicitly state
`OWL 2 Direct Semantics` in their expected results:

- `R10.direct.annotation-property-domain`: an annotation property `urn:p`
  has domain `owl:Nothing`, and `urn:a` has annotation `urn:p "note"`.
  Annotation property domain and assertion are annotation axioms under
  [Structural Specification §10.2](https://www.w3.org/TR/owl2-syntax/#Annotation_Axioms).
  They add no Direct Semantics class-membership condition, as specified in
  [Direct Semantics §1](https://www.w3.org/TR/owl2-direct-semantics/#Introduction).
  A model has object domain `{u}`, `owl:Thing` interpreted as `{u}` and
  `owl:Nothing` as empty, with a standard datatype interpretation. There
  are no logical assertions requiring `u` in the empty class.
- `R10.direct.class-individual-punning`: C and D name classes and
  individuals, C sameAs D, their classes are disjoint, and x belongs to C.
  Give individuals C, D and x the same denotation `u`, class C extension
  `{u}`, and class D extension empty. Equality, disjointness and membership
  all hold. The independent class and individual interpretations follow
  [Direct Semantics §2.2](https://www.w3.org/TR/owl2-direct-semantics/#Interpretations)
  and [Structural Specification §5.9](https://www.w3.org/TR/owl2-syntax/#Metamodeling).

These are mathematical countermodels to the false inconsistency claims,
not new machine-checked theorems. Both cases accept `true` or `null` and
reject `false`; their expectations are scoped to Direct Semantics. Exact
fixtures and the known draft limitation are recorded in
[the OWL public verdict worknote](20261021-owl-public-verdict-repair.md).
The annotation case remains a release blocker for the current draft.

The report lists R07 resource budgets, R11 CSVW, R12 TypeScript API agreement
and R13 RML as unimplemented obligations. These are not skipped passing
tests. `completeAuditCoverage` and `allSuitesConformance` are always false.

The gate measures the selected Node npm paths and the in-memory dataset
engine. It does not certify the CLI, Deno, browser, persistent storage,
complete W3C conformance, Solid HTTP transport or external authentication
interoperability. Runner timeouts do not implement or certify R07's engine
resource budget obligations.

## Enforced deadlines

Each case, including package import and wasm initialization, runs in a
separate Node child process. The coordinator can send SIGKILL while that
child is blocked in synchronous JavaScript or wasm. The default per-case
limit is 10,000 milliseconds. The whole execution limit is 120,000
milliseconds. `--case-timeout-ms` and `--timeout-ms` change those positive
integer limits, up to 3,600,000 milliseconds.

The coordinator's whole-execution deadline aborts artifact hashing, kills
an active case and marks remaining discovered cases as timeouts. Report
finalization follows termination. A timeout always makes the gate fail.
The mechanism does not depend on a timer running in the wasm process or
on `Promise.race` interrupting a synchronous call.

The 12 runner self-tests check empty catalogs, duplicate IDs, skipped
results, missing results, nonzero worker exits, worker errors, a killed
synchronous infinite loop, whole-execution cancellation, nonexistent
packages, missing public functions, missing reflected engine operations
and refusal to overwrite evidence. They use temporary source fixtures;
no engine binary is copied or manufactured.

## Published package result

The first catalog version ran against the unchanged published 0.11.0 package:

```sh
node tools/npm-semantic-gate.mjs --package ../package \
  --json ../logs/npm-semantic-gate-published.json
```

It exited 1 after approximately 22.4 seconds. It discovered 48 cases:
27 pass, 14 fail, 7 error, 0 timeout and 0 skipped. The seven API errors
are the five registered SERVICE cases with output or entailment, the
SPARQL 1.2 CONSTRUCT result path, and INSERT with `sparql12: true`.
The latter option is rejected by the published Dataset.update method.

The report records wasm SHA-256
`15eb8d770829f3f07dad4f8eabbbaf4503f55104a1803cb87209d05d093dc642`,
package metadata SHA-256
`4e39fbc933350f4b40029c1b4677dcccb87a8a37a92329b87835c2eb58606ffa`,
engine `lean4-wasm`, API version `0.11.0`, ABI `1` and 155 reflected
operations. This run measures the published artifact; source repairs in
the checkout do not change that artifact.

The failure controls also ran:

- `--self-test` exited 0 with 12 pass and 0 fail. Its retained log is
  `../logs/npm-semantic-gate-selftest.log`.
- A standalone nonexistent-package run exited 1 with 48 error, 0 pass,
  0 fail, 0 timeout and 0 skipped. Its report is
  `../logs/npm-semantic-gate-missing-package.json`.
- A published-package run with `--timeout-ms 1` exited 1 with 48 timeout,
  0 pass, 0 fail, 0 error and 0 skipped. Its report is
  `../logs/npm-semantic-gate-deadline.json`.

All reports are new files. Existing audit reports remain unchanged.
`node --check tools/npm-semantic-gate.mjs` and `git diff --check` pass.

The expanded 50-case catalog then ran under Node `v22.22.2`:

```sh
/opt/homebrew/opt/node@22/bin/node tools/npm-semantic-gate.mjs \
  --package ../package --json ../logs/npm-semantic-gate-published-v2.json
```

It exited 1 with 50 discovered: 27 pass, 16 fail, 7 error, 0 timeout and
0 skipped. Both new Direct Semantics cases failed because the published
API returned `consistent: false`. The artifact hashes match the first run.
The original 48-case report and its failure-control reports remain
unchanged. The runner and self-test logic did not change in this expansion;
the 12-case self-test log remains the record of the earlier runner checks.
No repaired wasm or draft source path was run by this published-package
gate, and no OWL issue is claimed closed by this result.
