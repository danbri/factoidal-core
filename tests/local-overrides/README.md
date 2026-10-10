# Local test overrides

A **local override** records a deliberate, documented disagreement
between this project and a specific upstream conformance fixture — a
case where the fixture's stated expectation cannot be met without
being *wrong*, because the fixture data itself is defective.

An override is a **disposition, not a semantic change**. The engine
pipeline still runs unchanged and still reports its real answer; the
override only reclassifies one named, justified divergence out of the
`FAIL` bucket into a distinctly-counted `local-override` bucket, so a
suite can reach exit 0 without hiding the divergence. Nothing here
alters RDF / SPARQL / RIF reasoning — this is test-harness
bookkeeping consumed by the per-suite runner (a rule #11 consumer),
which is why override loading lives in `bin/<suite>-runner/` and not
in any `.fst` module.

## Convention

```
tests/local-overrides/<suite>/<TestName>.override
```

- One file per overridden test. The **file count per suite is the
  suite's "local-override" count** — a runner reports overrides
  separately from plain passes and from fails.
- Each `.override` is a small header block of `key: value` lines,
  then a `---` line, then free-text rationale. Runners parse only the
  header keys they key on (`test`, `disposition`); the rationale body
  is for humans.

### Header keys

| key             | meaning                                                        |
|-----------------|----------------------------------------------------------------|
| `suite`         | which suite this override belongs to (e.g. `rif`)              |
| `test`          | the exact test name the runner emits (the match key)          |
| `category`      | the upstream test category (e.g. `PositiveEntailmentTest`)    |
| `upstream-result` | what the fixture manifest expects                            |
| `our-result`    | what our pipeline actually computes                            |
| `kind`          | why they differ (e.g. `corpus-data-defect`)                    |
| `disposition`   | must be `local-override` for a runner to honour the file       |
| `date`          | when the override was authored                                 |
| `provenance`    | where the defect was confirmed upstream                        |
| `issue`         | the open GitHub issue that tracks the disagreement (full URL)  |

## Before adding an override

Run the case alone (`--verbose` on the runner) and read the document and the
reason it fails. An override says that the fixture, and not the engine, is
wrong, so check that the engine's verdict is the one the specification gives
for THIS document, not for a document that looks like it. On 2026-10-10 the
xmlconf case `ibm-1-1-valid-P03-ibm03v09.xml` was recorded as a fixture that
contradicts XML 1.1 (its external entity has a bad text declaration), an
override was added, and the runner reported it STALE the moment the real cause
was fixed: the document never references the entity, and the parser had read it
anyway (XML 1.0 section 2.1 asks for the entities a document references).
Cost: an issue, a task order and two commits for a dispute that did not exist.

## Runner contract

A runner that honours overrides MUST:

1. Only apply an override when the test's observed outcome is the
   expected divergence (a real `FAIL`). An override never masks a
   `PASS` — if an overridden test starts passing on its own, the
   runner flags the override as **stale** (removable) and counts a
   plain pass, never a silent success.
2. Count honoured overrides in a distinct bucket, printed on its own
   line, excluded from the fail count (so a suite whose only reds are
   dispositioned overrides can exit 0).
3. Never let an override change any computed result — the pipeline
   output that the override reclassifies must be the same output the
   runner would print without the override file present.

Because an override is a standing disagreement with a published test,
each file must carry enough provenance for a reviewer to confirm the
defect independently.

## Periodic upstream re-check

An override records a disagreement with a fixture *at a point in time*.
Upstream corpora move: the ShEx `start2RefS2` override was retired on
2026-07-29 when shexSpec/shexTest commit `0f45c51` reconciled the
p1/p2 defect it documented and added synchronization actions. A stale
override that no longer fires is the same failure mode as stale
documentation — it reads as a live disagreement when the dispute is
settled.

**Procedure** (run alongside the `issue-hygiene` sweep, or whenever a
suite's submodule is updated):

1. `git -C <submodule> fetch origin` and compare `HEAD` with upstream.
2. If behind, update, re-run the suite, and see whether the override
   still fires.
3. If it no longer fires, **delete the file** — do not leave it inert.
   Update the ledger and the `test-suites` skill, keeping a dated note
   explaining why the score moved.
4. If it still fires, append a dated entry to `recheck_log` (JSON
   overrides) or an `RE-CHECK <date>` block (`.override` text files),
   recording the upstream commit checked.

**Overrides that cannot be retired by an upstream fix** — record this
once rather than re-deriving it each sweep:

| Override | Why permanent |
|---|---|
| `jsonld-compact__t0038` | Version dispute, not a defect. The test declares `option.specVersion=json-ld-1.0`; we implement 1.1, whose behaviour the suite's own `#tp001` pins. Retirable only by adding a real 1.0 processing mode. |
| `jsonld-fromrdf__t0008` | Same version dispute. The manifest's own `purpose` says the input is deliberately only partially ordered. |
| `jsonld-frame__t0010` | Same version dispute, in the framing suite: under JSON-LD 1.1 IRI Compaction (API §6.2) the input property `dcterms:creator` raises `IRI confused with prefix`; the fixture needs 1.0-era compaction as a whole. All three json-ld-1.0 disputes are tracked at https://github.com/danbri/factoidal/issues/703. |
| `xslt-node-1601` | XPath 1.0 §5.4 makes namespace-node order implementation-defined. The fixture pins one processor's hash-table order; ours is equally conformant. No upstream fix is possible in principle. |
| `rif/RDF_Combination_Constant_Equivalence_4` | Corpus data defect in a **read-only archive** (W3C rules WG closed), so nobody can correct it upstream. |

Last full re-check: **2026-07-29** — all four still required; ShEx
retired.
