# OWL consistency: connect the proof to the public producer

Current PR status: [2026-10-22 reconciliation and evidence](20261022-owl-pr-reconciliation.md).
The dated checkpoint below is retained as historical evidence.

Date: 2026-10-21. Local repair, not published. Artifact verification is
recorded below separately from source proofs. This continues
[reader preservation](20261021-owl-reader-preservation.md).

## Reproduced failure and scope decision

The pre-edit local `owlIsConsistent` returned `consistent:false` for the
satisfiable annotation-property/domain-Nothing example. The actual public
function was evaluated, not just a surrogate checker. Evidence in the review
workspace: `logs/owl-public-boundary-before.log`, the before-case report,
and `audit/owl-public-boundary-before-sources/` with hashes.

Pinned GitHub source at `16ac0377a82732285974e24fcebeb0cacee1553b` still
uses an unchecked RL/refuter route. Its JS facade passes the verdict through;
the new proof modules are absent there. Exact files, Git blob verification,
and immutable source links are in `logs/github-main-16ac-owl/`. This source
inspection does not establish the provenance of the user's pragmatic release
fix or the behavior of a separately built npm artifact.

The local repair explicitly narrows consistency decisions to the admitted
atomic fragment. Unsupported inputs return null; there is no unchecked RL
fallback. This is a compatibility reduction, not complete OWL support.
Negative property assertions, restrictions, imports and equivalentClass are
among the unsupported forms. The existing npm regression file, which expects
some broader decisions, remains intact: those expectations are not silently
weakened into conformance passes. Its previous source is also preserved.

Both declarations and reasoning are about `ds.default`, as the existing type
documentation specifies. An RDF Dataset can contain named graphs; this
operation does not claim a model for their union. A contradiction or
annotation declaration in a named graph must not affect default-graph
reasoning. The existing whole-dataset RDF 1.2 term preflight remains: an RDF
1.2 term in a named graph can still cause an input error.

## Actual source-to-response proof

`Wasm/Ops/ReasonDlCertified.lean` contains the actual JSON-object producer.
`owlConsistencyJsonWithCert_sound` covers every dataset and every candidate
certificate; no assumption about the search that supplied it is required.
It checks the certificate against `AtomicDirect`'s reading of the original
default graph. `owlConsistencyJsonWithCert_ne_true` proves that this producer
cannot report a model, even if an arbitrary certificate is supplied.

`ReasonDl.owlIsConsistentParsed` serializes that object. Its
`owlIsConsistentParsed_certified` theorem connects the actual string-returning
function to a JSON object whose `consistent` field satisfies the independent
source meaning. `owlIsConsistent_certified` gives the corresponding theorem
conditional on the actual N-Quads parser returning a particular dataset.
Changing the public function to return an unchecked false breaks this proof.

This does not prove the N-Quads parser implements its standard, or that JSON
serialization/external parsing, Lean extraction, Wasm and JavaScript preserve
the response. Those are named artifact-test boundaries. The meaning theorem
alone also does not enforce JSON schema: `getBool?` maps absent/non-Boolean
fields to none. Separate success/refusal schema theorems now require the
actual fields: success has ok:true, explicit consistent:null or false, a
string reason and no error; refusal has ok:false, a string error, and no
consistent/reason fields. These cover arbitrary certificates and the default
producer. External parsed response-shape checks remain separate requirements.
Both producers also have universal unique-field proofs. Without that
obligation, a first-match Lean lookup and a last-match external JSON parser
could disagree on duplicate keys despite the original field-meaning proof.

Production currently proposes `Cert.close`. The checker performs its own
proved saturation with a fixed 64-round bound. The compatibility `fuel`
option does not change that bound; there is no tableau search here. Rejection
means unknown, not consistency or demonstrated budget exhaustion. Reusing the
legacy emitter needs care: it now encodes class names, while this restricted
reader uses raw class names. Any proposed certificate must be checked against
the exact original-input ontology; a name mismatch cannot justify fallback.

## Equality coverage defect found during integration

The unchanged public test for `a sameAs b`, `b sameAs c`, `a differentFrom c`
failed in the first integration build. `DirectCert.mergeAll` applied
substitutions to assertions but left later equality endpoints unchanged.
Some pair orders therefore lost an equality representative.

The repair renames both remaining equality endpoints after each merge.
Termination is by the number of remaining pairs. `respectsSame_subst` and
`satAll_mergeAll` preserve the same interpretation and assignment;
`checkCert_sound` keeps its original statement. Eight order/direction variants
cover 24 outcomes: eight contradictory chains close, while equality-only and
unrelated-difference controls reject the close certificate.

The old algorithm also satisfied model preservation. That theorem never
claimed equality-closure completeness. A general quotient/reachability
refinement theorem remains a coverage obligation. Renaming pending pairs adds
quadratic pair work; no scaling claim is made. Generated C uses a tail loop.
The failing integration log remains `logs/owl-public-boundary-first.json`.

## QA gates and their own negative controls

`tools/check-owl-public-boundary.py` builds the actual dispatch and executes
20 public cases through text, dataset and dispatch adapters. Inventory:
seven false verdicts, ten unknowns (four unsupported), and three errors.
Unknowns are correct refusal observations, not successful semantic decisions.
Three production mutations must fail inside their relevant proofs: invert
the JSON Boolean, reason over named graphs instead of the default, and bypass
the checked JSON producer in the public function.

Independent review found that the initial gate accepted heartbeat/recursion
failures inside proof lines as mutation rejection. It also accepted an omitted
null expectation and duplicate JSON response keys. The revised gate rejects
these. Twelve parser controls and twelve simulated main-loop controls pass;
their evidence is in `logs/owl-public-boundary-synthetic-controls-final-schema-20261021/`.
These are synthetic runner tests, not Lean proof results. The shared reader
mutation gate now rejects resource failures too. Missing Lake, import/syntax
errors, missing inventories and timeouts cannot become successful proof checks.

The new module is registered in the explicit Wasm Lake roots. The first
attempt before registration failed and remains in
`logs/owl-public-boundary-build.log`; an absent object file was not a semantic
failure. Core and builds workflow drafts call the public boundary gate and
preserve its report. These changes have not run remotely.

`tools/check-owl-public-artifact.mjs` replays the passing source inventory
through a specific package's Wasm dispatch and JavaScript API, with per-case
child-process deadlines and artifact hashes. Malformed raw ABI option text
has no JavaScript options-object equivalent: it exercises dispatch only.
Thus 20 dispatch cases correspond to 19 public-facade cases.

## Remaining obligations

`owlEntails` is still a separate legacy operation. Consistency's proof does
not certify its closure, reader or negated-goal transformation. The source
review also found a false freshness rationale in `NegationGoals`: underscores
are legal in RDF blank-node labels, so the `__factoidal_` prefix is not fresh
by syntax. No public collision exploit was demonstrated in this review.
Use tagged/fresh names with a proof, and prove countermodel coverage before
reusing that transformation in a certified entailment producer.

General OWL coverage, positive models, entailment, parser/serializer adequacy,
broader compiled-artifact validation and reconciliation with current main remain
separate obligations. The old reader/preprocessing acceptance gate stays red
for the annotation example; changing one caller does not repair that legacy
transformation or other callers such as the separate tableau diagnostics.

## Final verification record

Completed 2026-10-22. These are local draft results, not a release claim.

| Check | Result | Review-workspace evidence |
| --- | --- | --- |
| Public source boundary | 20 cases, 3 proof mutations, 11 axiom audits pass | `logs/owl-public-boundary-unique-final.json` |
| Reader boundary | 45 cases, 7 proof mutations pass | `logs/owl-reader-contracts-public-final.json` |
| Full Lean library | 808 jobs pass | `logs/owl-public-boundary-library-build.log` |
| Module reachability | 815/815 library modules reachable; csimp audit passes | `logs/owl-public-boundary-import-audit.log`, `logs/owl-public-boundary-csimp-audit.log` |
| W3C consistency measurement | 266 selected; 246 executed: 232 unsupported, 14 unknown; 20 missing RDF/XML; zero definitive answers | `logs/atomic-direct-w3c-public-final.json` |
| Rebuilt packed artifact | 20/20 dispatch cases, including 19 public API cases, pass | `logs/owl-public-artifact-rebuilt-final.json` |
| Original artifact control, corrected runner | 5/20 cases match the new contract; gate fails | `logs/owl-public-artifact-published-control-loader-final.json` |
| Artifact runner refusal controls | 6/6 pass; synthetic, not engine conformance | `logs/owl-artifact-refusal-controls.json` |
| Unchanged broader OWL regressions | 11 pass, 4 fail | `logs/owl-public-broader-regressions.log` |
| Broader packed-artifact semantic gate | 50 discovered: 37 pass, 11 fail, 2 error, zero skipped/timeouts | `logs/npm-semantic-after-public-boundary.json` |
| Legacy annotation/preprocessing gate | Still fails | `logs/owl-legacy-preservation-after-public.json` |

The build used the project's normal `Wasm/build-wasm.sh` pipeline, Lean
4.33.1 and Emscripten 6.0.8. Network fetching and an unwritable global cache
caused initial failures; standalone source clones and a task-owned writable
Emscripten cache resolved them. Final build log:
`logs/owl-public-boundary-wasm-writable-cache.log`. Linker warnings remain for
`lean_io_create_tempfile` and `lean_io_create_tempdir` function signatures.
The exercised OWL paths pass; this run does not establish those IO paths safe.

The package was packed with `npm pack --ignore-scripts` and extracted before
testing. A task-owned npm cache resolved the initial cache permission error.
The local draft retains version 0.11.0; identify it by digest, never by that
version alone. It is not the registry release.

- Tarball: `artifacts/owl-public-checked/factoidal-core-0.11.0.tgz`, 2,704,354 bytes.
- Tarball SHA-256: `bf00f0d02434c9eceda47f6199cd08d3a2c11e627a169d7a5376c68c938d2540`.
- Full Wasm SHA-256: `c35e94dc39871c684cbd1ebf4e9e44608709251bf2151405a230990e6ad920d3`.
- Pack inventory and every packed-file digest: `logs/owl-public-package-pack.json`, `logs/owl-public-package-manifest.json`.

The first artifact run passed 17/20 because the runner wrongly expected
`engine.call` to return refusal envelopes. The loader actually throws an
Error retaining `.envelope`. After correcting that, a 19/20 run exposed
the public API's separate preliminary parser: its structured ParseError is
not the raw OWL parser's message. The final runner checks the exact source
error envelope for dispatch and line/column/offset/format for that public
parse case. Generic exceptions do not pass. Both failed iterations remain
preserved. The original-artifact control consequently changed from 2/20 to
5/20; the three additional matches are refusal cases. These contract counts
are not counts of wrong semantic verdicts.

The four unchanged broader OWL failures are: negative object-property
assertion now unknown instead of false; budget diagnostic now unsupported;
punning diagnostic now general unsupported syntax; and the legacy entailment
operation returns `refutation` where the test expects `closure`. That last
failure is outside the new consistency proof. Do not weaken these tests to
approve this draft. The broad gate additionally records outstanding duplicate
triple handling, XMLLiteral identity, variable SERVICE, triple-term blank-node
identity, SPARQL 1.2 errors, XSLT and Solid access-control findings.

This artifact includes earlier authorized repair drafts in the dirty checkout.
The source reports hash selected files, not the entire transitive source and
toolchain closure. No remote workflow run, merge or publication was performed.
Legacy `RefuteCert.applyRen` also still folds unrenamed equality pairs; a
future emitter integration must reconcile its representatives with the repaired
checker. A rejected certificate must remain unknown, never trigger fallback.

The builds workflow draft now packs and extracts a tarball before the public
OWL gate, and preserves pack metadata and its SHA-256 with the report. Its
shell/Python snippets and both workflow YAML files pass local syntax checks
(`logs/owl-public-workflow-validation.json`). Web publication requires the
successful web-gates artifact; the separate npm publication draft retains its
broader packed-artifact gate. These statements describe inspected local
workflow code, not evidence that remote enforcement has run.
