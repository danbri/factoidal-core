# Review of factoidal-core PR #1

Recorded 22 October 2026. PR: https://github.com/danbri/factoidal-core/pull/1.
Reviewed head: `ed19f0905781008d12275c6fbbff257cb77f044a`.
Base: `906527bae7a741780bb4bab8ccb0f8eb890c85ad` on
`claude/autoexec-scratchpad-assess-37oeok`.

**Verdict: changes required before merge.** The refactor has substantial useful
work, and its principal reported test counts reproduce. One introduced cast
regression is confirmed. An inherited regex error remains accepted by the new
profile. This review does not certify all 145 changed files, full standards
conformance, or the npm/Wasm artifact.

The PR is a draft development checkpoint, expressly not a mainline integration.
Its history has no merge base with current main, fetched at
`0383de5280b361fb7638221212a108f23176d80b`. Merging into its existing base would
not deliver these changes to current main. Do not retarget it or replace main's
files wholesale. Main already has independently developed numeric, casting,
RIF, XML and SPARQL code. The intended integration destination was raised with
the user; no merge, retarget, source edit or release occurred during this review.

## Confirmed introduced defect: duration subtype erased before string casting

Severity P2. In `formal/lean4/L4Factoidal/Fn/Cast.lean:96`, `stringValue`
uses generic `canonicalDuration`. `RIF/Builtins.lean:287` passes a decoded
`Val` that no longer distinguishes the duration subtype.

| Source | Required string | Observed string |
| --- | --- | --- |
| `"P0M"^^xsd:yearMonthDuration` | `P0M` | `PT0S` |
| `"P0Y"^^xsd:yearMonthDuration` | `P0M` | `PT0S` |
| `"PT0S"^^xsd:dayTimeDuration` | `PT0S` | `PT0S` |
| `"P0M"^^xsd:duration` | `PT0S` | `PT0S` |

These are actual executions of the PR's Lean code. The first case previously
preserved `P0M` in the old cast fallback; that comparison does not endorse the
old lexical-only cast implementation. The requirement follows the PR's own
dated contract: [F&O 2007 §17.1.2 and §10.3.1.3](https://www.w3.org/TR/2007/REC-xpath-functions-20070123/#casting-to-string).

Retain source datatype information at the shared conversion boundary. A global
change to print every zero duration as `P0M` would break the two controls.
Returning the original input would fail the `P0Y → P0M` canonicalization case.
The fix must cover derived string targets as well as `xsd:string`.

Evidence: [numeric review](logs/pr1-numeric-review.md),
[executable probe](logs/pr1-probes/DurationCast.lean),
[actual results](logs/pr1-duration-cast.log),
[acceptance guards](logs/pr1-probes/DurationCastExpected.lean),
[expected failing guard log](logs/pr1-duration-expected.log). The acceptance
file exits 1 at this head: exactly the first two guards fail; the controls pass.

## Inherited defect exposed through the new regex profile

The new ECMA profile accepts `^^a` and `a$$`, but returns a negative match for
input `a`. Node's ECMA RegExp returns true. `JSONSchema.patternMatch "^^a" "a"`
then returns `.fail`, not `.unsupported`.

The underlying anchor encoding predates this PR: `Regex/XPath.lean` replaces
each anchor with a consuming boundary sentinel. Two assertions at the same
position therefore require two sentinels, although the input has one. This is
not labeled an introduced engine regression. It is a concrete hole in the new
profile's admission boundary (`Regex/Profiles.lean:89–93`): accepted syntax can
still receive a wrong decided answer. Correct zero-width assertion semantics,
or explicitly refuse the affected forms until supported. Adjacent anchors are
only the demonstrated cases; a fix should also consider grouped assertions.

An independent finite differential test ran 1,242 pattern/input pairs against
Node RegExp: 1,067 agreed, 13 disagreed, and 162 were explicitly refused by Lean.
Those counts are not a full ECMA conformance score. The 13 disagreements all
concern repeated anchors in this corpus.

Evidence: [generator](logs/pr1-probes/regex-differential.mjs),
[expected vectors](logs/pr1-probes/regex-vectors.json),
[Lean differential runner](logs/pr1-probes/RegexDifferential.lean),
[results](logs/pr1-regex-differential.log),
[consumer probe](logs/pr1-probes/RegexBoundary.lean),
[consumer results](logs/pr1-regex-boundary.log).
The consumer probe characterizes current incorrect behavior; it is not an
acceptance test for the repair.

## Independent validation

All source execution used the isolated, clean `review-pr-1` checkout at the
reviewed head. Its build cache was copied with APFS copy-on-write from the clean
`/private/tmp/factoidal-standards-pr` checkout at the identical commit; Lake
then checked the full build. This was not a cache-free rebuild or a Wasm build.
Native fixtures came from `/Users/danbri/working/factoidal` and the previously
pinned `/private/tmp/factoidal-okr-fixtures` archives. No fixtures were changed.

| Check | Observed result | Evidence |
| --- | --- | --- |
| Full untargeted Lean build | 932 jobs pass | [log](logs/pr1-independent-build.log) |
| RDF rdf-mt and SPARQL 1.1/1.2 manifests | 924 pass, 0 fail/skip/unsupported | [log](logs/pr1-independent-w3c.log) |
| RIF Core | 26 pass, 1 fail, 12 undecided; 1 unread, 6 import cases unattempted | [log](logs/pr1-independent-rif.log) |
| CSVW JSON | 270 pass, 0 fail/skip/unsupported | [log](logs/pr1-l4csvw-json.log) |
| CSVW RDF | 270 pass, 0 fail/skip/unsupported; 0 comparison budget failures | [log](logs/pr1-l4csvw-rdf.log) |
| JSON Schema draft-07 vendored suite | 770 pass, 0 fail/undetermined | [log](logs/pr1-l4jsonschema.log) |
| ShEx validation | 1,182 pass, 0 fail/unread | [log](logs/pr1-shex.log) |
| SHACL Core, full reports | 98 pass, 0 fail/skip/unsupported | [log](logs/pr1-shacl.log) |
| XML namespace manifests | 54 pass, 0 fail/errors; 3 optional, 2 non-UTF8 excluded | [log](logs/pr1-namespaces.log) |
| Vendored XSLT subset | 84 pass, 3 byte/whitespace comparison failures, 1 refusal | [log](logs/pr1-xslt.log) |
| Four PR Python regression scripts | 5 scanner, 8 RIF, 1 CSVW, 3 SHACL tests pass | `logs/pr1-lean-*-test.py.log` |
| Additional RIF engine/saturation guards | 7 pass | [probe](logs/pr1-rif-boundary-probes.lean), [log](logs/pr1-rif-boundary-probes.log) |

The three XSLT differences in this rerun concern attribute/namespace declaration
order; the refusal concerns missing `select-59.xml`. They match the survey's
disclosures and are not reported as new regressions. The unchanged harness
still counts them as failures/refusal. No claim of an independently rerun
expanded-name comparator is made here.

The RIF runner exits zero despite its decided failure. That is pre-existing and
explicitly disclosed, but an exit-code-only CI gate would still be false green.
The new RIF completeness propagation was checked separately and improved the
failure handling: blocked/capped/unmappable results do not supply a complete
graph to the changed SPARQL caller. [Bounded independent review](logs/pr1-boundary-review.md).

## Assurance lessons and integration requirements

1. **Retain every semantic distinction needed downstream.** A value-space
   projection can legitimately merge representations for equality while being
   insufficient for source-type-dependent casting. Add a source-aware typed
   conversion interface and a source-to-result specification for duration casts.
2. **A target-membership theorem is not conversion correctness.**
   `Fn.Cast.cast_target_valid` proves that a successful result passes the target
   check. Both wrong and right duration spellings are strings, so this theorem
   cannot exclude the observed error. Add a theorem stating the actual canonical
   projection, plus caller tests through RIF/SPARQL where applicable.
3. **Shared tests need an independent reference.** The new numeric harness
   comparator uses the production comparison layer. That reuse is disclosed;
   it must not serve as its own arithmetic oracle. Preserve independent vectors,
   metamorphic laws (including anchor idempotence), and failing mutations.
4. **Unknown must remain observable.** A profile must refuse unsupported syntax
   rather than give a false answer. The new RIF flags are useful, but their
   selector theorems do not prove complete RIF semantic adequacy.
5. **Reconcile on main in bounded changes.** Suggested order: namespace/encoding
   adapters; typed XSD membership and RDF identity; numeric/cast operations;
   regex profile/selection; RIF completeness and imports. Reconcile main's
   `Fn.Casting` with this branch's `Fn.Cast`; do not create competing kernels.
   Test each host-language adapter and retain all current-main functionality.
6. **Gate the deliverable.** Rerun actual manifests and explicit failure-count
   checks on each integrated head, then the packed Wasm/public API. Native
   success here says nothing about which source commit a future npm artifact
   contains. Keep this PR distinct from the OWL work in core PR #2.

The review rejected two tempting but incorrect findings: the observed subnormal
narrowing and long floating-to-string spellings follow the dated F&O rules the
PR names. A host-language default is not automatically a standards oracle.
See the numeric review for details. No new `sorry`, user axiom, `native_decide`,
`partial def` or FFI declaration was found in added Lean lines; this textual
check is not a proof that the modeled specifications are adequate.
