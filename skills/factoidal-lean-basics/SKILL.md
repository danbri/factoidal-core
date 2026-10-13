---
name: factoidal-lean-basics
description: Work with Factoidal's Lean 4 tree under formal/lean4/, including scope inspection, builds, tests, proof policy, executable and WASM paths, and recorded workflow failures. Use for Lean changes, port planning, capability questions, or environment setup.
---

# Factoidal Lean basics

## What exists (started 2026-08-22; re-measure before scope claims)

`formal/lean4/` is a self-contained lake project, library name
`L4Factoidal` (naming deliberately not finalised — owner: "don't rush
that"). Workstream + continuation ladder:
https://github.com/danbri/factoidal/issues/466

| Area | Files | Content |
|---|---|---|
| RDF core | `RDF/Core.lean`, `XmlCanon.lean`, `Graph.lean` | term model, XMLLiteral c14n, graphs/datasets, bnode renaming; eqb transitivity + membership/length lemma families |
| Isomorphism | `RDF/Isomorphism*.lean` | §3.6 spec + witness-returning bounded search, soundness proved |
| Canonicalisation | `RDF/Canonical*.lean`, `Harness/CanonProbe.lean` | RDFC-1.0 parameterised by `HashAlgorithm`; §3 sortedness + issuer injectivity proved; rdf-canon suite 86 pass, 0 fail (of 86) |
| SPARQL algebra | `SPARQL/Algebra.lean`, `PropertyPath.lean`, `Invariants.lean` | 15-constructor GraphPattern (GRAPH/LATERAL/BIND/VALUES/SERVICE/sub-SELECT/paths), dataset-aware `evalIn`; monotonicity/merge/empty laws proved |
| SPARQL physical paths | `SPARQL/IndexedEvalRefinement.lean`, `AlgebraRefinement.lean`, `StoreBackend.lean`, `StorePlan.lean`, `StoreFastPath.lean`, `StoreDataset.lean` | exact-list indexed BGP/hash-join refinement; partial declarative algebra refinement; backend capabilities, planning, fast paths, and dataset routing |
| Cottas | `Cottas/*.lean` (33 files at `73209342c232`) | total reader/writer, dictionaries, on-disk search, selective decode, planning, pruning, counts, presence and offset indexes |
| HDT | `HDT/*.lean` (5 files at `73209342c232`) | container, theorems, dictionary, triples, and static store |
| SPARQL expressions | `SPARQL/Expr*.lean` | §17 EBV, scaled numerics (order proved), §17.3 logic, builtins; EXISTS/NOW/extension fns/SERVICE via `EvalEnv` parameters |
| SPARQL query | `SPARQL/Query*.lean` | QueryPattern→GraphPattern lowering, forms, modifiers, aggregates; ORDER BY permutation + DISTINCT laws proved; LATERAL cases pinned; DESCRIBE returns the Concise Bounded Description (`RDF/ConciseBoundedDescription.lean`, record: [`docs/designissues/2026-10-10-sparql-describe.md`](../../docs/designissues/2026-10-10-sparql-describe.md)) |
| RML | `RML/*.lean`, `Codec/{Inflate,Archive,Lzma,Xz}.lean`, `Harness/RmlRun.lean` | the five KG-Construct modules: validation of the mapping graph, CSV/JSON/XML/SPARQL sources, gzip/zip/tar/xz, logical targets, gather maps (RML-CC), quoted triples as RDF 1.2 reifiers (RML-star), function registry (RML-FNML); `l4rml` rml-core 75 pass, 0 fail, 1 fixture defect (out of 76); rml-io 61 pass, 0 fail, 11 fixture defect, 1 database source (out of 73); rml-cc 35 pass, 0 fail (out of 35); rml-star 10 pass, 0 fail, 8 fixture defect (out of 18); rml-fnml 20 pass, 0 fail (out of 20); record: [`docs/designissues/2026-10-10-rml-modules-in-lean.md`](../../docs/designissues/2026-10-10-rml-modules-in-lean.md) |
| SPARQL results | `SPARQL/Results*.lean` | SRX/SRJ/CSV/TSV parse+serialise; SRJ N-row shape theorem proved |
| RDFS | `RDFS/Vocabulary.lean`, `RdfsCore.lean`, `Closure*.lean` | rdfs-core derivation relation + closure; extensive/sound/complete-at-saturation proved |
| OWL 2 | `OWL/*.lean` (RL closure, `ClassExpr.lean` class-expression reader, `Materialise.lean`, the tableau refuter `Refute.lean` with `NegationGoals.lean` and `CountingOracle.lean`, the refutation-certificate checker `DirectCert.lean` (`checkCert_sound`) with its reader and emitter `RefuteCert.lean` (`docs/designissues/2026-10-10-owl-dl-refutation-certificates.md`), species `SyntaxDL.lean`, the OWL 2 RDF-Based Semantics regime `OWL/RdfBased/{Spec,Rules,Witness,Engine,Clash,Tests}.lean`), `Harness/OwlProbe.lean` (`l4owl-probe`) | default regime = OWL 2 RL/RDF closure; `--dl` = closure + materialisation + refuter (`some false` must hold in every model); `--rdf-based` = OWL 2 RDF-Based Semantics (https://github.com/danbri/factoidal/issues/721): RL closure + 17 rule constructors and the Table 5.6 existential witnesses, each proved sound against `RdfBased.RdfBasedConditions` (36 cited conditions, satisfiability witness), and 5 clash rows (`Clash.lean`) proved against the same bundle, no comprehension layer, no refuter; buckets pass = PROVED, `not-refuted` = never counted as proved (`docs/designissues/2026-10-10-owl2-rdf-based-semantics.md`). Measured 2026-10-10, `--dl --refute-ms 3000`: type-inconsistency 126 pass, 1 fail, 1 skip (out of 128); type-positive-entailment PositiveEntailmentTest 194 pass, 12 fail (out of 206), the 12 are `test:species FULL`-only cases annotated DIRECT and are also judged by `--rdf-based`; type-consistency ConsistencyTest 354 pass, 0 fail (out of 354); syntax-dl 422 pass, 1 fail, 1 skip (out of 424); type-negative-entailment 46 pass, 0 fail (out of 46) with the refuter asked on 11 units; default RL run TOTAL 1234 pass, 221 fail, 2 skip (out of 1457); `--rdf-based all.rdf` PositiveEntailmentTest 147 pass, 54 fail (out of 201), InconsistencyTest 55 pass, 73 fail (out of 128), NegativeEntailmentTest 0 pass, 0 fail, 23 not-refuted (out of 23), ConsistencyTest 0 pass, 0 fail, 347 not-refuted (out of 347), the 12 FULL-only DIRECT cases 7 pass, 5 fail; `--species` 488 pass, 0 fail, 1 local-override (out of 489; `WebOnt-I5.5-005`, https://github.com/danbri/factoidal/issues/711). Left failing and why: `docs/designissues/2026-09-07-lean-owl-corpus-gap.md` § 15, and § 7 of the RDF-Based record. Two refuter soundness defects were found on 2026-10-10 by probes, not by the corpus (`skills/measuring-inference` §§ 12-13) |
| RDF syntaxes | `Syntax/Lexing.lean`, `NTriples.lean`, `NQuads.lean`, `Turtle.lean`, `TriG.lean`, `IriResolve.lean`, `Harness/TurtleProbe.lean` | rdf11+rdf12 parse/serialise; RFC 3986 resolution (all §5.4 examples guarded); rdf-turtle eval 111 of 111, rdf-trig 107 of 108 |
| RDF syntaxes, lenient (recovery) mode | `Syntax/Diagnostics.lean`, `NQuadsLenient.lean`, `TurtleLenient.lean`, `LenientFeed.lean`, `*LenientTheorems.lean`, `Wasm/Ops/Lenient.lean`, `Harness/LenientRun.lean` | https://github.com/danbri/factoidal/issues/716: skip a bad statement (N-Triples, N-Quads: to the end of its line; Turtle, TriG: to the next `TurtleStatementScan` cut at or after the error), report a `Diagnostic` (16 stable classes, offset, line, column), keep the good statements; `maxErrors`; reference and streaming walks (TriG: reference only). Proved for all four syntaxes: the lenient parse reports nothing exactly when the strict parser accepts, and then returns the strict result (`parse*Lenient_of_ok`, `parse*_ok_of_lenient_quiet`). Streaming = reference is checked by split `#guard`s and by `l4w3c --lenient` (5-character chunks), not proved. `l4w3c --lenient` over the RDF 1.1 and 1.2 Turtle, TriG, N-Triples and N-Quads syntax manifests: 1050 pass, 0 fail (out of 1050). Surfaces: dispatch op `parseDocument`, npm `parse(text, {lenient: true, maxErrors})`, `l4factoidal parse --lenient FILE` (JSON-line diagnostics on stderr). Streaming, `tests/stack/lenient_scaling.sh`: 204 MB of N-Quads in 28.6 s of CPU at 27 MB peak, time linear and memory flat from 25 MB (16 pass, 0 fail (out of 16)). Record: section 3a of the parsing strategy record below |
| XML | `XML/*.lean`, `Harness/XmlConfRun.lean` (`l4xmlconf`), `xmlconf-probe` | non-validating XML 1.0 and 1.1 parser (version from the declaration) with 20 WFCs, a bytes decoder (`XML/Encoding.lean`: UTF-8, UTF-16, ISO-8859-1, US-ASCII), Namespaces, and a validity layer (`XML/Validity.lean`). DTD attribute defaults are supplied (3.3.2, 5.1); `XML/XmlAttributes.lean` checks `xml:lang`, `xml:id` and `xml:base` values. `l4xmlconf` 2026-10-10: plain 1861 pass, 0 fail (out of 1861); namespaces 56 pass, 0 fail (out of 56); encodings 65 pass, 0 fail (out of 65); XML 1.1 258 pass, 0 fail (out of 258); validating 2184 pass, 0 fail (out of 2184); output (defaults) 46 pass, 0 fail (out of 46); xml-local 47 pass, 0 fail, 0 expected-fail (out of 47). Record: [`docs/designissues/2026-10-10-xml-profile-widened.md`](../../docs/designissues/2026-10-10-xml-profile-widened.md) |
| GRDDL | `GRDDL/Discovery.lean` (sections 2 and 4, bases), `GRDDL/Agent.lean` (`glean`: sections 3 and 5 read from the GRDDL results of the namespace and profile documents, computed together to a fixpoint; section 2 merge renames blank nodes apart; retrieval is a parameter), `GRDDL/AgentTests.lean`, `Harness/GrddlRun.lean` (`l4grddl`) | stylesheets run through `XSLT/Transform.lean`. `l4grddl` 2026-10-10: 47 pass, 0 fail (out of 47 decided), 0 no transformation, 5 unavailable, 0 refused, 3 related test passed, 13 local override (out of 68). Both language representations of `td/conneg.html` are vendored (`docroot/variants.tsv`; the harness gives `glean` a retrieval function that takes the agent's language range, chooses by RFC 4647 section 3.4 and falls back to the server's default variant; the language of each case is a table in `Harness/GrddlRun.lean`: `langconneg2` asks for `de`, `langconneg3` retrieves every variant and merges). The 13 local overrides (https://github.com/danbri/factoidal/issues/730): 7 networked inputs the W3C edited after 2007 (http to https in `base`/`link` attributes; the 2007 archive holds only the local inputs), 4 `loopx` cases where the served `loopy.xsl` names `one` and the expected outputs name `one.xsl`, and `langconneg2`/`langconneg3`, whose served representations link to `https://musicbrainz.org/...` where the expected outputs say `http://` (owner, 2026-10-10: "730 - do langconneg2 and langconneg3 join h - yes"). The 5 unavailable cases need server-side stylesheets that now answer with a W3C login. Fixtures and their provenance: `third_party/testing/grddl/PROVENANCE.md`; issue https://github.com/danbri/factoidal/issues/668 |
| JSON | `JSON/*.lean` | RFC 8259 parser/serialiser; escape + literal round-trips proved |
| Crypto | `Crypto/SHA2*.lean`, `Crypto/Ed25519.lean` | SHA-256/384/512 + `HashAlgorithm` agility; size theorems; FIPS vectors (million-byte ones parked opt-in). Ed25519 = the ONE `@[extern]` (HACL\* C through `lakefile.lean` `extern_lib`) |
| JSON-LD 1.1 | `JSONLD/{Context,Expand,ToRdf,Compact,OrderedMap,Flatten,NodeMapTheorems,FromRdf,Html,Frame}.lean`, `Harness/{JsonLdProbe,JsonLdApiProbe,JsonLdFrameRun,JsonLdScale}.lean` | context processing, expansion, toRdf, compaction (§6), flattening (§7), Serialize RDF as JSON-LD (§8.5-8.7), HTML script extraction, Framing (`l4jsonld-frame`, run from the repo root: 91 pass, 1 fail (out of 92); the one failure, `#t0010`, is a json-ld-1.0 version dispute); loader is a parameter. `l4jsonld-probe` toRdf 467 pass, 0 fail, 0 skip (out of 467); `l4jsonld-api` expand+compact+flatten+fromRdf+html 791 pass, 0 fail, 2 local-override (out of 793) — matching the F\* runners manifest for manifest |
| VC / DID | `VC/*.lean`, `Harness/VcProbe.lean` | Data Integrity `eddsa-rdfc-2022` create/verify (canonical forms, datasets, JSON-LD documents; primitives are parameters), base58/multibase with the decode-of-encode theorem, did:key both ways, the VCDM 2.0 data-model checks (`VC/Credential.lean` namespace `Doc`: structure, relatedResource digests, DATA_LOSS_DETECTION_ERROR, type-term resolution); `l4vc-probe` 236 pass, 0 fail (out of 236, 2026-10-10: RFC 8032 22, did:key 8, vc_runner roundtrip 8, W3C vc-di-eddsa spec vectors 20, SHA-256 differential 61, VCDM 2.0 fixtures 117). The wasm dispatch serves the lot as `vc*` and `didKeyResolve` ops (`Wasm/Ops/Vc.lean`) |
| Unicode case mapping | `Text/CaseMap.lean`, `Text/CaseMapData.lean` (generated), `Text/CaseMapTests.lean`, `tools/gen_casemap.py` | Unicode default case mapping (`upperCase`, `lowerCase` with SpecialCasing unconditional lines and Final_Sigma, language-independent), simple `caseFold`, F&O 3.1 5.6.1.1 `caseVariants`/`ciRanges`, the index fold `searchFold`; tables are sorted run arrays searched by binary search, generated from Unicode 15.1.0 with source digests in the header. Callers: `Fn.String.upperCase`/`lowerCase` (SPARQL UCASE/LCASE, RIF, GREL), regex flag `i` (`XSDPattern.parseCpsWith`), `Storage/LiteralGramIndex.lean`. Lean core `String.toUpper`/`toLower` map ASCII only: use them for BCP 47 tags, header names and grammar keywords, never for text; record: [`docs/designissues/2026-10-10-unicode-case-mapping.md`](../../docs/designissues/2026-10-10-unicode-case-mapping.md) |
| Wasm | `Wasm/`, `docs/web/hub/assets/l4/`, skill `lean4-wasm-export` | Lean→C→wasm via Emscripten (1.4 MB, ~40 ms load); hub post 36 runs Lean and F\* side by side |
| Tests/demo | `Tests.lean`, `Demo.lean` | build-time guards + `#print axioms` audit; runnable tour |
| Docs | `README.md` / `PORT_NOTES.md` | reviewer reading order / F\* correspondence, decisions, assumption report |

Measured 2026-08-22, late: the library has zero `sorry`, zero user `axiom`, zero `native_decide`, and, re-measured 2026-09-02, TWO `@[extern]`/`opaque` families: HACL* Ed25519 (`Crypto/Ed25519.lean`, library) and the POSIX range-I/O host library (`Harness/PosixRangeIO.lean`, `extern_lib libl4blockhost`: `l4_block_pread`, `l4_delta_log_append_sync_at_size`, `l4_atomic_replace_file_sync`; harness side, pure I/O). ⚠️ `partial def` is NOT zero and is GROWING FAST. **Re-measured 2026-08-29: 212 declarations across 35 library files, plus 14 across 9 harness files.** The library breakdown is XPath 44, ShEx 50, OWL 37, XSLT 27, RIF 15, Math 11, Geo 6, MathML 5, Testing 4, GRDDL 3, XForms/JSONSchema/CSVW 2 each, and XSD/Storage/Schematron/HTTP 1 each. `formal/lean4/Wasm/` contains none. RDF, RDFS, SPARQL, Cottas, HDT, SHACL, JSON-LD and `Unified/` have no live `partial def` declarations. OWL is not clean: its 37 include the tableau search and materialization functions. WHY IT COSTS: a `partial def` compiles to an opaque constant — no equation lemmas, no kernel reduction, invisible to `decide`. ⚠️ It is NOT invisible to `#guard`: `#guard` evaluates through the INTERPRETER, so a guard whose expression calls a `partial def` does run and does fail the build when the expression is false. Measured 2026-08-26 on a `partial def loopy`: `#guard loopy 3 == 99` errors with "did not evaluate to `true`", while `example : loopy 3 = 7 := by decide` fails with "its `Decidable` instance did not reduce to `isTrue` or `isFalse`". The line is interpreter vs kernel. So a `partial def` CAN be pinned by `#guard` and CANNOT be the direct subject of the same equation proof. That happened on 2026-08-26: design doc §4.7 puts `RIF.Engine.saturate` on the left of `unified_adequate_rifCore`, and `groundTm`/`matchFormula`/`qualifyTm` being `partial` forced the landed theorem onto `DatalogProgram.lfp`, with engine agreement demoted to a `#guard` pin (https://github.com/danbri/factoidal/issues/612). Whether these are accepted debt or must be made total is tracked with the full breakdown at https://github.com/danbri/factoidal/issues/617. Do not quote any `partial def` figure without re-measuring. Method that excludes prose mentions inside comments: `rg '^\s*(private\s+|protected\s+)?partial def\b' formal/lean4/L4Factoidal`.

How the parsers are built (reference parser, streaming execution for the
shard packer, the proofs between them, the costs paid and open):
[`docs/designissues/2026-09-03-rdf-parsing-strategy.md`](../../docs/designissues/2026-09-03-rdf-parsing-strategy.md).

## Toolchain

- Install: `curl -sSf https://elan.lean-lang.org/elan-init.sh | sh -s -- -y`.
- **PATH trap (2026-08-22, paid for):** every fresh harness shell
  needs `export PATH="$HOME/.elan/bin:$PATH"` or `lake` is absent —
  and a gate script that silently loses `lake` LOOKS like it passed.
  During the MINUS sabotage demo the first "the build caught nothing"
  result was actually "the build never ran" (`command not found`
  filtered away by a grep for 'error'). Always confirm the tool ran
  before trusting its silence.
- The lakefile is `lakefile.lean` (Lean DSL) since the VC stage — the
  TOML format has no `extern_lib`; keep new targets in the DSL.
- **zsh loop variable trap (2026-10-10):** `path` is a special array
  tied to `PATH`. A read-only instruction-file loop used `for path in`
  and two subsequent git metadata reads failed with `command not found`.
  Run a fresh shell to restore the environment; use a descriptive ordinary
  variable such as `instruction_file`, never `path`, for these loops.
- **zsh exit-status trap (2026-10-10):** `status` is read-only. A build
  followed by `status=$?` ran but its wrapper failed before showing the
  log or propagating the build result. Use `build_status=$?`, then
  `tail -n 100 "$build_log"; exit "$build_status"`; inspect the log to
  distinguish a compiler failure from a wrapper failure.
- **Serialize red phases and integration builds (2026-10-10):** a deliberate
  failing regression build can remove that module's `.olean`. Concurrent
  dependent builds then report a missing artifact even if they previously
  compiled. Stabilize the source and complete the focused red-to-green run
  before launching integration builds; do not misclassify this as a toolchain
  failure or trust a build racing a red phase.
- **Check new files after staging (2026-10-10):** an unstaged
  `git diff --check` omits untracked files. The native migration's final
  staged check exposed blank lines at EOF in three unchanged vendored HACL*
  C files. Preserve their source hashes; check nonvendored changes separately
  and record the upstream whitespace exception rather than silently editing
  pinned third-party code.
- `formal/lean4/lean-toolchain` pins the version (4.33.1 at
  creation); elan auto-fetches it. Bump only deliberately, own
  commit, green `lake build`.
- **Zero dependencies** — no mathlib, no batteries, core Lean only.
  Keep it that way until a theorem genuinely needs mathlib (that
  costs a multi-GB fetch or `lake exe cache get` on every fresh
  machine). Corollary: lemma names found via loogle/leansearch are
  often mathlib-only — check for `Init.*`/`Std.*` (core) namespaces
  before using.

## Build, test, demo

- **Working-directory invariant (paid for repeatedly):** `lake` discovers its
  project from the current directory; for this repository every `lake build`,
  `lake exe`, or `lake env` invocation must use `formal/lean4/` as its explicit
  working directory. Never run `lake` from the repository root, even if a
  previous command changed directory. Check the current tool call's `workdir`
  before every Lean command. Git/status/commit/push commands belong at the
  repository root. Do not combine a `lake` command and repository-root Git
  command in one shell invocation and assume a prior `cd` still applies; use
  separate tool calls or set the working directory explicitly for each. This
  repeated error caused invalid root-level Lake failures on 2026-08-31.
- `cd formal/lean4 && lake build` — this IS the test run and the
  proof check: `#guard` expressions evaluate during elaboration, so a
  wrong answer is a build error; every theorem is kernel-rechecked.
- `formal/lean4/Wasm/build-wasm.sh` — rebuild the WebAssembly artifact.
  Needed whenever a Lean change must reach the browser, and whenever
  `lean-toolchain` is bumped (the wasm objects are generated from the
  toolchain's core sources, so a version bump without a rebuild leaves
  the artifact built against the old core library). Since 2026-10-09 the
  outputs (`l4factoidal.wasm`, `l4factoidal.mjs` and their copies under
  `npm/`) are NOT committed; they are in `.gitignore`. The `web` set of
  `danbri/factoidal-builds` builds them from a core commit, and
  `tools/fetch-builds.sh` installs them. A local run of the script is for
  local testing; do not stage its output.
- `lake env lean --run Demo.lean` — the human-facing tour: BGP rows
  printed Turtle-ish, the §18.5 MINUS domain-disjointness contrast,
  live monotonicity, RDF 1.2 triple-term matching, the literal
  equality subtleties.
- **Sabotage testing** (do this when extending): deliberately break a
  semantic clause, confirm `lake build` FAILS at a named `#guard` or
  theorem, restore (`git checkout -- <file>`), confirm green.
  Verified example: deleting MINUS's `!domainsDisjoint` conjunct
  fails `Tests.lean:89` with the violated expression printed.
- ⚠️ **`Wasm/Ops/*.lean` was OUTSIDE that safety net until 2026-08-26.**
  The dispatch ops carried no `#guard` at all — they were gated only by
  `Wasm/native-smoke.sh` and `Wasm/cli-smoke.sh`, which need a built
  binary and an explicit run. Measured by sabotage while adding the
  CL/IKL ops of https://github.com/danbri/factoidal/issues/623:
  replacing `clFiniteSat`'s `noSeqQuantList` test with `false` — so the
  op ANSWERS where it is meant to REFUSE, outside the hypothesis of
  `satisfiesFin_eq` — left `lake build` reporting
  "Build completed successfully"; only the smoke script failed. A
  session that ran the build and not the scripts would have shipped it.
  `Wasm/Ops/CL.lean` now carries `#guard`s for its refusals and
  refutations (re-running the same sabotage fails the build at the two
  named guards), and the same should be done for the other ops modules,
  which are still smoke-script-only. When you add an op, pin the
  NEGATIVE cases: an op answering `true` unconditionally passes every
  affirmative guard.
- New `#guard`s go in `Tests.lean`; new theorems in `Invariants.lean`
  (or a sibling), each with a doc comment citing the spec section.

## Function semantics live in `L4Factoidal.Fn` — front ends do not reimplement

`L4Factoidal/Fn/` holds the
[XQuery and XPath Functions and Operators](https://www.w3.org/TR/xpath-functions/)
semantics ONCE, over the `L4Factoidal.XSD` value spaces:
`Fn/Numeric.lean` (F&O §6), `Fn/String.lean` (§5), `Fn/Boolean.lean`
(§9), `Fn/Duration.lean` (§10.5-10.6), `Fn/DateTime.lean` (§10.4,
§10.5, §10.7-10.8), `Fn/List.lean` (RIF-DTB 4.11) and
`Fn/Casting.lean` (§17).

Three front ends CALL it and none of them carries its own copy:
`RIF/Builtins.lean` adds the RIF-DTB `func:`/`pred:` names, signatures
and guards; `SPARQL/Expr.lean` adds §17 typing and errors;
`XPath/Eval.lean` adds XPath 1.0's coercions.

Rules when you touch any of them:

* A new function that any two of RIF, SPARQL, XPath or XSLT need goes
  in `Fn`, not in a front end.
* Where two Recommendations define the same-named function
  DIFFERENTLY, keep both and name the difference. `Fn/Theorems.lean`
  carries a theorem per difference with the input that witnesses it
  (`substring_sparql_differs_from_fando`,
  `substring2_rif_differs_from_fando`,
  `langMatches_extended_differs_from_basic`). Reconciling them is
  wrong: each front end must answer what its own specification says.
* The agreement theorems in `Fn/Theorems.lean` are `rfl`, and that is
  their job — they are a GUARD. Reintroduce a second copy of
  `fn:encode-for-uri` in `SPARQL/Expr.lean` and
  `encodeForUri_sparql` stops type-checking. A comment saying "do not
  duplicate this" does not do that.
* Changing `Fn.String.lowerCase` changes the literal search index fold in
  the same landing (`Storage/LiteralGramIndex.foldChars`). The index header
  said the two "cannot drift because there is one function"; that held only
  while both were `String.toLower`. Moving `LCASE` to Unicode default case
  mapping without the fold would have made the index drop rows the scan keeps
  (`École Normale` for the needle `école`), with every suite green, because no
  guard tied the two. The guards are now in `LiteralGramIndex.lean`
  (2026-10-10, https://github.com/danbri/factoidal/issues/706).
* A `#guard` where a theorem is expected usually means both sides call
  an `@[extern]` `String` primitive (`toLower`, `startsWith`), which
  the KERNEL cannot reduce: `decide` gets stuck and `rfl` fails.
  `native_decide` is not the answer here — it is banned.

Design record: `docs/designissues/2026-09-07-function-library.md`.
Tracking: <https://github.com/danbri/factoidal/issues/664>.

## Proof policy (stricter than the F\* tree's)

- **No `sorry`. No user `axiom`. No `native_decide`** (it adds trust in
  the compiled evaluator via `Lean.ofReduceBool`). Partial functions
  (`partial def`) also count as debt. New semantic, SPARQL, storage, and block-
  engine definitions must be total. Existing partial declarations outside
  those areas are measured above and tracked separately.
- Audit: `#print axioms <theorem>`. Acceptable base is exactly
  `propext`, `Classical.choice`, `Quot.sound` (Lean's standard
  foundations). `Tests.lean` keeps audit lines on the headline
  theorems so every build log shows it.
- **A theorem module is checked only if a build root imports it.** `lake
  build` builds the modules that the roots of `lakefile.lean` reach
  (`L4Factoidal.lean` for the library). A new `*Theorems.lean` that nothing
  imports compiles in an editor and in `lake env lean FILE`, and is never
  checked again. Paid for 2026-10-13: `Storage/Sbm11/ParallelScanTheorems.lean`
  (stage 1 of https://github.com/danbri/factoidal/issues/799, theorem
  `parallel_acc_eq`, reported as proved and checked by hand) had no olean
  in the build tree since it landed on 2026-10-12; it is now imported by
  `L4Factoidal.lean`. Add the import to
  `L4Factoidal.lean` in the same commit, and check that
  `.lake/build/lib/lean/<path>.olean` exists after `lake build`. A walk of
  the imports from the roots on 2026-10-13 found two more such modules:
  `L4Factoidal.OWL.ComprehensionTheorems`, `L4Factoidal.RDF.GraphPatterns`.
- Well-formedness witnesses for string constants are `rfl` (kernel
  evaluation) — the Lean counterpart of F\* `assert_norm`. For
  literals built by concatenation at call sites, use the autoparam
  pattern: `def iri! (s : String) (h : isIri s := by rfl) : WfIri`.

## Purity doctrine — the Lean answer to F\* `assume val`

Lean's equivalents are `axiom`, `sorry`, `@[extern]`/`opaque` (host
implementations), and `partial`. This project uses NONE of the first
two. `partial` was harness-only by design, but has since entered
non-core library modules (see the baseline note above — open decision); `@[extern]`/`opaque`
exists in two places. The second, since 2026-08-31, is the harness-side
POSIX range-I/O library `Harness/PosixRangeIO.lean` (`extern_lib
libl4blockhost`: `l4_block_pread`, `l4_delta_log_append_sync_at_size`,
`l4_atomic_replace_file_sync` — pure I/O, no semantics). The first is
the CRYPTO extern family, HACL\* via Lake's
`extern_lib` (`lakefile.lean`, `ffi/hacl_ed25519.c`), permitted under
the crypto-policy skill's Lean 4 amendment. It has TWO members:
`Crypto/Ed25519.lean` (`secretToPublic`, `sign`, `verify`) and, since
2026-09-02, `Crypto/SHA2Native.lean` (`sha256Hacl`). Each carries its
trust statement in the module header and its run-time measurement in
`lake exe l4vc-probe` — RFC 8032 vectors for Ed25519, and a
`sha256 differential` section for `sha256Hacl` against the pure Lean
`Crypto.sha256`, which remains the specification and remains what every
`#guard` and every theorem evaluates. Hosts choose between them through
an explicit hasher PARAMETER (`Storage/BlockMerkle.lean`'s `Hasher`),
never through `@[implemented_by]`: a `#guard` runs in the interpreter,
which cannot call an extern. The ten
`assume val`s in `SPARQL11.Algebra.fst` (none in the ported fragment)
each dissolve by parameterisation when their feature is ported:

| F\* `assume val` | Pure Lean form |
|---|---|
| SHA/MD5 hash builtins (§17.4.4) | implement in pure Lean; provable against a spec |
| Unicode case mapping | pure tables/functions: **done 2026-10-10**, `Text/CaseMap.lean` with tables generated from Unicode 15.1.0 (`tools/gen_casemap.py`), record `docs/designissues/2026-10-10-unicode-case-mapping.md` |
| `NOW()` | timestamp passed as an argument (`EvalEnv.now`); **done 2026-10-10** (https://github.com/danbri/factoidal/issues/743): each IO entry of the ops layer reads the clock once per execution (`Wasm/Ops/Clock.lean`, `Std.Time.Timestamp.now`) and formats it with the pure `SPARQL/Now.lean` `dateTimeOfUnixMillis`; the pure ops keep `now` as a parameter, default `none`; **2026-10-10** (https://github.com/danbri/factoidal/issues/748): the pure dispatch entries take it as an optional last argument (`Wasm/CoreDispatch.lean` `nowArg`, checked by `SPARQL/Now.lean` `isDateTimeLexical`), and the `l4block-*` query tools read the clock once per query (`Wasm/Ops/Clock.lean` `emptyEnvNow`) |
| `extension_function_call` (§17.6) | a typed function argument to eval, not a global registry |
| `service_endpoint_lookup` | an endpoint→graph map passed into evaluation |
| `eval_property_path_fwd` | F\* file-ordering artifact; doesn't arise |

Principle: what F\* asserted in a comment ("pure from F\*'s
perspective") Lean expresses in types — the semantics is a total
function of explicit inputs; real I/O lives typed in `IO` at the
executable edge only.

## Interactive tooling

- **lean-lsp-mcp** — registered in `.mcp.json` as `lean-lsp`, run via
  `uvx lean-lsp-mcp` (needs uv:
  `curl -LsSf https://astral.sh/uv/install.sh | sh`). The Lean
  analogue of the repo's `fstar` MCP: file diagnostics, the GOAL
  STATE at a position (the thing you need when a tactic fails), hover
  docs, lemma-search bridges. First call is slow (boots the Lean
  server on the lake project). Prefer it over re-running `lake build`
  to chase one error.
- **Lemma search**: https://loogle.lean-lang.org/ (by type shape,
  e.g. `?a ++ ?b = ?b ++ ?a`), https://leansearch.net/ (natural
  language); in-Lean `exact?`, `apply?`, and `simp?` (then PIN the
  lemmas it reports — don't leave bare `simp?`).
- For a human reviewer: the VS Code "lean4" extension's infoview.
- Deeper automation (aesop, omega is already core, mathlib tactics)
  only when a theorem demands it — see the zero-dependency rule.

## Pitfalls already paid for (don't rediscover)

1. **Derived `BEq` is lawless.** `deriving BEq` gives an instance
   with no `LawfulBEq`, so `x == x` is unprovable by `simp` and
   `beq_iff_eq` is unavailable. Derive `DecidableEq` INSTEAD and let
   `instBEqOfDecidableEq` provide a lawful `==`. (Cost: every proof
   downstream of a `TextDirection` BEq derivation failed until the
   derivation was dropped.)
2. **`List.filter_filter` conjunction order**: core states
   `filter p (filter q l) = filter (fun a => p a && q a) l` — outer
   predicate FIRST. State fusion theorems in that order.
3. **Subtype instances**: `{s : String // p s}` derives
   `DecidableEq` for free but needs manual `Hashable`/`Repr`/
   `ToString` instances (one-liners on `.val`).
5. **`split` and `generalize` unfold Nat literals.** On a subterm such as
   `d0 * 268435456 + ...` both tactics compare candidates by definitional
   unfolding of `Nat.mul` on a unary literal and never return (2026-09-02,
   `decodeEscape_length`; over seven minutes of CPU with no output). Move
   the arithmetic behind a function that takes the number as a parameter
   and prove the lemma with that parameter a variable. Full recipe and the
   other proof patterns: `skills/lean4-proof-patterns`.
4. **`abbrev` keeps dot-notation**: `abbrev Graph := List Triple`
   still resolves `g.mem` to `Graph.mem` — safe to define namespace
   functions on abbrevs.
5. **Sabotage-tests can void themselves** — see the PATH trap above.
6. **Parallel worktree agents eat disk**: each agent worktree is a
   full checkout (~1.2 GB with the committed binaries) plus its own
   `.lake` build; eight at once plus caches hit ENOSPC on a 228 GB
   laptop (2026-08-22) and a ninth spawn failed. Before a fan-out:
   `df -h /`, `git worktree prune`, remove stale worktrees under
   `.claude/worktrees/`, `npm cache clean --force`; budget ~1.5 GB
   per agent; never delete the owner's own caches
   (`~/.cache/huggingface` was 20 GB) without asking.
   THE FIX that actually worked (9.5 GB reclaimed in one pass): the
   bulk of a worktree is the committed platform binaries + bundles,
   byte-identical across worktrees. On APFS, replace each worktree's
   copy with a clone of the main checkout's file (`cmp -s` to verify
   identical, then `cp -c main/f wt/f.tmp && mv wt/f.tmp wt/f`) —
   blocks are shared, git sees no change, agents keep working.
   (Since 2026-10-09 binaries and bundles are not committed, so a new
   worktree of `danbri/factoidal-core` holds them only after
   `tools/fetch-builds.sh` runs; see iron rule 9. The sizes above were
   measured before the split.)
7. **Well-founded recursion blocks `decide`/`rfl`.** A mutually
   recursive function group (the JSON parser's five functions)
   compiles via well-founded recursion, so the kernel cannot unfold it
   by evaluation and `decide`/`rfl` get stuck. Recipe: `unfold <fn>`
   (its equation lemma) then `decide`; or keep parsers structurally
   recursive on a fuel `Nat` where possible.
8. **`/-` inside prose opens a block comment** — a doc comment or
   string containing `/-` (e.g. "XML/-JSON") nests a new comment and
   silently swallows the file to EOF, exactly like F\*'s `(* *)` trap.
   Never write `/-` in comment prose; `local` is a reserved word in
   Lean 4 too (2026-08-22, results-formats port).
9. **Integrate agent branches with MERGES, then push; never
   `git pull --rebase` afterwards.** A rebase replays the branch's
   commits onto origin and re-hits the same additive conflicts
   (`L4Factoidal.lean` imports, `PORT_NOTES.md` appends) the merge
   already resolved (2026-08-22). Recipe: `git merge --no-edit
   origin/lean4/<topic>` → resolve additive conflicts by keeping BOTH
   sides (dedupe import lines) → `lake build` green → `git pull
   --no-rebase` if origin moved → `git push`.
10. **`decide`/`rfl` over a concrete parser or tokenizer result eats
    RAM by the gigabyte, and the swap it forces FILLS THE DISK.** One
    theorem `tokensOf (tokenize "<http://a/b>") = …` cost 72 s and
    10 GB; ten of them in one file killed `lean` with signal 9, and
    the macOS swapfiles it wrote took the laptop from 7 GB free to
    0 GB — the disk watchdog fired three times before the cause was
    known (2026-08-22, SPARQL parser port). Concrete-input facts are
    `#guard`s (compiler evaluation, free); keep at most one `decide`
    proof as a demonstration. Relatedly, `split at h` on a scrutinee
    holding `pX topFuel …` weak-head-normalises every fuel level —
    expose `parseSparqlWith (fuel : Nat)` and keep fuel symbolic in
    proofs (`cases h : e`). If free disk oscillates with no large
    files appearing, suspect swap from a proof, not a writer.
11. **Probe executables resolve test paths from the CWD.**
    `lake exe l4jsonld-probe` / `l4sparql-probe` look for
    `third_party/testing/...` relative to where they run; `lake exe`
    runs them from `formal/lean4`, so invoke the built binary from the
    repo root (`formal/lean4/.lake/build/bin/l4jsonld-probe`) or pass
    an absolute manifest path where the probe accepts one. A probe
    that prints "manifest not found" has measured nothing.

12. **A proof about a match arm splits on EVERY scrutinee of that
    arm's inner match.** `strLitNextStep`'s `\u` arm matched on
    `hexVal h0, hexVal h1, hexVal h2, hexVal h3` at once, so any proof
    that reached it produced 16 cases; the `\U` arm produced 256. With
    the surrounding nineteen arms also split, `simp_all` reached
    10.5-12 GB and took SIGKILL, measured three ways (2026-08-24,
    <https://github.com/danbri/factoidal/issues/574>). The fix is to
    factor the inner match into one `Option`-valued helper — `hex4`,
    `hex8` — so the arm splits two ways. Behaviour is unchanged and the
    existing `#guard` differential table against the legacy definition
    is what proves that.
13. **An arm does NOT carry the earlier arms' negations.** Lean's
    equation compiler turns overlapping patterns into a case tree, so a
    catch-all arm such as `| c :: rest` gives you `c` and `rest` and
    nothing else — not `c ≠ '"'`, not `c ≠ '\\'`. A proof that needs
    those must state them as its own lemma
    (`strLitNextStep_plain`, `strLitNextStep_badEscape` in
    `Syntax/LocalityLiteral.lean`), proved by `unfold` then `split`
    over the arms. `grind` closes the residual cases that `simp_all`
    leaves, because it instantiates hypotheses that carry binders —
    `simp_all` does not.
14. **`cases h : f x` rewrites the GOAL, not the other hypotheses.**
    After it, `rw [h] at k` is still needed for every hypothesis `k`
    that mentions `f x`, and `rw [h] at k ⊢` then FAILS, because the
    goal no longer contains the pattern. Two rounds of the same error
    cost a rebuild each (2026-08-24).

15. **A `/-- ... -/` doc comment in front of `#guard` is a parse error**
    ("unexpected token '#guard'"; the doc comment must precede a declaration).
    Use `--` lines or a plain `/- ... -/` before a guard. And Lean string
    literals have `\xHH` and `\uHHHH` (exactly four hex digits) but NOT
    `\u{...}`: write an astral character (U+10400 and above) as the character
    itself or as `String.singleton (Char.ofNat n)` (2026-10-10, `Text/
    CaseMapTests.lean`; one build round each).

- **`lake build l4w3c` is not `lake build`.** The harness target skips
  every theorem-only module (`*Refinement.lean`, `*Theorems.lean` files
  nothing executable imports). A gate that builds only `l4w3c` can pass
  while an engine change broke the agreement proofs downstream — and a
  commit message then claims "full lake build clean" falsely.
  (2026-08-24: the SPARQL 1.2 EBV/literalPromote change broke
  `SPARQL.ExprRefinement` and `SHACL.SparqlTheorems`; two commits
  shipped before the full build caught it. When an engine definition
  changes, its spec-transcription twin — `ebvSpec`, `termToExpr?` —
  must move in the same commit.) Before any commit claiming build
  cleanliness: `lake build`, no target.

## Style contract (owner priority: W3C-expert readability)

- Every definition's doc comment cites the W3C document + section it
  implements; module headers state what is and is NOT ported and why.
- Spec/engine split: keep the plain evaluator as an executable semantic
  reference. The current tree also has hash joins, indexed BGP evaluation,
  backend planning, Cottas/HDT stores, and exact-list refinement proofs for
  the indexed SPARQL path. The owner chose on 2026-08-29 to make Lean the
  intended full-scope target. Add performance machinery in Lean and state its
  relation to the plain evaluator. The Block model, PushIR, PostgreSQL adapter,
  and TiKV adapter remain proposed; follow `skills/blockengine/SKILL.md`.

  PROVENANCE NOTE (2026-08-22, recorded after the owner rejected a
  fabricated rationale): the sentence above previously read "the split
  is absolute — never port them here", sat under the "owner priority"
  heading, and was Claude-authored in the skill-consolidation commit
  0d7219c75e4. No owner instruction said it. It then hardened into
  "must stay that way" in a design doc and into "the owner said
  porting hash-join machinery would destroy the tree's job" in chat.
  The owner's reply: "BS, I never said this." Every commit in this
  repo is authored as the owner's git identity (iron rule #13), so
  `git blame` CANNOT tell owner-written text from Claude-written text
  — provenance must be carried in the prose itself. Label
  Claude-inferred defaults as such, at the moment of writing.
- Naming: the certified six-rule RDFS fragment is **rdfs-core** /
  `RdfsCore` in identifiers and prose — never "ρdf" (owner,
  2026-08-22: the Greek letter reads as "pdf" on a phone). Cite the
  Muñoz–Pérez–Gutierrez 2007 name once, in a doc comment, for
  reviewers who know the literature.
- Theorem names state observational content
  (`Binding.lookup_merge`); `@[simp]` only on genuine
  simplification laws.
- `PORT_NOTES.md` is the F\*↔Lean ledger: update its correspondence
  table and assumption report with every ported module.
- When migrating modules between repositories, recheck assurance prose as
  well as imports. On 2026-10-10, two copied hash-module headers referred to
  an absent native harness and claimed universal hash agreement from finite
  differential tests. Corrected before commit: tests are measurements, not
  an equivalence theorem, and a source-tree run is not a destination-tree run.
  The native migration review also found copied Fn/XSD headers claiming
  caller centralization that was not migrated, and a benchmark description
  calling cardinality/preview checks complete result validation. Both needed
  a review correction: qualify source-only integration claims, and state
  exactly which outputs a measurement checks (a ten-row preview is not an
  answer-bag oracle).
- Before a cross-repository migration, fetch the source remote and inspect
  ancestry and relevant file differences. Preserve dirty source files: do
  not reset them or mix their uncommitted shared definitions into the port.
  Pin a commit and use `git show <commit>:<file>` for source contents; record
  deliberate destination repairs separately from the upstream snapshot.
- Iron-rule-#6 discipline carries over: NO conformance claims for
  the Lean side until a Lean executable reads the same W3C manifests
  `bin/w3c-runner` does (the continuation ladder at
  https://github.com/danbri/factoidal/issues/466).

## External Lean skills (2026-09-02)

Surveyed on the owner's suggestion. Vendored, unmodified, with provenance and
licence in `third_party/skills/leanprover-skills/`:

- `lean-proof` (leanprover/skills, Apache-2.0): the one-step-at-a-time
  proof method — one tactic then `done`, error priority (syntax, type,
  unsolved goals, linter), hardest case first, cleanup after the proof
  works, `suffices ∀ s, … by` + `convert` for "motive is not type
  correct". Symlinked into `.claude/skills/lean-proof`.
- `lean-mwe` (same source): minimal reproducible examples for upstream Lean
  or Lake bug reports. Symlinked into `.claude/skills/lean-mwe`.
- `lean-review` (gotrevor/lean-agent-skills, Apache-2.0, vendored in
  `third_party/skills/lean-agent-skills/`): the diff-scoped check registry
  (`maxHeartbeats`, `native_decide`, `axiom`, `sorry`, `unsafe`/`partial`/
  `opaque`, silenced linters) with `#print axioms` as the authoritative
  check. Symlinked into `.claude/skills/lean-review`.

Synthesized locally from the survey and from the 2026-09-02 Turtle fuel
proofs: [`lean4-proof-patterns`](../lean4-proof-patterns/SKILL.md) — the
no-Mathlib tactic set, fuel-independence theorem shape, nested-match
splitting, the large-Nat-literal unfolding trap, `rename_i` order, `omega`
after `List.length_cons`, and timed single-theorem compiles to bisect a hang.

Not vendored, cited for readers who want them:
[cameronfreer/lean4-skills](https://github.com/cameronfreer/lean4-skills)
(MIT; a Claude Code / Codex plugin with prove, autoprove, review, golf and
checkpoint commands, scripts and an LSP-first loop over lean-lsp-mcp; its
search-before-prove and tactic cascade assume Mathlib, which this tree does
not use — its two rules worth keeping are already policy here: theorem
statements are contracts and are not changed to make a proof pass, and the
only accepted axioms are `propext`, `Classical.choice`, `Quot.sound`);
[r-irbe/proof-skills](https://github.com/r-irbe/proof-skills) (53 Mathlib
and domain-mathematics skills);
[CBirkbeck/mathlib-quality](https://github.com/CBirkbeck/mathlib-quality)
(Mathlib style). The lean-lsp-mcp server itself is already wired here
(`.mcp.json`; tools `lean_goal`, `lean_diagnostic_messages`,
`lean_local_search`, `lean_multi_attempt`, `lean_verify`).

## Module headers may state a shortfall only with an issue and a test (2026-09-07)

A header sentence such as "deliberately does NOT implement X" is allowed only
next to the issue URL that tracks X and with an expected-failure case in the
relevant probe or Node suite (`skills/test-suites/SKILL.md` § Expected
failures). Owner, 2026-09-07: prose alone "is close to nothing". First
instance: `L4Factoidal/XMPP/Jid.lean` and https://github.com/danbri/factoidal/issues/676.
