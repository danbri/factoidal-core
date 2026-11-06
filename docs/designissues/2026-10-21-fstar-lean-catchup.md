# F\* catch-up with the Lean 4 tree, 2026-10-21

Owner, 2026-10-21, verbatim: "a subagent to bring f* up to date with lean4
progress, and report any conflicts."

Base: `origin/main` 450b2cc6. Between 2026-10-01 and 2026-10-21,
`formal/lean4` has 536 commits and `formal/fstar` has 7. This record lists
every Lean change in that period that changes the observable behaviour of a
function that the F\* tree also has, says what the F\* tree does, and records
the ports made and the conflicts found.

## 1. Method

Reading alone cannot see a behaviour difference, so the evidence is
measured (anti-pattern 28):

1. `git log --since=2026-10-01 -- formal/lean4/L4Factoidal/{SPARQL,RDF,OWL,
   JSONLD,Syntax,SHACL,ShEx,CSVW,RDFC}` (109 commits that are not WIP or
   merges), and the same log over all of `formal/lean4` (536 commits).
   Commits whose subject names only speed (a loop, an index, a `@[csimp]`
   twin "proved equal", a linear form, stack depth) or a Lean-only store
   (SBM11, qlvr, planner, DLOG, TDB2, LWS/Solid) are classed from the
   subject and the diff stat. The other commits were read.
2. The F\* `w3c_runner` and the Lean `l4w3c` on the same W3C manifests
   (fixtures: `third_party/testing/w3c`, the core-main checkout).
3. `tests/known-defects/run.sh`: every row compares the F\* CLI with the
   Lean CLI on one probe.
4. Binaries before the ports: `bin/linux-x86_64` of the core-main checkout
   (F\* `factoidal`, `w3c_runner`, `owl_runner` from the factoidal-builds
   release; `l4factoidal`, `l4w3c` built 2026-10-21 00:58). After the ports:
   the F\* binaries built in this branch by `build-ocaml.sh extract` and
   `compile`.

Limits of the method. A commit classed "speed only" from its subject and its
"proved equal" theorem was not run through a differential probe. Suites with
no F\* runner in this list (SHACL 1.2, SBM11, RML, GRDDL) were not run on
the F\* side.

## 2. Per-suite table (before the ports)

| Suite (manifest) | F\* | Lean | Both pass | Lean only | F\* only | Both fail |
|---|---|---|---|---|---|---|
| SPARQL 1.1 (`sparql11`, all manifests) | 665 pass, 0 fail, 3 local-override (out of 668) | 650 pass, 0 fail (out of 650) | all | 0 | 0 | 0 |
| SPARQL 1.2 (`sparql12/manifest.ttl`) | 255 pass, 16 fail (out of 271) | 271 pass, 0 fail (out of 271) | 255 | 16 | 0 | 0 |
| RDF 1.1 (six syntax suites and rdf-mt) | 1040 pass, 0 fail, 1 unsupported (out of 1041) | 1041 pass, 0 fail (out of 1041) | 1040 | 1 (rdf-mt, F\* reports unsupported) | 0 | 0 |
| RDF 1.2 syntax and eval (7 manifests) | 254 pass, 0 fail (out of 254) | see note | 254 | - | - | - |
| known-defects | 22 still present (XFAIL), 0 XPASS, 0 probe errors (out of 22) | - | - | - | - | - |

The SPARQL 1.1 denominators differ: the F\* runner counts the Protocol and
Graph Store manifests as 18 more tests (3 of them local overrides); both
trees pass every SPARQL 1.1 case each one runs. Note on RDF 1.2: the Lean
commit log reports rdf12 1358 pass, 0 fail (out of 1358) over a larger set of
manifests; the 254 cases the F\* runner reads all pass in F\*.

The 16 SPARQL 1.2 F\* failures are 12 `codepoint-escapes`, 3 `syntax`
(`group-by-scope-*`) and 1 `grouping` (`select-variable-reuse`). The W3C
fixtures for all 16 came with w3c/rdf-tests ec2ba15; the Lean tree changed
for them in commit fc9bc69a (2026-10-10), the F\* tree did not.

## 3. Inventory

Status: SAME (F\* already gives the same answer), DIFFERS (F\* gives a
different answer), LACKS (F\* has no such function), NONE (no F\*
counterpart; not ported). Conflict: the two trees give different answers on a
W3C test or a known-defects probe.

### 3.1 SPARQL

| Lean commit | Behaviour change | F\* module | Status | Conflict |
|---|---|---|---|---|
| fc9bc69a | SPARQL 1.2 section 19.2: escapes decoded per token, no whole-text pass; a surrogate escape in an IRI is an error | `SPARQL11.Parser` (`tokenize_12`, `process_iri_escapes_rec`) | DIFFERS, PORTED | yes, 12 W3C sparql12 tests |
| fc9bc69a | Section 11.4: a projection may use an earlier SELECT alias; section 18.2.4.4: AS target not in VS' (named GROUP BY variables at a grouping level) nor PV | `SPARQL11.Parser` (select body) | DIFFERS, PORTED | yes, 4 W3C sparql12 tests |
| fc9bc69a | Trailing VALUES scope, ASK/CONSTRUCT/DESCRIBE take a trailing VALUES | `SPARQL11.Parser` | SAME (F\* 435b939e) | no |
| (2026-10-13, issue 815) | OPTIONAL { P FILTER F }: F is the LeftJoin condition, section 18.2.2.5 | `SPARQL11.Parser` (Tok_OPTIONAL arm) | DIFFERS, PORTED | yes, known-defects SPARQL-OPT-FILTER-SCOPE |
| ee7c20da | CONSTRUCT output uses N-Triples blank node labels; `[ ]` in a collection is its own node (issues 740, 742, 747) | `SPARQL11.Parser`, CLI writer | DIFFERS | yes, known-defects 740 and 747 |
| 5a8b5add | Base IRI for query and update text; a relative IRI with no base is an error (issue 739) | CLI, `SPARQL11.Parser` | DIFFERS | yes, known-defects 739 |
| 2d11c256 | sameTerm reads the bound term; `=` on blank nodes is RDFterm-equal (issue 794) | `SPARQL11.Algebra` | SAME on the W3C suite; sameTerm on language tags DIFFERS (known-defects 324, older) | yes, known-defects 324 |
| 14534b03 | A typed literal in the query is compared by value (issue 784) | `SPARQL11.Algebra` | not probed | - |
| 0f55756d | Types derived from xsd:integer are numeric, section 17.1 (issue 782) | `SPARQL11.Algebra` | not probed | - |
| 53987041 | DESCRIBE returns the Concise Bounded Description (issue 698) | `SPARQL11.Algebra` | LACKS: the F\* DESCRIBE evaluator is a stub that returns no triples (`factoidal_cli.ml` names https://github.com/danbri/factoidal/issues/103) | no W3C test (DESCRIBE output is implementation-defined, SPARQL 1.1 section 16.4) |
| b716b954 | SPARQL string order (issue 724) | `SPARQL11.Algebra` | not probed | - |
| 3823aa3a | A failed SERVICE inside EXISTS fails the query (Federated Query section 2.3) | `SPARQL11.Algebra` | not probed (needs a SERVICE endpoint) | - |
| (issue 736) | IF with an error condition is an error; xsd:integer cast of "1.5" is an error | `SPARQL11.Algebra` | DIFFERS | yes, known-defects 736 (2 rows) |
| (issue 738) | FROM NAMED on the store backend | `SPARQL11.Store` | DIFFERS | yes, known-defects 738 |
| c62635b9 | text:query, geof:distance/envelope | - | NONE | no |
| adb44285, 749d1e04, 1d78681d, da40c9d8, 33b52078, 8acd213b | tokenizer, fuel caps, INSERT DATA, section 19.6 check, DISTINCT aggregates in linear time | `SPARQL11.Parser` | speed only, not ported | no |

### 3.2 RDF syntaxes, serializers, RDFC, JSON-LD

| Lean commit | Behaviour change | F\* module | Status | Conflict |
|---|---|---|---|---|
| 12132041 | RDF/XML: the scope of a property element (xml:lang) closes with it (issue 841; known-defects 329) | `Parser.RDFXML` | DIFFERS | yes, known-defects 329 |
| 6d91beb3 | JSON-LD toRdf: generated blank node labels cannot equal written ones (issue 840) | `JSONLD.Expand` / toRdf | DIFFERS | yes, known-defects 840 |
| accac951, 96b865e6 | serializers and readers carry RDF 1.2 triple terms (issue 870) | `RDF.Serialize.*` | not probed | - |
| 051d62ff | transparent triple-term literals; XML literal canonical form in isomorphism keys | `RDF.Graph.Iso` | not probed | - |
| 6607b7f5, 3e832dfe, 724fdd79, e98ec076 | Turtle writer and readers as loops (issue 725 for the writer) | `RDF.Serialize.Turtle` | speed and stack only; F\* Turtle writer overflows the stack at 40,000 paragraphs (known-defects 725) | yes, known-defects 725 (a resource defect, no different answer on a small input) |
| e12eebb0, cfcf5ae9, 00af942b, acb8e060, 4fa638ec | RDFC-1.0 speed (maps, merge sort, native string order) | `RDFC10.*` | speed only, not ported; tests/engine-compare RDFC 7 pass, 0 fail (out of 7) | no |
| be406cf8, 7397e9b9, 21206659 | JSON-LD fromRdf and node map speed | `JSONLD.*` | speed only, not ported | no |
| 9c9e50cc | JSON-LD 1.1 Framing algorithm | `JSONLD.Frame` | not compared | - |
| 9ee59cea to b31feaa0 | lenient parse (recovery mode) | - | NONE | no |

### 3.3 RDFS, OWL

| Lean commit | Behaviour change | F\* module | Status | Conflict |
|---|---|---|---|---|
| (issue 873, owner delegation 2026-10-19) | OWL 2 RL closure substitutes owl:sameAs inside triple terms | `OWL.Closure` | not probed in F\* (F\* has no RDF 1.2 triple terms in the OWL closure) | - |
| 3c1cdaa7 | RDF 1.2 Semantics axioms, rdfD1, rdfs14, rdfs14a | `RDF.Semantics` | LACKS for RDF 1.2 | no W3C F\* run |
| 4971f5ff | Graph merge (RDF 1.1 Semantics section 4) | `RDF.Graph.Merge` | SAME (Lean ported the F\* rows) | no |
| a1376a5b, d68756d7, f082d2ac, 9a012732 | OWL refuter: owl:onDataRange; <=-rule with data values and named individuals (issues 719, 720) | `Tableau_Refute` | DIFFERS | yes, known-defects 719, 720 (3 rows) |
| 50df19cd, 825299dd | OWL 2 RDF-Based Semantics regime | - | NONE | no |
| e73aafec, 7ff65d81 | RDFS closure indexed, semi-naive | `RDFS.*` | speed only, not ported | no |

### 3.4 SHACL, ShEx, CSVW, others

| Lean commit | Behaviour change | F\* module | Status | Conflict |
|---|---|---|---|---|
| 3ac5a609 to 520ad1e5 | SHACL 1.2 core and SPARQL (138 and 25 tests) | `SHACL.Validation` | LACKS (F\* is SHACL 1.1) | no (different suites) |
| 72342dd1 | SHACL-SPARQL: pre-binding row joined with WHERE | `SHACL.Validation` | not probed | - |
| ca9cea46 | RIF OWL-Direct imports; ShEx negative syntax | `RIF.*`, `ShEx.*` | not probed | - |
| 84c5254a | SHACL indexed data graph | `SHACL.Validation` | speed only, not ported | no |
| a81aba59, 9b008cb3 | CSVW test308 record | - | no behaviour change | no |

### 3.5 No F\* counterpart (not ported)

SBM11 and Shardborough (storage, update, DLOG, export, Merkle proofs), TDB2,
qlvr, the capability planner, LWS and Solid, `Dataset` handles in the wasm
ABI, RML (Core, IO, CC, star, FNML), lenient parsing, the Lean `serve`
command, XML 1.1 and the XML validity layer, OWL species check, GRDDL
transformations, VC data-model checks.

## 4. Ports made in this branch

Filled in as each port lands; see section 6.

## 5. Conflicts with two defensible readings

Filled in from the probes; see section 6.

## 6. Log

- 2026-10-21: record started; baseline measured (section 2).
