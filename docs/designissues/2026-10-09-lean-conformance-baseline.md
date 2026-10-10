# Lean conformance baseline, 2026-10-09

Measured with `tools/lean-scoreboard.sh --resume --json .claude-runs/lean-scoreboard.json`
on factoidal-core `8d8fd8ad` (branch `claude/core-split`), Lean 4.33.1, every
runner run from the repository root against the vendored fixtures
(`tools/ensure-test-env.sh` exited 0). 53 runs. Full table with commands and
notes below, as the script printed it. Re-run the script; do not quote this
file after the tree moves.

Owner goal, 2026-10-09, verbatim: "Ensure all target specs have a complete
and tested lean4 implementation" and "/goal complete performant suite all in
lean4". Tracking: see the issue linked from the README of this record's
landing commit.

## Areas with failures or no runner (from the table)

| Area | Lean score | F\* engine (for comparison, `docs/test-results/latest.json` lineage) |
|---|---|---|
| RDF 1.2 rdf-semantics | 40 pass, 7 fail (out of 47) | 41 pass, 3 fail, 3 skip (out of 47) |
| OWL 2 EL profile, RL regime | 118 pass, 2 fail, 1 other (out of 121) | 119 pass, 1 fail (out of 120) |
| OWL 2 DL regime: type-inconsistency | 116 pass, 11 fail, 1 other (out of 128) | 126 pass, 1 fail (out of 127) |
| OWL 2 DL regime: type-positive-entailment, positive tests | 169 pass, 35 fail, 2 other (out of 206) | — |
| OWL 2 DL regime: syntax-dl positive / inconsistency | 73 pass, 15 fail (of 90); 92 pass, 11 fail (of 104) | — |
| OWL 2 syntax / DL species | no Lean runner | 319 pass, 2 fail, 2 skip (out of 323) |
| SHACL 1.2 core | 103 pass, 30 fail (out of 133) | 138 pass, 0 fail |
| SHACL 1.2 sparql | 22 pass, 3 fail (out of 25) | 25 pass, 0 fail |
| XSLT 1.0 | 84 pass, 3 fail, 1 refused (out of 88) | 87 pass, 0 fail, 1 skip (out of 88) |
| JSON-LD framing | 29 pass, 63 fail (out of 92) | runner exists, no published score |
| CSVW validation | 281 pass, 1 fail (out of 282) | 281 pass, 1 fail (out of 282) |
| XSD datatypes (instance tests) | 18951 pass, 5 fail (out of 18956) | — |
| RIF Core | 43 pass, 0 fail, 2 undecided, 1 local override (out of 46) | 46 pass, 0 fail, 4 skip (out of 50) |
| GRDDL | 19 pass, 22 fail, 27 other (out of 68) | 18 pass, 50 fail (out of 68) |
| RML Core | 60 pass, 0 fail, 16 not attempted (out of 76) | 76 pass, 0 fail (out of 76) |
| ShEx negative syntax (100 reject fixtures) | no Lean runner | in the 1182 |
| RML-IO, RML-FNML, RML-CC, RML-star | no Lean runner | RML-IO 17 pass, 1 fail, 55 skip (out of 73) |
| XForms | no Lean runner (build-time guards only) | 2 pass, 0 fail (out of 2) |
| Differential vs F\* (`l4diff`) | not run: needs `bin/linux-x86_64/factoidal` (install with `tools/fetch-builds.sh`) | — |

## Full table

```

Lean scoreboard, 2026-10-09T23:36:14Z, git 8d8fd8ad, 53 runs, 1142 s this invocation (runs reused with --resume are not timed again)

spec area                                                                                            | runner           |  pass | fail | skip/other | total | command
-----------------------------------------------------------------------------------------------------+------------------+-------+------+------------+-------+--------
SPARQL 1.1 (query+update+protocol, manifest-all)                                                     | l4w3c            |   631 |    0 |          0 |   631 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/sparql/sparql11/manifest-all.ttl
SPARQL 1.1 query syntax (parser only, no evaluation) [n1]                                            | l4sparql-probe   |   403 |    0 |          0 |   403 | formal/lean4/.lake/build/bin/l4sparql-probe third_party/testing/w3c/sparql/sparql11
SPARQL 1.2                                                                                           | l4w3c            |   254 |    0 |          0 |   254 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/sparql/sparql12/manifest.ttl
RDF 1.1 syntax: N-Triples                                                                            | l4w3c            |    70 |    0 |          0 |    70 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf11/manifest.ttl
RDF 1.1 syntax: N-Quads                                                                              | l4w3c            |    87 |    0 |          0 |    87 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf11/manifest.ttl
RDF 1.1 syntax: Turtle                                                                               | l4w3c            |   313 |    0 |          0 |   313 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf11/manifest.ttl
RDF 1.1 syntax: TriG                                                                                 | l4w3c            |   356 |    0 |          0 |   356 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf11/manifest.ttl
RDF 1.1 syntax: RDF/XML                                                                              | l4w3c            |   166 |    0 |          0 |   166 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf11/manifest.ttl
RDF 1.1 rdf-mt (semantics/entailment)                                                                | l4w3c            |    39 |    0 |          0 |    39 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf11/manifest.ttl
RDF 1.1 Turtle (file-name probe): parse-positive                                                     | l4turtle-probe   |   222 |    1 |          0 |   223 | formal/lean4/.lake/build/bin/l4turtle-probe third_party/testing/w3c/rdf/rdf11
RDF 1.1 Turtle (file-name probe): reject-negative                                                    | l4turtle-probe   |    94 |    0 |          0 |    94 | formal/lean4/.lake/build/bin/l4turtle-probe third_party/testing/w3c/rdf/rdf11
RDF 1.1 Turtle (file-name probe): eval-iso                                                           | l4turtle-probe   |   111 |    0 |          0 |   111 | formal/lean4/.lake/build/bin/l4turtle-probe third_party/testing/w3c/rdf/rdf11
RDF 1.1 TriG (file-name probe): parse-positive                                                       | l4turtle-probe   |   242 |    0 |          0 |   242 | formal/lean4/.lake/build/bin/l4turtle-probe third_party/testing/w3c/rdf/rdf11
RDF 1.1 TriG (file-name probe): reject-negative                                                      | l4turtle-probe   |   115 |    0 |          0 |   115 | formal/lean4/.lake/build/bin/l4turtle-probe third_party/testing/w3c/rdf/rdf11
RDF 1.1 TriG (file-name probe): eval-iso                                                             | l4turtle-probe   |   108 |    0 |          0 |   108 | formal/lean4/.lake/build/bin/l4turtle-probe third_party/testing/w3c/rdf/rdf11
RDF 1.1 RDF/XML (probe): parse-positive                                                              | l4rdfxml-probe   |   132 |    0 |          0 |   132 | formal/lean4/.lake/build/bin/l4rdfxml-probe third_party/testing/w3c/rdf/rdf11/rdf-xml
RDF 1.1 RDF/XML (probe): reject-negative                                                             | l4rdfxml-probe   |    41 |    0 |          0 |    41 | formal/lean4/.lake/build/bin/l4rdfxml-probe third_party/testing/w3c/rdf/rdf11/rdf-xml
RDF 1.1 RDF/XML (probe): eval-isomorphic                                                             | l4rdfxml-probe   |   132 |    0 |          0 |   132 | formal/lean4/.lake/build/bin/l4rdfxml-probe third_party/testing/w3c/rdf/rdf11/rdf-xml
RDF 1.2 syntax: N-Triples: syntax [n2]                                                               | l4w3c            |    29 |    0 |          0 |    29 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf12/manifest.ttl
RDF 1.2 syntax: N-Triples: c14n                                                                      | l4w3c            |    41 |    0 |          0 |    41 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf12/manifest.ttl
RDF 1.2 syntax: N-Quads: syntax                                                                      | l4w3c            |    27 |    0 |          0 |    27 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf12/manifest.ttl
RDF 1.2 syntax: N-Quads: c14n                                                                        | l4w3c            |    41 |    0 |          0 |    41 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf12/manifest.ttl
RDF 1.2 syntax: Turtle: syntax                                                                       | l4w3c            |    67 |    0 |          0 |    67 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf12/manifest.ttl
RDF 1.2 syntax: Turtle: eval                                                                         | l4w3c            |    29 |    0 |          0 |    29 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf12/manifest.ttl
RDF 1.2 syntax: TriG: syntax                                                                         | l4w3c            |    35 |    0 |          0 |    35 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf12/manifest.ttl
RDF 1.2 syntax: TriG: eval                                                                           | l4w3c            |    25 |    0 |          0 |    25 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf12/manifest.ttl
RDF 1.2 syntax: RDF/XML: eval                                                                        | l4w3c            |    30 |    0 |          0 |    30 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/w3c/rdf/rdf12/manifest.ttl
RDF 1.2 rdf-semantics (entailment)                                                                   | l4rdf-semantics  |    40 |    7 |          0 |    47 | formal/lean4/.lake/build/bin/l4rdf-semantics third_party/testing/w3c/rdf/rdf12/rdf-semantics/manifest.ttl
RDFC-1.0: manifest-driven                                                                            | l4w3c            |    86 |    0 |          0 |    86 | formal/lean4/.lake/build/bin/l4w3c --quiet third_party/testing/rdf-canon/tests/manifest.ttl
RDFC-1.0: probe: SHA-256 eval tests                                                                  | l4rdfc-probe     |    63 |    0 |          0 |    63 | formal/lean4/.lake/build/bin/l4rdfc-probe third_party/testing/rdf-canon/tests/rdfc10
RDFC-1.0: probe: SHA-384 eval tests                                                                  | l4rdfc-probe     |     1 |    0 |          0 |     1 | formal/lean4/.lake/build/bin/l4rdfc-probe third_party/testing/rdf-canon/tests/rdfc10
RDFC-1.0: probe: map tests                                                                           | l4rdfc-probe     |    21 |    0 |          0 |    21 | formal/lean4/.lake/build/bin/l4rdfc-probe third_party/testing/rdf-canon/tests/rdfc10
RDFC-1.0: probe: negative eval (excessive-calls abort)                                               | l4rdfc-probe     |     1 |    0 |          0 |     1 | formal/lean4/.lake/build/bin/l4rdfc-probe third_party/testing/rdf-canon/tests/rdfc10
OWL 2, RL closure regime: profile-RL.rdf PositiveEntailmentTest                                      | l4owl-probe      |    30 |    0 |          0 |    30 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: profile-RL.rdf NegativeEntailmentTest                                      | l4owl-probe      |     6 |    0 |          0 |     6 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: profile-RL.rdf ConsistencyTest                                             | l4owl-probe      |    76 |    0 |          0 |    76 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: profile-RL.rdf InconsistencyTest                                           | l4owl-probe      |    14 |    0 |          0 |    14 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: profile-RL.rdf                                                             | l4owl-probe      |   126 |    0 |          0 |   126 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: profile-EL.rdf PositiveEntailmentTest                                      | l4owl-probe      |    28 |    1 |          0 |    29 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: profile-EL.rdf NegativeEntailmentTest                                      | l4owl-probe      |     6 |    0 |          0 |     6 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: profile-EL.rdf ConsistencyTest                                             | l4owl-probe      |    72 |    0 |          0 |    72 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: profile-EL.rdf InconsistencyTest                                           | l4owl-probe      |    12 |    1 |          1 |    14 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: profile-EL.rdf                                                             | l4owl-probe      |   118 |    2 |          1 |   121 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: profile-QL.rdf PositiveEntailmentTest                                      | l4owl-probe      |    20 |    0 |          0 |    20 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: profile-QL.rdf NegativeEntailmentTest                                      | l4owl-probe      |     3 |    0 |          0 |     3 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: profile-QL.rdf ConsistencyTest                                             | l4owl-probe      |    58 |    0 |          0 |    58 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: profile-QL.rdf InconsistencyTest                                           | l4owl-probe      |     6 |    0 |          0 |     6 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: profile-QL.rdf                                                             | l4owl-probe      |    87 |    0 |          0 |    87 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: type-positive-entailment.rdf PositiveEntailmentTest                        | l4owl-probe      |   138 |   66 |          2 |   206 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: type-positive-entailment.rdf ConsistencyTest                               | l4owl-probe      |   204 |    0 |          2 |   206 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: type-positive-entailment.rdf                                               | l4owl-probe      |   342 |   66 |          4 |   412 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: type-inconsistency.rdf InconsistencyTest                                   | l4owl-probe      |    44 |   83 |          1 |   128 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: type-inconsistency.rdf                                                     | l4owl-probe      |    44 |   83 |          1 |   128 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: type-consistency.rdf PositiveEntailmentTest                                | l4owl-probe      |   138 |   66 |          2 |   206 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: type-consistency.rdf NegativeEntailmentTest                                | l4owl-probe      |    23 |    0 |          0 |    23 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: type-consistency.rdf ConsistencyTest                                       | l4owl-probe      |   351 |    1 |          2 |   354 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: type-consistency.rdf                                                       | l4owl-probe      |   512 |   67 |          4 |   583 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl
OWL 2, RL closure regime: type-negative-entailment.rdf NegativeEntailmentTest                        | l4owl-probe      |    23 |    0 |          0 |    23 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl type-negative-entailment.rdf syntax-dl.rdf semantics-direct.rdf
OWL 2, RL closure regime: type-negative-entailment.rdf ConsistencyTest                               | l4owl-probe      |    23 |    0 |          0 |    23 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl type-negative-entailment.rdf syntax-dl.rdf semantics-direct.rdf
OWL 2, RL closure regime: type-negative-entailment.rdf                                               | l4owl-probe      |    46 |    0 |          0 |    46 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl type-negative-entailment.rdf syntax-dl.rdf semantics-direct.rdf
OWL 2, RL closure regime: syntax-dl.rdf PositiveEntailmentTest                                       | l4owl-probe      |    52 |   36 |          2 |    90 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl type-negative-entailment.rdf syntax-dl.rdf semantics-direct.rdf
OWL 2, RL closure regime: syntax-dl.rdf NegativeEntailmentTest                                       | l4owl-probe      |    16 |    0 |          0 |    16 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl type-negative-entailment.rdf syntax-dl.rdf semantics-direct.rdf
OWL 2, RL closure regime: syntax-dl.rdf ConsistencyTest                                              | l4owl-probe      |   211 |    1 |          2 |   214 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl type-negative-entailment.rdf syntax-dl.rdf semantics-direct.rdf
OWL 2, RL closure regime: syntax-dl.rdf InconsistencyTest                                            | l4owl-probe      |    23 |   80 |          1 |   104 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl type-negative-entailment.rdf syntax-dl.rdf semantics-direct.rdf
OWL 2, RL closure regime: syntax-dl.rdf                                                              | l4owl-probe      |   302 |  117 |          5 |   424 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl type-negative-entailment.rdf syntax-dl.rdf semantics-direct.rdf
OWL 2, RL closure regime: semantics-direct.rdf PositiveEntailmentTest                                | l4owl-probe      |   138 |   66 |          2 |   206 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl type-negative-entailment.rdf syntax-dl.rdf semantics-direct.rdf
OWL 2, RL closure regime: semantics-direct.rdf NegativeEntailmentTest                                | l4owl-probe      |    23 |    0 |          0 |    23 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl type-negative-entailment.rdf syntax-dl.rdf semantics-direct.rdf
OWL 2, RL closure regime: semantics-direct.rdf ConsistencyTest                                       | l4owl-probe      |   350 |    1 |          2 |   353 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl type-negative-entailment.rdf syntax-dl.rdf semantics-direct.rdf
OWL 2, RL closure regime: semantics-direct.rdf InconsistencyTest                                     | l4owl-probe      |    44 |   83 |          1 |   128 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl type-negative-entailment.rdf syntax-dl.rdf semantics-direct.rdf
OWL 2, RL closure regime: semantics-direct.rdf                                                       | l4owl-probe      |   555 |  150 |          5 |   710 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl type-negative-entailment.rdf syntax-dl.rdf semantics-direct.rdf
OWL 2, DL regime (RL closure + tableau refuter): type-inconsistency.rdf InconsistencyTest            | l4owl-probe      |   116 |   11 |          1 |   128 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl --dl --refute-ms 3000 type-inconsistency.rdf
OWL 2, DL regime (RL closure + tableau refuter): type-positive-entailment.rdf PositiveEntailmentTest | l4owl-probe      |   169 |   35 |          2 |   206 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl --dl --refute-ms 3000 type-positive-entailment.rdf
OWL 2, DL regime (RL closure + tableau refuter): type-positive-entailment.rdf ConsistencyTest        | l4owl-probe      |   204 |    0 |          2 |   206 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl --dl --refute-ms 3000 type-positive-entailment.rdf
OWL 2, DL regime (RL closure + tableau refuter): type-consistency.rdf PositiveEntailmentTest         | l4owl-probe      |   169 |   35 |          2 |   206 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl --dl --refute-ms 3000 type-consistency.rdf
OWL 2, DL regime (RL closure + tableau refuter): type-consistency.rdf NegativeEntailmentTest         | l4owl-probe      |    23 |    0 |          0 |    23 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl --dl --refute-ms 3000 type-consistency.rdf
OWL 2, DL regime (RL closure + tableau refuter): type-consistency.rdf ConsistencyTest                | l4owl-probe      |   351 |    1 |          2 |   354 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl --dl --refute-ms 3000 type-consistency.rdf
OWL 2, DL regime (RL closure + tableau refuter): syntax-dl.rdf PositiveEntailmentTest                | l4owl-probe      |    73 |   15 |          2 |    90 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl --dl --refute-ms 3000 syntax-dl.rdf
OWL 2, DL regime (RL closure + tableau refuter): syntax-dl.rdf NegativeEntailmentTest                | l4owl-probe      |    16 |    0 |          0 |    16 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl --dl --refute-ms 3000 syntax-dl.rdf
OWL 2, DL regime (RL closure + tableau refuter): syntax-dl.rdf ConsistencyTest                       | l4owl-probe      |   211 |    1 |          2 |   214 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl --dl --refute-ms 3000 syntax-dl.rdf
OWL 2, DL regime (RL closure + tableau refuter): syntax-dl.rdf InconsistencyTest                     | l4owl-probe      |    92 |   11 |          1 |   104 | formal/lean4/.lake/build/bin/l4owl-probe --dir third_party/testing/owl --dl --refute-ms 3000 syntax-dl.rdf
SHACL Core (1.0 suite)                                                                               | l4shacl          |    98 |    0 |          0 |    98 | formal/lean4/.lake/build/bin/l4shacl third_party/testing/shacl/data-shapes-test-suite/tests/core/manifest.ttl
SHACL-SPARQL (1.0 suite)                                                                             | l4shacl          |    22 |    0 |          0 |    22 | formal/lean4/.lake/build/bin/l4shacl third_party/testing/shacl/data-shapes-test-suite/tests/sparql/manifest.ttl
SHACL 1.2 core                                                                                       | l4shacl          |   103 |   30 |          0 |   133 | formal/lean4/.lake/build/bin/l4shacl third_party/testing/shacl/shacl12-test-suite/tests/core/manifest.ttl
SHACL 1.2 sparql                                                                                     | l4shacl          |    22 |    3 |          0 |    25 | formal/lean4/.lake/build/bin/l4shacl third_party/testing/shacl/shacl12-test-suite/tests/sparql/manifest.ttl
SHACL 1.2 node expressions                                                                           | l4shacl-nodeexpr |   140 |    0 |          2 |   142 | formal/lean4/.lake/build/bin/l4shacl-nodeexpr
SHACL 1.2 rules                                                                                      | l4shacl-rules    |    88 |    0 |          0 |    88 | formal/lean4/.lake/build/bin/l4shacl-rules
ShEx (ShExJ validation suite)                                                                        | l4shex           |  1182 |    0 |          0 |  1182 | formal/lean4/.lake/build/bin/l4shex --verbose
ShEx (ShExC parser vs ShExJ twins)                                                                   | l4shexc          |   442 |    0 |          0 |   442 | formal/lean4/.lake/build/bin/l4shexc
RIF Core [n3]                                                                                        | l4rif            |    43 |    0 |          3 |    46 | formal/lean4/.lake/build/bin/l4rif
CSVW csv2rdf                                                                                         | l4csvw-rdf       |   270 |    0 |          0 |   270 | formal/lean4/.lake/build/bin/l4csvw-rdf
CSVW csv2json                                                                                        | l4csvw-json      |   270 |    0 |          0 |   270 | formal/lean4/.lake/build/bin/l4csvw-json
CSVW validation                                                                                      | l4csvw-validate  |   281 |    1 |          0 |   282 | formal/lean4/.lake/build/bin/l4csvw-validate
CSVW CSV reader: census [n4]                                                                         | l4csvw-probe     |     - |    - |        177 |   177 | formal/lean4/.lake/build/bin/l4csvw-probe
XML 1.0 conformance (xmlconf) [n5]                                                                   | l4xmlconf        |  1861 |    0 |        516 |  2377 | formal/lean4/.lake/build/bin/l4xmlconf
XML 1.0 conformance (xmlconf): census [n6]                                                           | xmlconf-probe    |     - |    - |       3078 |  3078 | find third_party/testing/xml/xmlconf -type f -name '*.xml' | LC_ALL=C sort | formal/lean4/.lake/build/bin/xmlconf-probe
XPath 1.0 (repo unit battery tests/unit/xpath_cases.json) [n7]                                       | l4xpath          |   100 |    0 |          0 |   100 | formal/lean4/.lake/build/bin/l4xpath
XSLT 1.0 [n8]                                                                                        | l4xslt           |    84 |    3 |          1 |    88 | formal/lean4/.lake/build/bin/l4xslt
Schematron                                                                                           | l4schematron     |     8 |    0 |          0 |     8 | formal/lean4/.lake/build/bin/l4schematron
MathML (Content)                                                                                     | l4mathml         |    81 |    0 |          0 |    81 | formal/lean4/.lake/build/bin/l4mathml
JSON Schema draft-07                                                                                 | l4jsonschema     |   770 |    0 |          0 |   770 | formal/lean4/.lake/build/bin/l4jsonschema
XSD datatypes (W3C XSD test suite, instance tests) [n9]                                              | l4xsd-datatypes  | 18951 |    5 |          0 | 18956 | formal/lean4/.lake/build/bin/l4xsd-datatypes --verbose
JSON-LD toRdf                                                                                        | l4jsonld-probe   |   467 |    0 |          0 |   467 | formal/lean4/.lake/build/bin/l4jsonld-probe
JSON-LD expand                                                                                       | l4jsonld-api     |   385 |    0 |          0 |   385 | formal/lean4/.lake/build/bin/l4jsonld-api
JSON-LD compact [n10]                                                                                | l4jsonld-api     |   245 |    0 |          1 |   246 | formal/lean4/.lake/build/bin/l4jsonld-api
JSON-LD flatten                                                                                      | l4jsonld-api     |    58 |    0 |          0 |    58 | formal/lean4/.lake/build/bin/l4jsonld-api
JSON-LD fromRdf [n11]                                                                                | l4jsonld-api     |    53 |    0 |          1 |    54 | formal/lean4/.lake/build/bin/l4jsonld-api
JSON-LD html                                                                                         | l4jsonld-api     |    50 |    0 |          0 |    50 | formal/lean4/.lake/build/bin/l4jsonld-api
JSON-LD framing                                                                                      | l4jsonld-frame   |    29 |   63 |          0 |    92 | formal/lean4/.lake/build/bin/l4jsonld-frame
RML Core [n12]                                                                                       | l4rml            |    60 |    0 |         16 |    76 | formal/lean4/.lake/build/bin/l4rml
VC / DID / Data Integrity: ed25519-rfc8032                                                           | l4vc-probe       |    22 |    0 |          0 |    22 | formal/lean4/.lake/build/bin/l4vc-probe
VC / DID / Data Integrity: did:key                                                                   | l4vc-probe       |     8 |    0 |          0 |     8 | formal/lean4/.lake/build/bin/l4vc-probe
VC / DID / Data Integrity: vc-dataintegrity-eddsa-rdfc-2022                                          | l4vc-probe       |     8 |    0 |          0 |     8 | formal/lean4/.lake/build/bin/l4vc-probe
VC / DID / Data Integrity: vc-di-eddsa-spec-vectors                                                  | l4vc-probe       |    20 |    0 |          0 |    20 | formal/lean4/.lake/build/bin/l4vc-probe
VC / DID / Data Integrity: sha256 differential                                                       | l4vc-probe       |    61 |    0 |          0 |    61 | formal/lean4/.lake/build/bin/l4vc-probe
JOSE / DPoP / Solid-OIDC: jose-rfc-fixtures                                                          | l4jose-probe     |    17 |    0 |          0 |    17 | formal/lean4/.lake/build/bin/l4jose-probe
JOSE / DPoP / Solid-OIDC: wycheproof-ecdsa-secp256r1-sha256-p1363                                    | l4jose-probe     |   262 |    0 |          0 |   262 | formal/lean4/.lake/build/bin/l4jose-probe
JOSE / DPoP / Solid-OIDC: wycheproof-rsa-2048-sha256                                                 | l4jose-probe     |   258 |    0 |          1 |   259 | formal/lean4/.lake/build/bin/l4jose-probe
JOSE / DPoP / Solid-OIDC: wycheproof-rsa-3072-sha256                                                 | l4jose-probe     |   258 |    0 |          1 |   259 | formal/lean4/.lake/build/bin/l4jose-probe
JOSE / DPoP / Solid-OIDC: wycheproof-rsa-4096-sha256                                                 | l4jose-probe     |   257 |    0 |          1 |   258 | formal/lean4/.lake/build/bin/l4jose-probe
JOSE / DPoP / Solid-OIDC: dpop-rfc9449                                                               | l4jose-probe     |    11 |    0 |          0 |    11 | formal/lean4/.lake/build/bin/l4jose-probe
JOSE / DPoP / Solid-OIDC: solid-oidc                                                                 | l4jose-probe     |    14 |    0 |          0 |    14 | formal/lean4/.lake/build/bin/l4jose-probe
Crypto primitives (RFC vectors, Wycheproof): rfc8439                                                 | l4crypto-probe   |    13 |    0 |          0 |    13 | formal/lean4/.lake/build/bin/l4crypto-probe
Crypto primitives (RFC vectors, Wycheproof): wycheproof-chacha20-poly1305                            | l4crypto-probe   |   837 |    0 |          0 |   837 | formal/lean4/.lake/build/bin/l4crypto-probe
Crypto primitives (RFC vectors, Wycheproof): hmac-hkdf-differential                                  | l4crypto-probe   |    25 |    0 |          0 |    25 | formal/lean4/.lake/build/bin/l4crypto-probe
Crypto primitives (RFC vectors, Wycheproof): wycheproof-hkdf-sha256                                  | l4crypto-probe   |   172 |    0 |          0 |   172 | formal/lean4/.lake/build/bin/l4crypto-probe
Crypto primitives (RFC vectors, Wycheproof): wycheproof-x25519                                       | l4crypto-probe   |   299 |    0 |        254 |   553 | formal/lean4/.lake/build/bin/l4crypto-probe
Crypto primitives (RFC vectors, Wycheproof): rfc9180-a2                                              | l4crypto-probe   |    15 |    0 |          0 |    15 | formal/lean4/.lake/build/bin/l4crypto-probe
Crypto primitives (RFC vectors, Wycheproof): aes-gcm                                                 | l4crypto-probe   |     0 |    0 |        316 |   316 | formal/lean4/.lake/build/bin/l4crypto-probe
GeoSPARQL (v0 unit pin; not the OGC suite) [n13]                                                     | l4geo            |    37 |    0 |          0 |    37 | formal/lean4/.lake/build/bin/l4geo
GRDDL [n14]                                                                                          | l4grddl          |    19 |   22 |         27 |    68 | formal/lean4/.lake/build/bin/l4grddl
HDT container                                                                                        | l4hdt            |     2 |    0 |          0 |     2 | formal/lean4/.lake/build/bin/l4hdt
LWS 1.0 core: guarded checks (executed)                                                              | l4lws-probe      |     9 |    0 |          0 |     9 | formal/lean4/.lake/build/bin/l4lws-probe
LWS 1.0 core: requirement rows [n15]                                                                 | l4lws-probe      |    11 |    0 |          7 |    18 | formal/lean4/.lake/build/bin/l4lws-probe
Solid Protocol + WAC: guarded checks (executed)                                                      | l4solid-probe    |    64 |    0 |          0 |    64 | formal/lean4/.lake/build/bin/l4solid-probe
Solid Protocol + WAC: requirement rows [n16]                                                         | l4solid-probe    |    70 |    0 |          7 |    77 | formal/lean4/.lake/build/bin/l4solid-probe
Think-of-a-Number parity battery (Math + MathML) [n17]                                               | l4toan           |   114 |    0 |          0 |   114 | formal/lean4/.lake/build/bin/l4toan
Property-based invariants (generated cases) [n18]                                                    | l4prop           |  9000 |    0 |          0 |  9000 | formal/lean4/.lake/build/bin/l4prop
RDFS closure, semi-naive vs naive (equivalence) [n19]                                                | l4rdfs-semi      |     6 |    0 |          0 |     6 | formal/lean4/.lake/build/bin/l4rdfs-semi
Differential vs F* engine (SPARQL 1.1 manifest-all) [n20]                                            | l4diff           | ERROR |    - |          - |     - | formal/lean4/.lake/build/bin/l4diff --fstar bin/linux-x86_64/factoidal third_party/testing/w3c/sparql/sparql11/manifest-all.ttl
XForms (Bind, recalculate) [n21]                                                                     | none             |  none |    - |          - |     - |
ShEx negative syntax (100 ShExC reject fixtures) [n22]                                               | none             |  none |    - |          - |     - |
RML-IO, RML-FNML, RML-CC, RML-star test cases [n23]                                                  | none             |  none |    - |          - |     - |
EECC interop (vc-verifier-rules, webuild-attestations) [n24]                                         | none             |  none |    - |          - |     - |
QUDT [n25]                                                                                           | none             |  none |    - |          - |     - |

Notes:
[n1] SPARQL 1.1 query syntax (parser only, no evaluation): 12 query files in no manifest are not scored; 55 update files are out of scope for this probe
[n2] RDF 1.2 syntax: N-Triples: syntax: ! exit code 1, but no row of this run shows a failure; the log has failures in a suite this run does not report (see the log)
[n3] RIF Core: total derived: decided 43 + undecided 2 + not read 0 + local override 1; the runner prints no total
[n4] CSVW CSV reader: census: NOT a conformance score: 177 CSV files read (170 uniform width, 7 ragged), 0 failed to read; the probe does not compare with the expected output
[n5] XML 1.0 conformance (xmlconf): total derived: scored 1861 (the runner's 'out of 1861 in profile') + 516 out-of-profile cases the runner reports but does not score
[n6] XML 1.0 conformance (xmlconf): census: NOT a conformance score: 1904 files accepted as well-formed, 1174 rejected (no expected verdict is read; l4xmlconf is the scored row)
[n7] XPath 1.0 (repo unit battery tests/unit/xpath_cases.json): repository unit battery, not a W3C suite
[n8] XSLT 1.0: pass includes whitespace-only differences; other = refused (1) + not UTF-8 (0) + unreadable (0)
[n9] XSD datatypes (W3C XSD test suite, instance tests): total = scored instance tests only; not scored: structures 7053, mixed 0, schema-invalid 1, version-1.0 8, unreadable 138, not-simple 8, assertion 32, unreadable-pattern 105, nilled 3, value-constraint 53
[n10] JSON-LD compact: other = local-override + unsupported
[n11] JSON-LD fromRdf: other = local-override + unsupported
[n12] RML Core: total derived; other = comparison gave up (0) + not read (1) + negative cases the runner does not attempt (15)
[n13] GeoSPARQL (v0 unit pin; not the OGC suite): unit pin twin of the F* test, not the OGC GeoSPARQL suite
[n14] GRDDL: other = no transformation found (10) + document not in the vendored docroot (17) + refused (0)
[n15] LWS 1.0 core: requirement rows: pass = rows backed by a proof (2), a guarded check (9) or a host test (0); other = 7 open rows with no check
[n16] Solid Protocol + WAC: requirement rows: pass = rows backed by a proof (3), a guarded check (64) or a host test (3); other = 7 open rows with no check
[n17] Think-of-a-Number parity battery (Math + MathML): parity battery, not a W3C suite
[n18] Property-based invariants (generated cases): sum over 18 properties, 500 generated cases each; generated, not a W3C suite
[n19] RDFS closure, semi-naive vs naive (equivalence): pass = semi-naive closure equals the naive closure; an equivalence check, not a W3C suite
[n20] Differential vs F* engine (SPARQL 1.1 manifest-all): measured nothing: F* binary not found: bin/linux-x86_64/factoidal (pass --fstar PATH; run from the repository root)
[n21] XForms (Bind, recalculate): no Lean runner: Lean library L4Factoidal/XForms/Bind.lean has build-time #guard checks only; no Harness runner
[n22] ShEx negative syntax (100 ShExC reject fixtures): no Lean runner: l4shexc compares ShExC with ShExJ twins only; the reject fixtures are not read
[n23] RML-IO, RML-FNML, RML-CC, RML-star test cases: no Lean runner: l4rml reads rml-core test-cases only
[n24] EECC interop (vc-verifier-rules, webuild-attestations): no Lean runner: no Lean module or runner
[n25] QUDT: no Lean runner: no Lean module or runner

Rows with numbers: 136 (of which 34 have failures). Rows that are ERROR, TIMEOUT or UNPARSED: 1. JSON: .claude-runs/lean-scoreboard.json. Logs: .claude-runs/lean-scoreboard/

First 10 failing test ids, from the saved logs:
  l4turtle-probe: 1 failing ids listed in the log
    test-38.ttl
  l4rdf-semantics: 7 failing ids listed in the log
    literal-type
    malformed-literal-no-spurious
    malformed-literal-bnode-neg
    annotation
    annotation-unfolded
    triple-terms-propositions
    reifies-range
  l4owl-probe-rl: 218 failing ids listed in the log
    New-Feature-Keys-002 [InconsistencyTest]
    WebOnt-someValuesFrom-003 [PositiveEntailmentTest]
    Consistent-but-all-unsat [PositiveEntailmentTest]
    New-Feature-DataQCR-001 [PositiveEntailmentTest]
    New-Feature-DisjointUnion-001 [PositiveEntailmentTest]
    New-Feature-ObjectQCR-001 [PositiveEntailmentTest]
    rdfbased-sem-restrict-maxqcr-inst-obj-one [PositiveEntailmentTest]
    WebOnt-AllDifferent-001 [PositiveEntailmentTest]
    WebOnt-AnnotationProperty-002 [PositiveEntailmentTest]
    WebOnt-Class-001 [PositiveEntailmentTest]
  l4owl-probe-rl-extra: 267 failing ids listed in the log
    Consistent-but-all-unsat [PositiveEntailmentTest]
    Contradicting datatype Restrictions [InconsistencyTest]
    Contradicting-dateTime-restrictions [InconsistencyTest]
    Datatype-Float-Discrete-001 [InconsistencyTest]
    datatype-restriction-min-max-inconsistency [InconsistencyTest]
    Different types in Datatype Restrictions and Complement [InconsistencyTest]
    FS2RDF-literals-ar [ConsistencyTest]
    Inconsistent Byte Filler [InconsistencyTest]
    Inconsistent Data Complement with the Restrictions [InconsistencyTest]
    Inconsistent Disjoint Dataproperties [InconsistencyTest]
  l4owl-probe-dl-inconsistency: 11 failing ids listed in the log
    Inconsistent Disjoint Dataproperties [InconsistencyTest]
    Inconsistent String Pattern with Disjoint Dataproperties [InconsistencyTest]
    Minus Infinity is not in owl:real [InconsistencyTest]
    one=two [InconsistencyTest]
    WebOnt-description-logic-035 [InconsistencyTest]
    WebOnt-description-logic-040 [InconsistencyTest]
    WebOnt-description-logic-108 [InconsistencyTest]
    WebOnt-description-logic-502 [InconsistencyTest]
    WebOnt-description-logic-504 [InconsistencyTest]
    WebOnt-description-logic-909 [InconsistencyTest]
  l4owl-probe-dl-positive-entailment: 35 failing ids listed in the log
    Consistent-but-all-unsat [PositiveEntailmentTest]
    New-Feature-DisjointUnion-001 [PositiveEntailmentTest]
    WebOnt-AnnotationProperty-002 [PositiveEntailmentTest]
    WebOnt-Class-001 [PositiveEntailmentTest]
    WebOnt-Class-003 [PositiveEntailmentTest]
    WebOnt-FunctionalProperty-004 [PositiveEntailmentTest]
    WebOnt-I5.24-002 [PositiveEntailmentTest]
    WebOnt-I5.24-003 [PositiveEntailmentTest]
    WebOnt-I5.24-004 [PositiveEntailmentTest]
    WebOnt-I5.3-014 [PositiveEntailmentTest]
  l4owl-probe-dl-consistency: 36 failing ids listed in the log
    Consistent-but-all-unsat [PositiveEntailmentTest]
    FS2RDF-literals-ar [ConsistencyTest]
    New-Feature-DisjointUnion-001 [PositiveEntailmentTest]
    WebOnt-AnnotationProperty-002 [PositiveEntailmentTest]
    WebOnt-Class-001 [PositiveEntailmentTest]
    WebOnt-Class-003 [PositiveEntailmentTest]
    WebOnt-FunctionalProperty-004 [PositiveEntailmentTest]
    WebOnt-I5.24-002 [PositiveEntailmentTest]
    WebOnt-I5.24-003 [PositiveEntailmentTest]
    WebOnt-I5.24-004 [PositiveEntailmentTest]
  l4owl-probe-dl-syntax: 27 failing ids listed in the log
    Consistent-but-all-unsat [PositiveEntailmentTest]
    FS2RDF-literals-ar [ConsistencyTest]
    Inconsistent Disjoint Dataproperties [InconsistencyTest]
    Inconsistent String Pattern with Disjoint Dataproperties [InconsistencyTest]
    Minus Infinity is not in owl:real [InconsistencyTest]
    New-Feature-DisjointUnion-001 [PositiveEntailmentTest]
    one=two [InconsistencyTest]
    WebOnt-AnnotationProperty-002 [PositiveEntailmentTest]
    WebOnt-I5.24-003 [PositiveEntailmentTest]
    WebOnt-I5.24-004 [PositiveEntailmentTest]
  l4shacl-core12: 30 failing ids listed in the log
    Test of sh:severity sh:Debug 004
    Test of sh:severity sh:Trace 005
    Test of sh:closed at node shape 003
    Test of sh:closed at node shape 004
    Test of sh:datatype at node shape 003
    Test of sh:maxListLength on node shape 001
    Test of sh:memberShape on node shape 001
    Test of sh:minListLength on node shape 001
    Test of sh:nodeByExpression at node shape 001
    Test of sh:nodeKind at node shape 002
  l4shacl-sparql12: 3 failing ids listed in the log
    Test of a sh:property with a sh:sparqlExpr expression 001
    Test of a sh:property with a sh:select expression 001
    Test of sh:targetNode with a sh:select expression 001
  l4csvw-validate: 1 failing ids listed in the log
    FAIL manifest-validation#test308
  l4xslt: 3 failing ids listed in the log
    copy/copy-3102
    namespace/namespace-4801
    node/node-1601
  l4xsd-datatypes: 5 failing ids listed in the log
    targetNS00101m1_p
    Negative
    ST_name00101m1_n
    simple053.n01.xml
    vc_003_2
  l4jsonld-frame: 63 failing ids listed in the log
    #t0005
    #t0008
    #t0009
    #t0010
    #t0011
    #t0012
    #t0013
    #t0016
    #t0018
    #t0022
  l4grddl: 22 failing ids listed in the log
    grddlProfileBase1
    four-transforms
    htmlbase4
    three-transforms
    xmlbase4
    title_author
    multipleRepresentations3
    multipleRepresentations2
    langconneg3
    langconneg1
```

## Re-measurement 2026-10-10 and two totals that changed

CI run 18 of danbri/factoidal-builds (core dba1bdb1) ran the scoreboard. Its
output is the `lean-scoreboard.txt` asset of the release
`build-dba1bdb1d320-web`:
https://github.com/danbri/factoidal-builds/releases/tag/build-dba1bdb1d320-web

Two totals changed between this record and that run. Both changes come from
the test suite, not from the runners:

- RDF 1.2 rdf-semantics: 47 cases here, 29 in run 18 (29 pass, 0 fail).
- RDF 1.1 syntaxes plus rdf-mt: 1031 here, 1041 in run 18.

Cause: this record was measured with `third_party/testing/w3c` at 35c503a6
(the pin in danbri/factoidal). factoidal-core pins ec2ba15. Between the two,
upstream rdf-tests made 13 commits to `rdf/rdf12/rdf-semantics`. Among
them: "moving some tests from rdf12 to rdf11", "remove all "control" tests",
"removing three tests involving ill-typed literals", "do not include
#opaque-iri test", "fix tests #annotation and #annotation-unfolded". The
manifest went from 47 `mf:name` entries to 29. Check:
`git -C third_party/testing/w3c diff --stat 35c503a6 ec2ba15 -- rdf/rdf12/rdf-semantics`
(30 files changed, 2058 lines deleted).

## GRDDL, re-measured 2026-10-10 (language content negotiation)

The GRDDL rows above (19 pass, 22 fail, 27 other, out of 68) are the
2026-10-09 record. Current `l4grddl` (`lake build l4grddl`, run from the
repository root): 47 pass, 2 fail (out of 49 decided); 0 no transformation;
5 unavailable; 0 refused; 3 related test passed; 11 local override (out of
68). Issue: https://github.com/danbri/factoidal/issues/668.

What changed for the language cases. `td/conneg.html` is a resource that the
W3C server negotiates over language. The test cases `langconneg1`,
`langconneg2` and `langconneg3` need different representations of it
(GRDDL Test Cases, "Content Negotiation with GRDDL": English; German; "may
retrieve both representations ... This GRDDL result is the merge of the
previous two"). Before: only the English one was vendored, so `langconneg2`
produced the English title and `langconneg3` produced one of its two
triples (2 fail). Now:

- The German representation is vendored as `docroot/td/conneg.html.de`. The
  English representation from the server is byte-identical to the vendored
  `docroot/td/conneg.html`. Provenance: `third_party/testing/grddl/PROVENANCE.md`.
- `docroot/variants.tsv` records the representations as data (resource IRI,
  `Content-Language`, file). The first row is the server's default variant.
- `Harness/GrddlRun.lean` gives `GRDDL.Agent.glean` a retrieval function
  that takes the agent's language range. It chooses by RFC 4647 section 3.4
  (Lookup) and, with no match, answers the default variant (RFC 9110 section
  12.5.4 allows this). The server behaves the same way (measured 2026-10-10,
  table in PROVENANCE.md). `GRDDL/Agent.lean` is unchanged: retrieval is a
  parameter, and `GRDDL/AgentTests.lean` now pins that.
- The language of each case is a table in `Harness/GrddlRun.lean`, because
  the manifest does not carry it: `langconneg2` asks for `de`; `langconneg3`
  retrieves every variant and merges the results (GRDDL section 2, blank
  nodes renamed apart); every other case asks for `en`.

Cause of each remaining failure. Both produce the expected graph except
for the scheme of the subject. `glean_title.xsl` takes the subject from the
`<link rel="alternate">` of the document. Both representations carry
`https://musicbrainz.org/...`; the expected files use `http://musicbrainz.org/...`.
The produced graphs (`GRDDL_DEBUG=conneg.html`):

| Case | Produced | Expected |
|---|---|---|
| `langconneg2` | `<https://musicbrainz.org/mm-2.1/album/6b050dcf-7ab1-456d-9e1b-c3c41c18eed2> dc:title "Hast Du Erfahrung? "` | the same triple with `http://musicbrainz.org/...` |
| `langconneg3` | the same subject (https) with `dc:title "Are You Experienced?"` and `dc:title "Hast Du Erfahrung? "` | the same two triples with `http://musicbrainz.org/...` |

The runner counts both in "of those failures, 2 differ ONLY by the
http/https scheme" (before: 0). This is the same post-2007 edit of a W3C
document as the 7 cases of https://github.com/danbri/factoidal/issues/730.
`langconneg1` is one of those 7 already (a local override). Whether
`langconneg2` and `langconneg3` join them was a decision for the owner. Owner,
2026-10-10, verbatim: "730 - do langconneg2 and langconneg3 join h - yes".
They are local overrides since then (`tests/local-overrides/grddl__langconneg2.json`,
`grddl__langconneg3.json`); the vendored representations are not edited.
`l4grddl` after that: 47 pass, 0 fail (out of 47 decided); 5 unavailable;
3 related test passed; 13 local override (out of 68).

The other buckets are unchanged: the 5 unavailable cases need server-side
stylesheets (`*.sxsl?...`, `layering-namespace?`, `layering-profile?`) that
now answer 303 to a W3C login; the 3 related-test cases pass by
`g:alternative` or `g:subsumes` (counted apart); the 13 local overrides are
the 7 edited networked inputs, the 4 `loopx` cases and the 2 language cases
of issue 730.
