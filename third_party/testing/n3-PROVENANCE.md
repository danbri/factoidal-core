# Notation3 (N3): specifications and test suite, provenance

- Source: https://github.com/w3c/N3 (the W3C Notation 3 Community Group
  repository), branch `master`, commit
  `1d29dea774d3e5a97883ebbc8ab033a176ac11b5` ("Merge pull request #233 from
  eljeffeg/codex/current-spec-test-status", 2026-08-23).
- Vendored as the git submodule `third_party/testing/n3`, pinned at that commit
  (the whole repository: specifications, grammar, tests).
- Added on 2026-10-28, for https://github.com/danbri/factoidal/issues/1165
  (spec coverage, N3 section) and https://github.com/danbri/factoidal/issues/1171
  (N3 workstream).

## Specification versions

None of these is a W3C Standard or on the Standards Track. The Language and
Semantics documents are Community Group drafts (`specStatus: "CG-DRAFT"`); the
Builtin Functions document at the pinned commit calls itself "Final Community
Group Report, 3 June 2026".

| Document | File at the pinned commit | Last change to the file |
|---|---|---|
| Notation3 Language (editor's draft) | `spec/index.html` | `b975fc59`, 2026-07-13 |
| Notation3 Semantics (editor's draft) | `spec/semantics.html` | `97653d42`, 2026-07-03 |
| Notation3 Builtin Functions (Final Community Group Report, 3 June 2026) | `spec/builtins.html` | `23ccf3d5`, 2026-06-03 |
| Notation3 Language, dated report | `reports/20230703/index.html` | report of 2023-07-03 |
| N3 grammar, EBNF | `reports/20230703/n3.ebnf` (from `grammar/n3.g4`) | report of 2023-07-03 |

The Lean code names these as "Notation3 Language § ...", "Notation3 Semantics §
...", "Notation3 Builtin Functions § ...", meaning the editor's drafts at the
pinned commit, and grammar production numbers `[1]`-`[36]` of
`reports/20230703/n3.ebnf` (the same productions as `grammar/n3.g4` at the
pinned commit).

## Test suite

`tests/` at the pinned commit:

| Manifest | Entries | Test types |
|---|---|---|
| `tests/N3Tests/manifest-parser.ttl` | 224 | `test:TestN3PositiveSyntax`, `test:TestN3NegativeSyntax`, `test:TestN3Eval` |
| `tests/N3Tests/manifest-extended.ttl` | 978 | `test:TestN3PositiveSyntax`, `test:TestN3NegativeSyntax` |
| `tests/N3Tests/manifest-reasoner.ttl` | 89 | `test:TestN3Reason` |
| `tests/TurtleTests/manifest.ttl` | 296 | the RDF 1.1 Turtle types (`rdft:TestTurtle*`) |

`rdft:Rejected` entries (for example the `@forAll`/`@forSome` cases, which the
current Language draft removed) are "non-conformance compatibility tests and
should be reported separately" (`tests/README.md`); `lake exe l4n3` counts them
in their own score line.

## Licence

`tests/LICENSE.md`: the W3C Test Suite License and the W3C Software and
Document License.
