# SPARQL 1.2 RL (SPARQL-RL) test suite and draft: provenance

- Source: https://github.com/w3c/data-shapes, branch `gh-pages`, commit `fe4eed4`
  ("processing feedback", 2026-10-27).
- Copied: `shacl12-test-suite/tests/sparql-rl/` (manifests and fixtures) to
  `sparql-rl/tests/`; `sparql12-rl/index.html`, `sparql-rl-grammar.bnf` and
  `CHANGES.md` (the editor's draft, https://w3c.github.io/data-shapes/sparql12-rl/)
  to `sparql-rl/spec/`; `LICENSE.md`.
- Copied on 2026-10-27, for https://github.com/danbri/factoidal/issues/1099.
- Status: a W3C editor's draft of the Data Shapes Working Group. Expect changes.
  The draft has open items: the translation to SPARQL has no algorithm,
  `evalAggregate` is not finished, and some text is `@@`.
- The older copy of these tests, `shacl/shacl12-test-suite/tests/rules` (submodule
  `third_party/testing/shacl` at 08adb377, 2026-07-02), stays for
  `l4shacl-rules` until the new runner replaces it.
