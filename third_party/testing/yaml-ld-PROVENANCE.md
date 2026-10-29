# YAML-LD test suite: provenance

- Source: https://github.com/json-ld/yaml-ld, branch `main`, commit
  `fafcf7ae69d5e5cb7402e71dfd5cd2c03c18f29f` ("[#254]: Add shared blank node
  RDF result", 2026-10-24).
- Copied: `tests/` (manifest `manifest.jsonld`, `context.jsonld`, `README.md`,
  `LICENSE.md` and `cases/`) and the repository `LICENSE.md`, into
  `third_party/testing/yaml-ld/`. Not copied: the generated `tests/manifest.html`
  and its generator `tests/generate_index.js`.
- Copied on 2026-10-29.
- Specification: YAML-LD 1.0, Editor's Draft of the W3C JSON-LD Working Group
  (`index.html` of the same commit, `specStatus: "ED"`, `shortName: "yaml-ld-10"`).
  The last snapshot in the repository is `publication-snapshots/WD-yaml-ld-10-20260305`.
  Expect changes.
- Licence: the test suite is under the W3C test suite dual licence
  (https://www.w3.org/Consortium/Legal/2008/04-testsuite-copyright.html); the
  other documents under the W3C Software and Document License.
- Runner: `formal/lean4/Harness/YamlLdRun.lean` (`lake exe l4yamlld`), wrapper
  `tests/yamlld/run.sh`.
