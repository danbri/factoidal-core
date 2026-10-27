# json-ld-star test suite: provenance

- Source: https://github.com/json-ld/json-ld-star, branch `1.2-tests`,
  commit `6142c6ff` ("Adds/updates annotations on triple terms.", 2025-05-19).
- That branch is the head of https://github.com/json-ld/json-ld-star/pull/61
  (updated tests for RDF 1.2 triple terms and reifiers, by Gregg Kellogg; open).
  The pull request has no specification text. Its algorithm changes are in the
  pull request comment of 2025-05-19, copied into
  `docs/designissues/2026-10-26-jsonld-star.md`.
- Copied: `tests/` (manifests and fixtures) and `LICENSE.md`. Not copied: the
  generated HTML manifests, `Rakefile`, `template.haml`.
- Copied on 2026-10-26. Status: a Community Group draft. JSON-LD WG plans to move
  these tests to w3c/json-ld-api as JSON-LD 1.3 tests
  (https://github.com/json-ld/json-ld-star/pull/61#issuecomment, niklasl, 2026-09-16).
  Expect the syntax to change (`@quote` proposal in
  https://github.com/json-ld/json-ld-star/issues/49).
