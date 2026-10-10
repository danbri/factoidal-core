# Binding-site regression fixture

This checkout carries only `data/binding_site.ttl`: 368 triples from the
Wikidata life-sciences KGX export. The source repository records a public
pipeline download on 2026-04-20 and re-serialization to Turtle, with no other
changes. Wikidata data is CC0.

The file is copied unchanged from `danbri/factoidal` commit
`e505f643297922f195e940eb432d4f3ddf2c2a63`. Native persisted-store smoke tests
and `tools/blockengine-core-baseline.py` use this fixture. It is small test
data, not evidence of large-database performance.
