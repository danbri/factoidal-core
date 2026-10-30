# FOAF data adapter

`FoafGraph.lean` reads Turtle through the current Factoidal
`L4Factoidal.Syntax.Turtle.parseTurtle` in RDF 1.1 mode. It returns a small
typed graph for a native renderer. It does not draw, fetch linked documents,
run inference, or implement a browser.

```lean
import FoafGraph
-- Caller supplies text and, optionally, its retrieval IRI.
-- FoafGraph.fromTurtle text (some "https://example.org/people.ttl")
--   : Except String FoafGraph.Data
-- FoafGraph.Data.fromJson data.toJson = .ok data for adapter-produced data
```

The view contains subjects explicitly typed with the exact FOAF Person IRI
and both resource endpoints of the exact FOAF knows predicate. Name-only
subjects and lookalike predicates do not add nodes. This view choice does
not assert that the knows endpoints have an RDF type triple. Links stay
directed, self links remain, and repeated triples or links add no weight.
Literal knows objects are excluded and counted in `ignoredKnows`, once per
distinct invalid triple.

Each `Person` keeps the actual Factoidal `RDF.Subject`, a constructor-prefixed
`id`, and a display `label`. IRI and blank-node identities stay distinct.
Labels prefer the lexically least `foaf:name` literal, then the lexically
least `rdfs:label` literal, then the full IRI or `_:` plus the blank-node ID.
`labelIsFallback` records whether the adapter generated this label. A literal
equal to its subject's full IRI remains an explicit label, not a fallback.
The adapter has no language preference and does not merge equal labels.
People sort by identity, and links sort by their endpoint indices. Thus
permuting named/explicit-blank-node triples or repeating them preserves the
view. Anonymous parser allocation can depend on statement order. These are
document-scoped blank-node identities, not canonical RDF labels. Do not
merge independently parsed documents by these IDs without first using
Factoidal's blank-node renaming operations.

`Data.toJson` and `Data.fromJson` use the existing Factoidal JSON tree.
`Data.encode` and `Data.decode` provide compact text with Factoidal escaping
and parsing, including Unicode and control characters. The schema is:

```json
{"people":[{"kind":"iri","value":"https://example.org/alice","id":"iri:https://example.org/alice","label":"Alice","labelIsFallback":false}],"links":[{"source":0,"target":0}],"ignoredKnows":0}
```

The decoder rejects unknown, duplicate, or missing fields; repeated
identities or links; mismatched constructor/ID values; invalid kinds;
non-natural endpoints; out-of-range endpoints; nonboolean provenance; and
fallback labels inconsistent with their subject. Its IRI validation uses
the existing `RDF.Core.isIri` gate, not a new full IRI validator. It accepts
valid graph order as supplied, without renumbering links or claiming RDF
provenance for arbitrary JSON.

Default limits are 65,536 Turtle characters before parsing, 256 people,
1,024 directed links, 4,096 characters per identity/label, and 2,097,152
JSON characters before parsing. Natural JSON fields have at most ten
decimal digits. Post-parse graph limits do not bound Turtle parser work or
nesting depth; `fromGraph` also has no input-triple count limit.

The small current-source closure is:

```text
L4Factoidal.RDF.XmlCanon
L4Factoidal.RDF.Core
L4Factoidal.RDF.Graph
L4Factoidal.Encoding.Hex
L4Factoidal.Syntax.Lexing
L4Factoidal.Syntax.NTriples
L4Factoidal.Syntax.IriResolve
L4Factoidal.RDF.IriSyntax
L4Factoidal.NatBounds
L4Factoidal.Syntax.Turtle
L4Factoidal.JSON.Value
L4Factoidal.JSON.Parser
L4Factoidal.JSON.Serialize
```

`test.sh` compiles only this closure and the adapter into ignored local
`.build/` files, then runs native Lean tests. It does not build the full
corpus or runtime and does not modify the existing demo engines. Run it
from the repository root:

```sh
bash labs/demos/foafnaut/foaf/test.sh
```

When another worker shares the Lean build slot, set `FOAFNAUT_BUILD_LOCK`
to the agreed lock directory. The script uses `formal/lean4` as its Lean
working directory. The fixtures are locally authored synthetic data.
`fixtures/demo.ttl` has readable ASCII names for the UI; `fixtures/people.ttl`
retains Unicode and escaping regressions. Tests
cover fixture counts, base resolution, exact vocabulary, RDF identity,
label priority, directed/self/duplicate edges, limits, invalid Turtle,
and checked JSON Unicode/control-character round trips. These local tests
are not W3C RDF conformance suite results. WASM and native UI integration
are separate work; this adapter alone makes no rendering claim.
