# MLP query explainer (deterministic)

Rule-based explanations of the 580 Martin Poulter Wikidata queries in
`data/mlp-all-queries.json` (or `$MLP_CORPUS`). It explains the Factoidal rewrite
(`lean_replacement_query`). No LLM is involved. Design: `SPEC.md`.
Parser requirements: `PARSE-API-NEEDS.md`.

## Status (2026-11-24)

- **Parser:** INTERIM. ASTs come from a local dump made with factoidal's
  own Lean parser (`L4Factoidal.Wikidata.parseQuerySyntax`, main at
  074a3e5), using a throwaway exporter in a scratch clone. It is not part
  of factoidal. It will be replaced by `parseSparqlAst` when that lands.
  The dump is `data/interim/ast-lean-interim.jsonl`. It has no source
  ranges, and it cannot tell `[]` from `_:b`.
- **Coverage:**

  | Queries | Count |
  |---|---:|
  | Factoidal rewrite parsed and fully explained (no unexplained pattern element; every expression function described) | 536 |
  | Stub: the factoidal parser rejects the rewrite's `WITH … AS %name` prologue (all are named-subquery rewrites) | 23 |
  | Stub: `skipped_unsupported` (MediaWiki API and similar) | 20 |
  | Stub: `parse_error` | 1 |

- **Tests:** `npm test` runs 7 comment-extractor tests and 13 checks
  against the SPEC §8 targets (T1–T13). All pass.

"Fully explained" means every element is described by some rule. It does
not mean every description has been reviewed by a person. The
high-volume multiplicity rules were spot-checked on 9 samples; 2 false
positives were found and fixed.

## Run

```sh
npm test
node src/run.mjs mlp-039 mlp-349       # print L1 (precise) explanations
node src/run.mjs --all                 # writes data/out/records.json and data/out/L1.txt
npm run extract-comments               # regenerates data/comments.json
```

## Layout

| Path | What it is |
|---|---|
| `src/ir.mjs` | Internal representation, mirroring factoidal's `SPARQL.Query` |
| `src/scope.mjs` | Variable scope: may be bound / always bound |
| `src/explain.mjs` | Flattening, label-rewrite recognition, multiplicity analysis, rules → record |
| `src/render.mjs` | L1 precise text |
| `src/names.mjs` | IRI → "label (ID)" from the label cache |
| `src/comments.mjs` | Comments and `#title`/`#defaultView` with offsets; note vs commented-out code |
| `data/wikidata-labels.json` | Labels, descriptions, datatypes for 833 IDs (retrieved 2026-11-24) |
| `data/wikidata-facts.json` | 16 sourced facts the rules rely on |
| `data/translation-notes.json` | Fixed texts per rewrite rule and status |
| `data/comments.json` | Extracted comments (from `classic_query`) |
| `data/out/` | Generated records and L1 text |

## Parallax mapping

`node src/parallax-run.mjs` classifies each parsed rewrite against the Freebase Parallax model (sets, facets, pivots) and writes `data/out/parallax.json`. Tiers: A core; B plus literal filters or computed columns; C plus statement traversal (`p:`/`ps:`/`pq:`); D plus subclass closure; N not mappable, with named blockers.

Negation (`MINUS`, `FILTER NOT EXISTS`) and `FILTER EXISTS` count only when one facet chip can show them (`src/negation.mjs`). That means one shared, always-bound variable, and a single chain of at most two fixed-property hops. The chain ends in a constant, "anything", or a value with one test: a language, "other than X" (so "only gold" becomes "exclude: material includes something other than gold"), or a text match (tier B).

Chips are worded as removing a positive facet value, e.g. "exclude: occupation includes economist" or "exclude: has any value for image". The wording avoids "occupation is not economist", which misleads for properties with several values.

Negated combinations ("not (A and B)"), negations tied to a second column, conditions inside the negation, and deeper chains stay blocked.

## Known limits

- Only L1 (precise) rendering exists. L2 and L3 are not written yet.
- Comments are not attached to specific triples. That needs source
  ranges plus rewrite provenance; they are shown with the code line they
  follow.
- Multiplicity analysis assumes every property is multi-valued, except
  for the invariants in the facts table. It can over-warn when a property
  is single-valued in practice.
- R-JOIN-DROP only covers variables produced by a subquery.
- The facts marked `partial` in `wikidata-facts.json` (year-precision RDF
  form, BCE numbering, QLever distance wording) are not yet verbatim
  checked.

## Hub pages

This code generates the data for two Hub pages:
`docs/web/hub/wikidata-explanations/` (`node src/export-hub.mjs <out.json>`)
and `docs/web/hub/wikidata-parallax/` (`node src/export-parallax-hub.mjs <out.json>`).
Write each output to that page's `*.11tydata.json`. Run `npm test` first.
