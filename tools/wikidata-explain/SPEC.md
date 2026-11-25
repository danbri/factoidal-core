# Deterministic explanations of the MLP Wikidata queries — spec, draft 0

Status: draft for discussion, 2026-11-24. No code yet.
Scope: deterministic explanations only. No LLM is involved at any stage
described here.

## 1. Goal

For each query in `mlp-all-queries.json`, produce an explanation that
is **exact first and simplified second**. A rule-based generator
produces it from the parsed query, so it is reproducible, diffable and
checkable.

It explains **what the results mean**: what one row is, which columns
it has, which things are included and excluded, and the ways the
results can surprise a reader. It does not explain how an engine
executes the query.

### Principles

1. **Account for every node.** Every node in the parsed query is either
   covered by a rule or listed under `unexplained`. Nothing is dropped
   silently, and this is mechanically checkable: the set of covered
   parse-tree paths must equal the set of all paths.
2. **No claim without a trigger.** Every sentence traces to a rule ID
   and the parse-tree path(s) that fired it.
3. **Simplify by omitting, never by rewording into something false.**
   A plainer level may leave out a caveat, and must then list it under
   `omitted_caveats`. It must not restate a caveat in a way that is
   untrue.
4. **We explain the Factoidal rewrite.** The query explained is always
   `lean_replacement_query`: the newer Factoidal (Lean) rewrite, not
   Wikimedia's Java rewrite (`replacement_query`).
   - **`rewritten` (453 queries):** explain `lean_replacement_query`.
     The original is used only for the translation notes (§6) and to
     map rewriter-generated structure back to what the author wrote
     (PARSE-API-NEEDS item 10).
   - **`unchanged` (106):** `lean_replacement_query` is the same text as
     the original; explain it.
   - **`skipped_unsupported` (20) and `parse_error` (1):** there is no
     Factoidal rewrite (`lean_replacement_query` is null). We produce
     no full explanation, only a stub record with the status, the
     diagnostic code (e.g. `unsupported_proprietary_service`) and, for
     an unsupported service, the R-EXTERNAL description of what the
     original would have called.
5. **Author comments are hints, not facts.** Comments such as
   `# Not closed down` are kept from the source text, because parsing
   discards them. They are shown as "the author notes". They never
   replace what the query actually does. When a comment and the query
   disagree, say so.

6. **No generic statements.** Never state what holds for every query of
   a kind, e.g. "one row per way the conditions can be met" for any
   SELECT, or what DISTINCT means in general. State only consequences
   specific to this query: rows that can repeat, an item spanning several
   rows, a column that is always blank. A query feature with no special
   consequence gets at most a terse fact line ("Rows are deduplicated
   (DISTINCT).").

## 2. Inputs

| Input | Source | Status |
|---|---|---|
| Parse tree | factoidal `SPARQL.Query`, lossless JSON (planned; see PR 917 `docs/20261124-sparql-functional-api.md`) | **waiting** |
| WDQS prefix environment | `L4Factoidal.Wikidata.Parser` (38 prefixes) | in PR 917 |
| Rewrite status, rule IDs, warnings | `lean_rewrite_*` fields; `wikidataRewrite()` op in PR 917 | available |
| Display directives | `#defaultView:` comments; reuse `view-data.mjs` from PR 917 | available |
| Author comments | source text, with offsets | needs a small extractor |
| Labels, descriptions, property datatypes | dated cache `explain/data/wikidata-labels.json` (833 IDs, en/mul, retrieved 2026-11-24) | done |
| Wikidata facts table | `data/wikidata-facts.json` (§5) | draft 0.1 |

The generator is written against a thin adapter over the parse tree:
`kind(node)`, `children(node)`, `vars(node)`, `path(node)`. Until the
factoidal JSON exists, nothing is built against any other parser.

### Constructs the rules match on (from `Expr.lean`)

- **Patterns:** `bgp`, `join`, `leftJoin` (OPTIONAL), `filter`,
  `union`, `minus`, `graph`, `lateral`, `bind`, `values`, `service`,
  `serviceVar`, `subSelect`, `propertyPath`, `empty`.
- **Query:** `form`, `dataset`, `pattern`, `groupBy`, `having`,
  `modifier{orderBy, distinct, reduced, offset, limit}`, `postValues`.
- **Expressions** of interest: `aggregate(fn, distinct, e)` with `fn`
  one of count, sum, min, max, avg, groupConcat or sample; `existsPat`,
  `notExistsPat`, `bound`, `cond`, `coalesce`, `lang`, `regex`,
  `contains`, `strStarts`, `year`, `functionCall`.

## 3. The structured description (output record)

One JSON record per query. All text fields are generated from
templates.

```jsonc
{
  "id": "mlp-349",
  "explained_query": "lean_replacement_query", // or null for a stub (§1 principle 4)
  "versions": { "parser": "...", "rules": "0.1", "facts": "0.1", "labels_retrieved": "..." },
  "query_sha256": "...",

  "row": {                                   // what one result row is
    "unit": ["?obj"],                        // vars whose combination the row is "about"
    "multiplicity": "may_repeat",            // unique | may_repeat | aggregated
    "repeat_reasons": [ { "rule": "R-MULT-VALUE", "path": "...", "var": "?_b0" } ]
  },
  "columns": [
    { "var": "?count", "kind": "aggregate", "fn": "count", "distinct": false,
      "of": "?obj", "may_be_blank": false }
  ],
  "required":  [ /* conditions every row satisfies; one entry per triple, path or filter */ ],
  "optional":  [ /* parts that may be blank, and what blank means */ ],
  "excluded":  [ /* MINUS / NOT EXISTS, with exact semantics */ ],
  "grouping":  { "keys": [], "aggregates": [], "having": [] },
  "ordering":  [], "limit": null, "offset": null, "distinct": false,
  "display":   { "default_view": null, "options": null },
  "external":  [ /* SERVICE calls other than the label service */ ],
  "labels":    { "languages": ["en", "mul"], "fallback": "entity ID" },
  "translation_notes": [ /* §6 */ ],
  "author_comments": [ { "offset": 0, "text": "..." } ],
  "caveats":   [ { "rule": "R-COUNT-ROWS", "severity": "changes_answer",
                   "paths": ["..."], "precise": "...", "plain": "..." } ],
  "unexplained": [ /* parse-tree paths no rule covered */ ]
}
```

**Severity** sets which caveats survive simplification:

- `changes_answer`: the result differs from a natural reading of the
  title or the question. Always kept, at every level.
- `scope`: a precise boundary of what's included. Kept at the precise
  and intermediate levels.
- `display`: labels, ordering and presentation. Kept at the precise
  level only.

## 4. Rules (draft 0)

Each rule has an ID, a trigger on the parse tree, a precise template,
a plain template and a severity. The triggers below are written
informally; the code will make them exact. Placeholders such as
`{P}` and `{Q}` render as *label (ID)*.

### 4.1 Wikidata statement model

| ID | Trigger | Precise text | Sev |
|---|---|---|---|
| R-TRUTHY | triple with `wdt:{P}` | "uses only the best-ranked value(s) of {P}: preferred-rank statements if any exist, otherwise normal-rank. Deprecated statements are ignored." | scope (stated once per query, listing every `wdt:` property) |
| R-FULLSTMT | `p:{P}` → `ps:{P}` | "looks at every {P} statement, of any rank, including deprecated ones." | scope |
| R-QUALIFIER | `pq:{P}` on a statement var | "{P} here is a qualifier on that statement, not a property of the item." | scope |
| R-SOMEVALUE | object is `[]` or an otherwise-unused variable | "has at least one {P} value. An 'unknown value' counts; 'no value' does not." (facts F-SOMEVALUE, F-NOVALUE) | scope |
| R-SUBCLASS | path `wdt:P31/wdt:P279*` to `{Q}` | "is an instance of {Q} or of any class that is (through any chain of 'subclass of' links) a subclass of {Q}." | scope |
| R-DIRECT-ONLY | `wdt:{P}` where {P} is in the facts table's hierarchy-property list (P131, P361, P279, P171...) without `*`/`+` | "{P} is matched directly: things linked to {Q} only through intermediate {P} links are not included." | changes_answer |
| R-ANYPROP | variable in predicate position | "linked to {Q} by any property at all. In practice these are best-rank direct values (`wdt:`) and a few other direct links; statement nodes are not reached this way." | scope |
| R-SITELINK | `schema:about` + `schema:isPartOf <wiki>` | "has a page on {wiki}. An item has at most one page per wiki (F-SITELINK-UNIQUE)." | scope |
| R-LABEL-EXACT | `rdfs:label`/`skos:altLabel` with `lang(...) = "x"` | "the label/alias in language tag exactly 'x'. Variants such as 'x-gb' and the 'mul' label are not included." | scope |
| R-LITERAL-EXACT | literal object with a language tag | "whose {P} is exactly the text "…" with language tag 'x' (case-sensitive, whole string)." | scope |

### 4.2 Row multiplicity: the core analysis

Rows may repeat whenever a variable can take several values for the
same "unit". The default assumption is that **any property may have
several values**. The only exceptions are invariants in the facts
table, e.g. one label per language, one sitelink per wiki, one value
per statement for `ps:`.

| ID | Trigger | Precise text | Sev |
|---|---|---|---|
| R-MULT-VALUE | a variable or `[]` bound by a triple whose property is not single-valued | "A {unit} with several {P} values produces one row per value." | changes_answer if under COUNT or shown as one-per-item, else scope |
| R-MULT-PATH | sequence path `a/b` | "Each distinct intermediate link produces its own row. A thing that is an instance of two qualifying classes appears twice." | as above |
| R-MULT-UNION | `union` whose branches can both match the same unit | "Something matching both alternatives (or one alternative in several ways) appears once per match." | as above |
| R-MULT-OPTIONAL | `leftJoin` whose right side can match several times | "If several {P} values exist, the row is repeated for each; if none, it appears once with {var} blank." | scope |

### 4.3 Aggregation and selection

| ID | Trigger | Precise text | Sev |
|---|---|---|---|
| R-COUNT-ROWS | `aggregate(count, distinct=false, ?x)` and the row is `may_repeat` | "{?c} counts matching rows, not distinct {things}. A {thing} is counted once for each way it matches: {repeat_reasons}." | changes_answer |
| R-COUNT-DISTINCT | `count, distinct=true` | "{?c} counts distinct values of {?x}." | — |
| R-COUNT-STMTS | `count(?s)` where `?s` is a statement variable (`p:`) | "{?c} counts statements, not items. An item with several such statements is counted several times." | changes_answer |
| R-SAMPLE | `aggregate(sample, ...)` | "{?v} is one value chosen arbitrarily from the group. Which one may vary between runs and endpoints." | scope |
| R-GROUPCONCAT | `groupConcat(sep)` | "all values in the group, joined with "{sep}", in no guaranteed order." | display |
| R-GROUP-KEY-MULT | group key that is not functionally determined by the unit | "Grouping is by {keys}, so a {unit} with several {key} values appears once per value." | changes_answer |
| R-GROUP-BY-LABEL | group key is a label variable | "Things whose labels are identical are merged into one group." | changes_answer |
| R-HAVING | `having` | "Only groups where {cond} are kept." | scope |
| R-MULT-PER-ENTITY | a projected column not determined by the first projected variable | "A ?x can appear in several rows: once for each value of ?y (DISTINCT removes only rows identical in every column)." Replaces the generic R-DISTINCT-ROW, which was dropped. | scope |
| R-JOIN-DROP | join on a lookup (e.g. `?language wdt:P218 ?code`) | "Rows whose {var} has no matching {P} are dropped; a {var} matching several things repeats." | changes_answer |

### 4.4 Negation and scope

| ID | Trigger | Precise text | Sev |
|---|---|---|---|
| R-MINUS | `minus(l, r)` sharing variables V | "excludes any result for which {r} also holds, matching on {V}." | scope |
| R-MINUS-NOSHARED | `minus` with no shared variables | "this exclusion has **no effect**: it shares no variables with the rest of the query." | changes_answer |
| R-NOTEXISTS | `filter(notExistsPat p)` | "keeps a result only if there is no way to satisfy {p} with this result's values of {V}." | scope |
| R-SCOPE-LEAK | a variable bound only inside `minus`/`notExistsPat`/`existsPat` but used outside | "{?v} is never set: the only place it gets a value is inside the exclusion, which does not pass values out. So {column} is always blank." | changes_answer |
| R-OPTIONAL | `leftJoin` | "{vars} are filled in if {r} holds, and left blank otherwise." | scope |

### 4.5 Ordering, limits, dates, strings

| ID | Trigger | Precise text | Sev |
|---|---|---|---|
| R-ORDER | `orderBy` | "sorted by {keys}." | display |
| R-ORDER-UNBOUND | order key can be blank | "rows where {key} is blank sort first in ascending order (last in descending)." | display |
| R-LIMIT-NOORDER | `limit` without `orderBy` | "only {n} rows are returned, chosen arbitrarily." | changes_answer |
| R-YEAR | `year(e)` on a date property | "the year part of {P}. Wikidata stores dates known only to the year or decade with placeholder month and day, so the year is reliable but finer parts may not be." | scope |
| R-REGEX/R-CONTAINS | string tests | exact semantics: case sensitivity, flags, anchoring | scope |

### 4.6 Services, labels, display

| ID | Trigger | Precise text | Sev |
|---|---|---|---|
| R-LABELS | rewritten label pattern (rule `rewrite-wikibase-label-service`) | "{var}Label is the English label, else the 'mul' (multilingual) label, else the bare entity ID." Read from the rewritten query, not assumed. | display |
| R-EXTERNAL | `service` to anything except the label service, e.g. `wikibase:mwapi` | "fetches data from {endpoint} at query time. The results depend on that service's live content and cannot be described from the query alone." | changes_answer |
| R-VIEW | `#defaultView:X` | "shown by default as a {X}." | display |
| R-DELETED-ID | a `P`/`Q` ID that is missing from the label cache | "{ID} no longer exists on Wikidata, so this part of the query matches nothing." (P794 in the corpus) | changes_answer |
| R-REDIRECT-ID | an ID the cache marks as redirected | "{ID} is now a redirect to {target}. Data recorded against the target may not match." (Q5227308 → Q5227240, Q39811647 → Q21112633) | changes_answer |

## 5. Wikidata facts table

The table is in `data/wikidata-facts.json`: 16 facts, each with a
source, a quotation where one exists, and a status (`verbatim`,
`partial` or `corpus`). A rule may state a `partial` fact only after it
has been verified. F-HIERARCHY-PROPS is editorial policy, not a fact
about the data.

Corrections made while verifying:

- F-SOMEVALUE: "unknown value" appears under both `wdt:` and `ps:`, so
  `?x wdt:P []` matches it.
- F-NOVALUE: "no value" is only a `wdno:` class, so `?x wdt:P []` does
  not match it.
- F-LABEL-UNIQUE: at most one label and one description per language,
  any number of aliases.
- F-SITELINK-UNIQUE: at most one sitelink per wiki.
- F-REDIRECT: the old ID carries only `owl:sameAs` in WDQS, so a query
  naming it matches almost nothing.
- F-DATE-PRECISION: the `wdt:` value of a date known only to the year
  still looks like a full date. Precision is on the full value only.

## 6. Translation notes

The fixed texts are in `data/translation-notes.json`, keyed by:

- the Factoidal `rule_id/variant_id`: label-service automatic (376) and
  manual (70), named subquery (23), legacy select alias (18), query
  hint (8), isSomeValue (4), geof:distance (2);
- the input-preparation step: auto-language (438), MediaWiki pipe
  escape (5);
- the rewrite status, with the warning codes for skipped queries;
- `endpoint_audit` results, which are reported as measured, without
  explanation.

Points worth knowing:

- **Label languages** are the author's list in their order, duplicates
  removed, with `mul` where the author listed it or appended last.
  Descriptions never get `mul` and have no fallback.
- **The named-subquery rewrite keeps `WITH … AS` / `INCLUDE`**, which is
  not standard SPARQL 1.1. In `mlp-192` the QLever version returned
  20,456 rows against Blazegraph's 20. No note may claim equivalence
  for this rule.
- **Scaffolding variables** such as `?x__label_value`,
  `?x__wdqs_input` and `?__include_*` are explained in terms of what the
  author wrote, never as themselves.

## 7. Renderings

All renderings are generated from the record. None is free text.

- **L1 precise.** Every section, every caveat, entities named as
  *label (ID)*. Fixed terms ("best-ranked value", "row") are defined
  once, in a glossary footer.
- **L2 intermediate.** Row meaning, columns, required, optional and
  excluded conditions, and caveats of severity `changes_answer` and
  `scope`. IDs are kept in parentheses.
- **L3 plain.** One or two sentences built from the row meaning and
  required conditions, plus every `changes_answer` caveat in plain
  form. No IDs.
- Every rendering lists its omissions (`omitted_caveats`) in
  machine-readable form, so a reviewer can see what was simplified
  away.

## 8. Test set and target explanations

These 13 queries were chosen to cover the most frequent idioms in the
corpus (lexical survey, approximate): `wdt:` 544, `MINUS` 144, `COUNT`
without `DISTINCT` 109, `GROUP BY` with `OPTIONAL` 81, `SAMPLE` 56,
`P31/P279*` 44, `mwapi` 20. For each, the hand-written **L1 target**
lists the *facts the generator must produce*; wording may differ.

Labels were checked against the label cache of 2026-11-24.

### T1 `mlp-003` — "Count of scientific articles"
```sparql
SELECT (COUNT(?article) AS ?count) WHERE { ?article wdt:P31/wdt:P279* wd:Q13442814 }
```
- **Row:** one row, `?count`.
- **Required:** `?article` is an instance of scholarly article
  (Q13442814) or any subclass of it (R-SUBCLASS), using best-ranked
  instance-of values (R-TRUTHY).
- **Caveat** (changes_answer, R-COUNT-ROWS + R-MULT-PATH): it counts
  (article, qualifying instance-of value) pairs. An article that is an
  instance of two qualifying classes is counted twice, so the number
  can exceed the number of articles.

### T2 `mlp-349` — "How many items have an inventory number but no collection?"
```sparql
SELECT (COUNT(?obj) AS ?count) WHERE { ?obj wdt:P217 [] MINUS {?obj wdt:P195 []} }
```
- **Required:** `?obj` has at least one best-ranked inventory number
  (P217); unknown value counts (R-SOMEVALUE).
- **Excluded:** anything with at least one best-ranked collection
  (P195) value, matched on `?obj` (R-MINUS). Something whose only
  collection statements are deprecated is *not* excluded (R-TRUTHY).
- **Caveat** (changes_answer, R-COUNT-ROWS + R-MULT-VALUE): an item
  with several inventory numbers is counted once per number. The title
  asks "how many items"; the query counts item-number pairs.

### T3 `mlp-268` — "How many Wikidata things have the 'in collection' property"
```sparql
SELECT (COUNT(?obj) AS ?count) WHERE { ?obj p:P195 ?s. ?s ps:P195 ?collection. MINUS { ?s pq:P582 [] } }
```
- **Required:** every collection (P195) statement of every rank,
  including deprecated (R-FULLSTMT).
- **Excluded:** statements that carry an end time (P582) qualifier
  (R-QUALIFIER, R-MINUS on `?s`).
- **Caveat** (changes_answer, R-COUNT-STMTS): counts statements, not
  things. An item in three collections counts three times. The title
  says "things".

### T4 `mlp-030` — "educated at the University of Oxford or at individual colleges"
```sparql
SELECT (COUNT(?alum) AS ?count) WHERE { { ?alum wdt:P69 wd:Q34433 } UNION { ?alum wdt:P69/wdt:P31 wd:Q2581649 } }
```
- **Required:** either a best-ranked educated-at (P69) value of
  University of Oxford (Q34433), or a best-ranked P69 value that is
  itself directly an instance of college of the University of Oxford
  (Q2581649).
- **Scope:** any entity, not only humans.
- **Caveat** (changes_answer, R-COUNT-ROWS + R-MULT-UNION +
  R-MULT-PATH): someone at both the University and a college, or at
  two colleges, is counted more than once. It counts qualifying
  education links, not people.

### T5 `mlp-352` — "Semantic search · Synonyms"
```sparql
SELECT DISTINCT ?name WHERE { VALUES ?rel {rdfs:label skos:altLabel} VALUES ?rel2 {rdfs:label skos:altLabel}
  ?target ?rel "Confucius"@en; ?rel2 ?name FILTER ( lang(?name)="en" ) }
```
- **Required:** any entity whose label or any alias is exactly
  "Confucius" tagged `en` (R-LITERAL-EXACT).
- **Columns:** each English label or alias of such entities, language
  tag exactly `en` (R-LABEL-EXACT), duplicates removed
  (R-MULT-PER-ENTITY).
- **Note:** "Confucius" itself is always among the results.

### T6 `mlp-382` — "Biographies in the Plomer Dictionary of Booksellers and Printers"
```sparql
SELECT ?entry ?wslink WHERE { ?entry wdt:P1433 wd:Q40901539. # published in Plomer DBP
  OPTIONAL{ ?wslink schema:about ?entry; schema:isPartOf <https://en.wikisource.org/> } }
```
- **Required:** best-ranked published in (P1433) = *A Dictionary of the Booksellers and Printers who Were at Work in England, Scotland and Ireland from 1641 to 1667* (Q40901539).
- **Optional:** the entry's English Wikisource page, at most one per
  item (R-SITELINK, F-SITELINK-UNIQUE). Blank if none.
- **Rows:** one per entry, since P1433 to a fixed object cannot
  multiply.
- **Author note:** "published in Plomer DBP".

### T7 `mlp-348` — "Books with a title in a given language but not a label in that language"
```sparql
SELECT ?item ?lang ?title WHERE { ?item wdt:P31/wdt:P279* wd:Q571 ; wdt:P1476 ?title .
  BIND(LANG(?title) as ?lang) FILTER (?lang != "und")
  FILTER (NOT EXISTS{ ?item rdfs:label ?itemLabel. FILTER(lang(?itemLabel) = ?lang) }) }
```
- **Required:** instance of book (Q571) or a subclass of it; each
  best-ranked title (P1476) whose language is not "und".
- **Excluded** (R-NOTEXISTS, correlated on `?item` and `?lang`): titles
  for which the item has a label in exactly that language tag. A "mul"
  label does not count as a label in that language.
- **Rows:** one per (book, title). Also **duplicated** for a book that
  is an instance of two qualifying classes (R-MULT-PATH, no DISTINCT;
  changes_answer).

### T8 `mlp-248` — "Places visited by the Sibthorp/Bauer expedition lacking co-ordinates"
```sparql
SELECT ?loc ?locLabel (SAMPLE(?coords) AS ?latlong) WHERE { wd:Q52496052 wdt:P276 ?loc.
  MINUS {?loc wdt:P625 ?coords} SERVICE wikibase:label {...} } GROUP BY ?loc ?locLabel
```
- **Required:** `?loc` is a best-ranked location (P276) of Sibthorp and Bauer expedition (Q52496052).
- **Excluded:** places with any best-ranked coordinate location (P625).
- **Caveat** (changes_answer, R-SCOPE-LEAK): `?latlong` is **always
  blank**, because `?coords` only gets a value inside the MINUS. That
  is harmless here, since the places are chosen for having no
  coordinates, but the column is meaningless.
- **Translation:** label service rewritten (§6).

### T9 `mlp-345` — "Numbers of language labels for things with a Japan Search Name ID"
```sparql
SELECT ?languageLabel ?count WHERE { {SELECT ?langcode (COUNT(?label) as ?count) WHERE {
  ?thing wdt:P6698 ?jpsid; rdfs:label ?label. BIND(lang(?label) AS ?langcode) } GROUP BY ?langcode }
  ?language wdt:P218 ?langcode SERVICE wikibase:label {...} } ORDER BY DESC(?count)
```
- **Inner:** for each label language tag, the count of labels on items
  with a Japan Search name ID (P6698). An item with two such IDs counts
  twice (R-COUNT-ROWS).
- **Outer** (R-JOIN-DROP, changes_answer): language tags are matched
  to items by exact ISO 639-1 code (P218). Tags with no such item
  ("mul", "zh-hans", "en-gb", three-letter codes) **disappear from the
  results**. A code held by several items repeats its count.
- Sorted by count, highest first.

### T10 `mlp-117` — "Topics with Featured Articles in more than one language"
```sparql
SELECT ?item ?itemLabel (COUNT(?sitelink) AS ?count) WHERE { ?sitelink schema:about ?item; wikibase:badge wd:Q17437796 .
  SERVICE wikibase:label {...} } GROUP BY ?item ?itemLabel HAVING(?count > 1) ORDER BY DESC(?count)
```
- **Row:** one per item. `?count` is the number of its wiki pages
  carrying the featured-article badge (Q17437796). That's one per wiki
  (F-SITELINK-UNIQUE), so the count is exact.
- **Kept:** items with at least two such pages (R-HAVING).
- **Scope:** counts wikis, which may include non-Wikipedia projects,
  rather than "languages".

### T11 `mlp-197` — "People connected with Coventry … but no image"
```sparql
SELECT DISTINCT ?person ?personLabel ?personDescription (YEAR(?dob) AS ?born) WHERE {
  ?person ?prop wd:Q6225; wdt:P31 wd:Q5. MINUS {?person wdt:P18 ?image}
  OPTIONAL {?person wdt:P569 ?dob} SERVICE wikibase:label {...} } ORDER BY ?born
```
- **Required:** linked to Coventry (Q6225) by any property (R-ANYPROP);
  best-ranked instance of human (Q5), directly, not via a subclass.
- **Excluded:** anyone with a best-ranked image (P18).
- **Optional:** birth year (R-YEAR).
- **Rows:** DISTINCT over the whole row, so a person with two
  best-ranked birth dates in different years appears twice
  (R-MULT-PER-ENTITY). People with no birth date come first
  (R-ORDER-UNBOUND).

### T12 `mlp-329` — "External links from Ashmolean Museum's English Wikipedia article"
- **Status:** `skipped_unsupported`, so there is no Factoidal rewrite. The output is a **stub record**, not a full explanation.
- **R-EXTERNAL** (changes_answer): calls the MediaWiki API of
  en.wikipedia.org at query time for the external links of the page
  "Ashmolean_Museum". Nothing is looked up in Wikidata. The results
  depend on the live article.
- **Translation note:** not runnable on QLever.

### T13 `mlp-039` — "Map of things in Oxford colour-coded by type"
(query shown in the discussion)
- **Required:** best-ranked located in the administrative territorial
  entity (P131) = Oxford (Q34217), **directly** (R-DIRECT-ONLY;
  changes_answer).
- **Excluded:** anything with a best-ranked dissolved/abolished/
  demolished date (P576), including "unknown value" (R-SOMEVALUE).
  Author note: "Not closed down".
- **Location:** own coordinates (P625) if any, otherwise the
  coordinates qualifier on a headquarters location (P159) statement of
  any rank (R-FULLSTMT, R-QUALIFIER). One is chosen arbitrarily
  (R-SAMPLE).
- **Rows:** grouped by place, place label and type label. A place with
  several types appears once per type, and types with identical
  labels merge (R-GROUP-KEY-MULT, R-GROUP-BY-LABEL). Places with no
  coordinates at all remain, with a blank location.
- **Display:** map; the `?location` column is hidden.

## 9. Evaluation (after code exists)

1. **Coverage:** the share of the 580 queries with an empty
   `unexplained` list, and a histogram of unexplained node kinds. This
   is the main measure of how far mechanization goes.
2. **Target agreement:** the generator's L1 output on T1–T13 contains
   every fact listed in §8.
3. **Title disagreement:** how many `changes_answer` caveats contradict
   a natural reading of the title (T2, T3 and T4 above). This is useful
   in its own right as a report to the corpus maintainer.
4. **Stability:** re-running on the same inputs gives byte-identical
   output.

## 10. Open questions

- The shape of the factoidal parse JSON: property paths, blank nodes
  (`[]` as fresh variables?), and source offsets for each node so
  author comments can be attached.
- Whether the facts table should live in factoidal (as RDF?) or here.
