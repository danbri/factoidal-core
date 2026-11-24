---
templateEngineOverride: md
---
# Wikidata result views in Factoidal Hub

The Hub starts with the result visualisation. An optional colourised query
editor below it can submit a query to either Wikidata endpoint. Its **Show
parsed structure** action loads the same-origin Factoidal Wasm engine and
uses `parseSparqlStructure`. The returned S-expression comes from Lean's
parsed query AST and preserves property paths. The bundled graph example
appears before the browser makes any SPARQL requests.

The [WDQS presentation comments][views] work in an edited query.
`#defaultView` picks the first result tab. `#view` configures a view
and `#title` supplies its heading. Raw results are available in the second
tab with a download of the complete response, including ASK and RDF
responses where applicable.

Each documented view has a handler in `createResultViews`. Graph follows
Wikidata entity columns and shows the edges incident on a selected node.
Graph builder accepts explicit source, target and edge-label columns.
Map uses Leaflet with CRS84 WKT geometry, layers and marker colours.
Image grid uses Commons media URLs. Timeline shows point dates and date
ranges. Tree and tree map show hierarchies. Dimensions shows parallel
coordinates with value highlighting. The line, bar, scatter and area
charts offer axis selection. Bubble chart uses quantity for size.

WDQS gallery modals, map marker clustering, chart categories and storyboard
animation remain open. The visual preview includes up to 400 rows, and
Graph displays up to 40 nodes. The Raw results download includes all rows.

## Martin Poulter's default view settings

Counted from the prepared query sources in the published catalogue. Cases
with no directive normally start in Table. The 100-query file is an exact
slice of the full catalogue.

| Default view | First 100 | All 580 |
| --- | ---: | ---: |
| No directive | 79 | 438 |
| ImageGrid | 3 | 43 |
| Map | 14 | 42 |
| Graph | 2 | 25 |
| BubbleChart | 0 | 14 |
| BarChart | 2 | 8 |
| ScatterChart | 0 | 6 |
| Timeline | 0 | 2 |
| LineChart | 0 | 1 |
| TreeMap | 0 | 1 |

Both [public downloads][workbench] were checked against the pinned wikitext
harvest and freshly run native Lean and source-built Wikimedia Java outputs.
All 580 saved status/text pairs from each engine matched those runs. See
the [parity audit][audit] for the separate 213-fixture gate and the shared
rewrite limitations.

## Using the parser

In Lean, import `L4Factoidal.SPARQL.FunctionalQuery` for pure transformations
on the query AST or `L4Factoidal.Wikidata.Parser` for parsing under the WDQS
prefix environment. An explicit PREFIX declaration takes precedence. Use
`L4Factoidal.Wikidata.parseQuerySyntax` to preserve the parsed property paths
and `Query.toSse` for a textual S-expression.

In JavaScript, `parseSparqlStructure(query, { wdqs: true })` returns the form,
projected variables and the S-expression. The default uses standard prefixes
only. Specify `version: '1.2'` to select SPARQL 1.2 syntax.

```sh
bash formal/lean4/Wasm/build-wasm.sh
node --test tests/hub/hub_wikidata_results_test.mjs
FACTOIDAL_L4_ASSETS="$PWD/docs/web/hub/assets/l4" \\
  node tools/wikidata/compare_wasm_catalogue.mjs /tmp/mlp-catalogue.json
```

Set `L4_WASM_UV_INCLUDE` to the libuv include directory if its headers are
outside the system include paths. From `docs/`, run `npm ci` and
`npm run serve`, then open
`http://localhost:8080/factoidal/web/hub/wikidata-results/`.

[audit]: ./20261124-mlp-wikidata-catalogue.md#exact-output-and-jsonl-compatibility
[views]: https://www.wikidata.org/wiki/Wikidata:SPARQL_query_service/Wikidata_Query_Help/Result_Views
[workbench]: https://mlp-wikidata-workbench.danbri.chatgpt.site/
