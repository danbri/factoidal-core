---
templateEngineOverride: md
---
# Wikidata query rewriter in Factoidal Hub

The page at `/factoidal/web/hub/wikidata-rewriter/` calls
`@factoidal/core`'s browser `wikidataRewrite` operation. The Hub serves
the API and the built WASM assets from the same origin. The graph example
appears without loading the engine or contacting a SPARQL endpoint.
The rewriter loads on the first **Rewrite in browser** action. Running a
query submits just the chosen text to the selected Wikidata endpoint.
The example's three result rows are bundled fixtures.

The [WDQS presentation comments][views] work with the classic query.
`#defaultView` picks the first result tab. `#view` configures a view
and `#title` supplies its heading. An edited rewrite may override
those settings. The second tab presents raw result bindings with
language tags and datatypes, or an ASK boolean or RDF response as
appropriate. The complete response data is downloadable there.

Each documented result view has its own handler in the exported
`createResultViews` registry. Graph follows Wikidata entity columns and
shows the edges incident on a selected node. Graph builder accepts
explicit source, target and edge-label columns. Map uses the Hub's
vendored Leaflet and OpenStreetMap tiles, with CRS84 WKT geometry, a
layer selector and marker colours. Image grid uses Commons media URLs.
Timeline shows point dates and date ranges. Tree and tree map use
expandable or drillable hierarchy views. Dimensions shows parallel
coordinates with value highlighting. The line, bar, scatter and area
charts offer axis selection. Bubble chart uses the first numeric
quantity for size.

These are Hub handlers for the WDQS view names. The WDQS gallery modal,
map marker clustering, chart categories and storyboard animation are
later work. Map accepts Point, LineString, Polygon and their Multi
forms in default longitude–latitude order. The display caps the
visualisation at 400 rows and the graph at 40 nodes. The raw table
previews 200 rows and the download contains the full response.

Chromium loaded the freshly compiled Wasm module, removed the example’s
Blazegraph query hint, ran the rewrite on QLever and rendered all three
returned rows in both the Graph and Raw results tabs. The same module
matched the native rewrite status and exact output across all 580
Poulter inputs in the Node API audit. Those results included all 434
Wikimedia rewrites. The module’s SHA-256 was
`e080b4987a92020d62c1229e2d7622953022312661b3da099ccba34872105d54`.

The [parity audit][audit] covers the 580 prepared English Poulter
inputs and the separate suite of 213 pinned upstream fixtures.
The Hub page does not modify the rewrite rules.

```sh
# Run from the repository root with the matching toolchains on PATH.
bash formal/lean4/Wasm/build-wasm.sh
node --test tests/hub/hub_wikidata_rewriter_test.mjs
FACTOIDAL_L4_ASSETS="$PWD/docs/web/hub/assets/l4" \
  node tools/wikidata/compare_wasm_catalogue.mjs /tmp/mlp-catalogue.json
```

Set `L4_WASM_UV_INCLUDE` to libuv's include directory if its headers
are outside the system include paths. The Wasm build uses the headers
for declarations.

From `docs/`, run `npm ci` and `npm run serve`, then open
`http://localhost:8080/factoidal/web/hub/wikidata-rewriter/`.
The matching web build assets can also be installed with
`bash tools/fetch-builds.sh --set web --strict`.

[audit]: ./20261124-mlp-wikidata-catalogue.md#exact-output-and-jsonl-compatibility
[views]: https://www.wikidata.org/wiki/Wikidata:SPARQL_query_service/Wikidata_Query_Help/Result_Views
