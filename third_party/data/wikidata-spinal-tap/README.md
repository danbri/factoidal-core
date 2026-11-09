# Wikidata about Spinal Tap: a snapshot of SPARQL results

`snapshot.json` holds the results of the seven SPARQL queries of the demo page
`labs/demos/foafnaut/pages/spinal-tap-sparql.html`, as SPARQL 1.1 Query Results JSON, with the
query text beside each result set.

- **Source:** Wikidata, <https://www.wikidata.org/>.
- **Endpoint:** QLever, `https://qlever.dev/api/wikidata` (the old address,
  `https://qlever.cs.uni-freiburg.de/api/wikidata`, redirects there), HTTP GET with `query=`
  and `Accept: application/sparql-results+json`.
- **Retrieved:** the `provenance.retrieved` field of `snapshot.json` (UTC).
- **Licence:** Wikidata's structured data is CC0 1.0 (public domain dedication),
  <https://creativecommons.org/publicdomain/zero/1.0/>. Only labels, descriptions, dates, numbers
  and item identifiers are kept; there are no images or other media.
- **Changes:** QLever's own response fields (timing and the like) are dropped; `head` and
  `results.bindings` are kept as returned.

The page runs the same queries live when the browser has `fetch`. Without it (Foafnaut page
scripts today), it shows these results, inlined into the page as one
`<script type="application/json" id="s-NAME">` block per query.

Refresh, check:

    python3 labs/demos/foafnaut/tools/spinal-tap-snapshot.py --capture   # network: QLever
    python3 labs/demos/foafnaut/tools/spinal-tap-snapshot.py --check     # no network
