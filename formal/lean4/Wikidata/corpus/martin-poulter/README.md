# Martin Poulter's Wikidata query pages

Snapshot harvested 24 November 2026 via the MediaWiki API. `pages.json` contains
the original wikitext of the main page and all 14 subpages, each with revision,
permalink, history, timestamp and SHA-256. `queries.json` extracts 579 SPARQL
and SPARQL2 query templates, with page, section and revision provenance.

Wikidata user-namespace text is CC BY-SA 4.0, not CC0 structured data; see
https://www.wikidata.org/wiki/Wikidata:Licensing and
https://creativecommons.org/licenses/by-sa/4.0/. Attribution: Martin Poulter
and other Wikidata contributors; follow each page's history for contributors.
Some source pages acknowledge additional individual query authors. These files
are a separate CC BY-SA corpus, not Apache-licensed project code. Extraction
copies the template contents unchanged and retains the complete source pages.

Regenerate with `python3 tools/wikidata/harvest_martin_poulter.py`. The script
captures current revisions and requires internet. It extracts SPARQL/SPARQL2
`query=` templates whose whitespace-delimited closing braces end a line; it
does not expand templates or harvest URL-encoded links. Matching template starts
and extracted counts agree (579), but this does not establish wider completeness.
The Lean probe does not modify prefixes or execute queries. WDQS implicit
prefixes and extensions can cause a rejection without making a query invalid in
WDQS. From formal/lean4 run `lake env lean --run Wikidata/MartinPoulterProbe.lean`.
