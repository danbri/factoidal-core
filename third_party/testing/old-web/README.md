# Old web pages for browser tests

Small byte-exact copies of historic pages. The foafnaut browser test
(`labs/demos/foafnaut/native_html_test.ts`) renders them with no network. The
Hub browser can not fetch other sites, so these are also the safe samples for
online tests. There is no open proxy, by owner decision of 2026-11-06.

| Folder | Source | Fetched |
|---|---|---|
| `info.cern.ch/` | https://info.cern.ch/ (the first website, restored by CERN) | 2026-11-06 |

It holds the World Wide Web Virtual Library (`hypertext/DataSources/bySubject/`),
the original NeXT WorldWideWeb browser notes (`hypertext/WWW/NeXT/`, every page
reachable from them that still exists) and a few project pages.

Paths match the source URLs. `index.html` is http://info.cern.ch/.

Licence: the pages carry no licence statement, and none was found on the site.
Copyright stays with CERN and the authors. They are kept as test data only.
Remove them if CERN asks.
