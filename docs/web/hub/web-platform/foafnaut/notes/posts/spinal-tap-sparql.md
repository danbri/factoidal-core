---
title: "Spın̈al Tap: a SPARQL client for Wikidata"
date: 2026-11-09T08:34:22Z
category: "Scripts"
commit: "28982978a"
summary: "A demo page asks Wikidata seven SPARQL questions about Spın̈al Tap, through QLever, and shows the answers as amp-panel cards with dials that go to eleven."
demos: ["spinal-tap-sparql.html"]
---

The page shows each query with syntax highlighting. Where the browser has `fetch`,
it runs them live on `https://qlever.dev/api/wikidata`. Foafnaut page scripts have no
`fetch` yet, so there the page shows a snapshot of the results, held in the page
([third_party/data/wikidata-spinal-tap](https://github.com/danbri/factoidal-core/blob/main/third_party/data/wikidata-spinal-tap/README.md),
CC0, from Wikidata).

- The cards are built in one DOM batch. The page gives the same DOM commands on
  BubblePopJS and on QuickJS-NG (commit
  [558b897d7](https://github.com/danbri/factoidal-core/commit/558b897d7)).
- The wordmark sets the name in Fraktur letters from Noto Sans Math, with chrome and
  a flame edge in SVG. It is not the band's logo. A blackletter line zooms from 1 to
  40 and fades into Foafnaut.
- The name is written <span aria-label="Spinal Tap">Spın̈al Tap</span>, with a dotless
  ı and an n with a diaeresis, as in Wikidata's stylized name (P9989). Screen readers
  get "Spinal Tap".
