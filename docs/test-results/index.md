---
title: Test results
layout: base.njk
---

# Test results

Scores and measurements of Factoidal and of Foafnaut, the browser built on the same code.
Each page below reads its numbers from a recorded run; none is written by hand.

## Pages

- [Conformance](../web/hub/conformance/): Test262 (JavaScript) and the Web Platform Tests from full measured runs of Foafnaut, next to other browsers, with the history of every run.
- [Standards support](../web/hub/#standards-support): one row for each W3C data standard suite (RDF, SPARQL, OWL 2, SHACL, ShEx, JSON-LD, XSLT and more), from the latest scoreboard record.
- [Rendering and font scores](../web/hub/render-scores/): the score of each rendering and font suite by commit, and the largest failure groups.

## Files in this directory

Machine-readable results of older benchmark and server test runs:

- [closure-bench-baseline.json](closure-bench-baseline.json): RDFS and OWL 2 RL closure timings.
- [npm-costs.json](npm-costs.json): size and start-up costs of the npm package.
- [perf-quadstore-baseline.json](perf-quadstore-baseline.json): quad store benchmark baseline.
- [ukparliament-bench.json](ukparliament-bench.json) ([CSV](ukparliament-bench.csv)) and [ukparliament-bench-modern.json](ukparliament-bench-modern.json) ([CSV](ukparliament-bench-modern.csv)): SPARQL timings over the UK Parliament data.
- [lws-touchstone-2026-10-21-index/run.txt](lws-touchstone-2026-10-21-index/run.txt): Linked Web Storage server tests of 2026-10-21.
