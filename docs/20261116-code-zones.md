# Code zones and theorem pipeline — 2026-11-16

Task records: [modularity survey, issue 452 part 2](https://github.com/danbri/factoidal-core/issues/452)
and [theorem pipeline, issue 513](https://github.com/danbri/factoidal-core/issues/513).

## Decisions

Use 13 primary zones in `zones/zones.json`. Rules are unordered path-glob unions with explicit
exclusions. Every tracked and non-ignored untracked file in the five requested roots gets one rule;
new Lean subtrees without a decision fail the coverage check. The inventory includes support files,
tests and binary fixtures. Source-only totals appear beside all-file totals. Symlinks are tagged and
counted without following them into another checkout or a font cache.

Keep `WasmVM/Hosts` in Browser integration without moving code. Split CSS from the Rendering directory;
keep the XPath function and regex libraries in XML. Mark shared primitives as secondary tags. Browser
also contains general tooling and dataflow infrastructure; an import into that zone is not necessarily
a dependency on browser behaviour. The report names every crossing so this distinction is inspectable.

The policy is proposed review guidance, not a list of established defects or a gate that ratchets the
current imports. Named interfaces admit expected crossings, such as URL parsing and SPARQL HTTP adapters.
Unlisted pairs and crossings outside named interfaces are flagged. JSON-LD/GRDDL use supplied loaders;
an import scan cannot prove that those loaders enforce Fetch policy.

## Validation

`python3 tools/zones_test.py` checks coverage, overlapping rules, import comments/strings, static and
literal dynamic JS imports, relative resolution, three-zone cycles, symlinks, untracked/ignored/deleted
files and the JSON/Markdown CLI. No Lean command is run. An initial overlapping benchmark-script rule
was found by the test and narrowed to Lean files. A character literal containing a double quote exposed
a lexical-scanner error; the regression case now checks it.

This change adds offline analysis and skills; browser execution is unchanged. Before/after page timings
are not measured because no page execution path changes. Tool runtime and final premerge results are
recorded below when the complete report and skills are checked.
