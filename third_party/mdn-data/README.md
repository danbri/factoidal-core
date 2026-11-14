# mdn-data (CSS subset)

A trimmed, unmodified copy of the CSS data from the npm package `mdn-data`: the formal
grammar, inheritance and initial value of each CSS property (`css/properties.json`) and the
non-terminals those grammars use (`css/syntaxes.json`).

- Version: 2.37.2
- Source: https://github.com/mdn/data (npm package `mdn-data`)
- Licence: CC0-1.0, see `LICENSE`
- Files kept: `css/properties.json`, `css/syntaxes.json`, `LICENSE`. Everything else in the
  package (API data, localisation strings, at-rules, selectors, units, schemas) is left out.

`tools/css-values/gen-properties.py` reads these two files, applies the corrections and additions
in `tools/css-values/supplement.json`, and writes
`formal/lean4/L4Factoidal/Rendering/CssValues/Data.lean`.

To update: run `npm pack mdn-data` in a scratch directory, copy the two JSON files and `LICENSE`
over these, change the version above, then run the generator and resolve what it reports.
