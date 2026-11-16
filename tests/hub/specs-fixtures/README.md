# Sample data of the Data and documents page

- `runs-sample.csv`: rows of runs.csv (wpt-scores, danbri/factoidal-builds) for a few suites, columns
  trimmed, plus three made-up rows: a newest `l4-rif_core` row that is invalid (its older valid rows
  give `lastValid`), an `l4-mathml` row three days older than the rest (a stale built-in suite), and an
  `l4-geosparql` row that the mapping does not know (listed in `unmapped`).
- `meta/<run_id>.json`: the "parts" of the newest `l4w3c-sparql11` row. Illustrative counts, not the
  recorded run's sub-manifests.
- `sample/`: what `tests/browser-wpt/specs-data.py` writes from these files:

```
python3 tests/browser-wpt/specs-data.py --runs tests/hub/specs-fixtures/runs-sample.csv \
  --meta-dir tests/hub/specs-fixtures/meta --only-recorded --now 2026-11-16T06:00:00Z \
  --out tests/hub/specs-fixtures/sample
```

`tests/browser-wpt/specs_data_test.py` checks that the generator still writes exactly `sample/`;
`tests/hub/specs_test.mjs` checks `sample/` against the schema and renders the page from it.
