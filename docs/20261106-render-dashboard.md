# Rendering and font scores dashboard

Date: 2026-11-06. Issue: https://github.com/danbri/factoidal/issues/1245.

The owner asked for dashboards, sensible metrics and regular iteration. This
note records what now exists and what the first run found.

## Files

- `tools/render-dashboard/history.jsonl`: one record per suite and run. The
  file only grows. `origin` is `measured`, `copied` (from a named source) or
  `not-run` (with a reason, and no counts).
- `tools/render-dashboard/run.py`: runs the suites, adds records, writes the
  page. `--list` shows the suites. `--only` selects some.
- `tools/render-dashboard/font_coverage.py`: counts characters, scripts and RGI
  emoji sequences of a named font set, out of Unicode 18.0.0.
- `tools/render-dashboard/old_web.ts`: renders the old-web mirror through the
  browser document path.
- `tools/render-dashboard/page.py`: writes `docs/web/hub/render-scores/index.njk`.
- `tools/foafnaut-scoreboard.py --history`: a release scoreboard can now read
  this history. It no longer calls the 601-relation score a CPU sampler score:
  that number comes from the browser WASM and WebGPU run.

## Facts to keep

- The 601-relation suite and `native-reftests.py` (279 HTML relations) are two
  suites. They have separate keys: `wpt-images-wasm` and `wpt-images-native`.
- The oracle capture was lost in a restart. `wpt-images-wasm` makes it again in
  each run, and `wpt-images-native` uses that capture. The two suites now use
  Chrome on this Mac as the oracle browser of the day.
- The corpus harness is on branch `codex/svg-corpus-overnight`, and it is older
  than the engine. `run.py` copies its scripts into the run directory and makes
  two edits (`CORPUS_PATCHES`). Without the first edit, all HTML cases fail
  with "Renderer worker failed", because the harness does not serve
  `engine-worker.mjs`. That is a harness fault, not an engine fault. No fixture,
  reference or limit changes. Land PR 310 to remove these edits.
- HarfBuzz test data are not vendored. The run used the 15.0.0 tag archive,
  sha256 `fe4b8bad7afbbae75d61b2095c267c98f4ed04fe4a117680130ed253d2732efe`.
- The fonts of `font-records` are not in the repository. The OKR does not name
  the exact files. The record gives the sha256 of each file used.
- A `TIMEOUT` of `wpt-images-native` means the 5 second limit of the probe. The
  native CPU sampler is slow, so a timeout does not say the page fails.
- Tiny failure groups put each case in one group, the first cause found in
  `TINY_CAUSES`. This is a guide for what to fix. It is not a proof of the cause.

## Regular use

After an engine change: build (`build-web-render.sh --native`, `--wasm`,
`build-engines.sh`), run `tools/render-dashboard/run.py`, and commit the history
and the page. A full run takes about 25 minutes on an M1.
