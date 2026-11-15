---
name: realpages-survey
description: The real-page survey of each Foafnaut release (Wikipedia desktop and mobile skins, BBC News, GitHub, MDN, a blog, Hacker News, a W3C spec, the Spinal Tap showcase), probed live and measured on the native engine; per page a verdict, first frame, first layout, GPU per frame, idle CPU, longest script turn, scroll latency, peak RSS, liberal-mode skips, crash or exit, and layout similarity against headless Chrome. Use before running the survey locally, adding or changing a page or budget, reading the trend, or changing realpages.yml.
---

# The real-page survey

Code: [`labs/demos/foafnaut/realpages/`](../../labs/demos/foafnaut/realpages/). Workflow:
`realpages.yml` in `danbri/factoidal-builds`. Started for issue 450 (is the Spinal Tap page the slow one,
or only the one that renders well enough to be measured?).

## Rules

- **Real pages are copyright.** The survey probes them live at run time. `pages.json` holds URLs only.
  Pictures and logs go to a workflow artifact kept 7 days, or to local scratch; never into git, a release, an
  issue or a PR. Public outputs are numbers, verdicts and defect lists (a defect is described in our own
  words: "mask-image icons drawn as black squares", not a copy of the page).
- **The host is the release's own commit.** `run_html.ts` and Textnaut change with the engine; a newer host
  on an older engine measures the host, not the release (on 2026-11-15 the host of main drew the Spinal Tap
  page at 41 ms GPU per frame on engine cc73af028, against 337 ms with cc73af028's own host). The survey
  tools (`realpages/`) come from main, so an old release is judged by today's rules.
- **Unreachable is not a regression.** A page whose fetch fails (after two more tries, 5 and 10 s apart) is
  `unreachable`. A run that ends by a signal or an error of the browser is a `crash`: a hard failure.

## Run it locally (macOS)

```bash
cd labs/demos/foafnaut
# Once per checkout: the Wasm modules the host imports, and the window library.
gh release download build-<12 hex>-foafnaut-web -R danbri/factoidal-builds -p foafnaut-web.tar.gz -D /tmp/web
mkdir -p /tmp/web/x && tar -xzf /tmp/web/foafnaut-web.tar.gz -C /tmp/web/x docs/web/hub/html-webgpu/runtime
realpages/setup-host.sh "$PWD" /tmp/web/x
# The survey (about 15 min for 15 pages); --only hn,wp-stub for a few.
deno run -A realpages/survey.ts --engine ~/.foafnaut/current/foafnaut/libweb-render.dylib \
  --out /tmp/rp --lock /tmp/foafnaut-timing.lock
deno run --allow-read --allow-write realpages/compare.ts --current /tmp/rp/summary.json [--previous OLD.json]
```

On the shared Mac pass `--lock /tmp/foafnaut-timing.lock` so runs do not overlap other agents' timings. To
measure a release as released, give `--host` a checkout of its commit (sparse: `labs/demos/foafnaut`,
`docs/web/hub/foafnaut`; then `setup-host.sh` on it). Linux: `--platform linux --engine libweb-render.so`
runs Textnaut instead (no window, no Chrome).

## What is measured

macOS, each page: a watch run (`run_html.ts --offscreen --offscreen-size WxH@1 --text-size 100
--be-liberal-in-what-we-accept --perf-summary --shot F --shot-at-end --liberal-report json
--watch-sweep 15`) and a scroll run (`--scroll-sweep --idle-checks-only`), then headless Chrome at the size
of the page area (`--window-size=W,H-top`, iPhone user agent for `mobile` rows).

| Field | Meaning |
|---|---|
| `first_frame_s` | wall time from process start to the first presented frame (about 1.5 s is start-up) |
| `first_layout_ms`, `prims` | layout of the first frame; its primitives |
| `gpu_p50_ms` | GPU submit to done, median (perf summary) |
| `cpu_idle_pct` | process CPU over wall, from the first frame to the end of the 15 s watch, no input |
| `script_turn_max_ms` | the longest script turn (`leanMs`); `scripts_off` says why scripts did not run |
| `scroll_latency_p50_ms`, `_p95_ms` | queued wheel event to present, 20 steps (includes script turns that hold the loop) |
| `rss_peak_mb` | peak resident memory over both runs (ps every 250 ms) |
| `skips` | what liberal mode skipped (System console entries), each once |
| `layout_similarity` | SSIM of the two pictures shrunk to 1/16, flat windows left out (`visual.ts`): HN 0.50, Spinal Tap page 0.61, Wikipedia without its columns 0.12-0.20, a blank page 0.04 |
| `verdict` | `crash`, `timeout` (no frame), `blank` (< 20 primitives), `unusable` (scroll p95 > 5 s or first frame > 60 s), `slow` (first frame > 10 s, scroll p95 > 1 s, idle CPU > 50% or a turn > 5 s), else `usable` |

Linux: `load_ms`, `first_layout_ms`, `rows`, `links`, `first_frame_s` (to the timing line), `cpu_s`,
`rss_peak_mb`, crash or exit; a refusal is `blank`.

`over_budget` lists fields above the budgets in `pages.json` (`defaults.budgets`, a page's own `budgets`
override): goals, not failures.

## Add a page

Add `{"id": "...", "url": "https://..."}` to `pages.json` (optional `viewport`, `mobile`, `scripts: false`,
`scroll: false`, `budgets`, `note`). A page of this lab is `lab:pages/NAME.html`. Pick pages that stay put
(an article, a spec, a repository front page) and say in the PR why the page adds coverage. Never commit the
page. The next survey compares it with nothing; the one after with its first row.

## Read the trend

On `danbri/factoidal-builds`, branch `wpt-scores`, directory `realpages/`: `trend.csv` (one row per run,
platform and page; columns in `compare.ts` `TREND_COLUMNS`), `runs/<run_id>/<platform>.json` (the whole
summary), `latest-<platform>.json` and `previous-<platform>.json` (the newest two releases surveyed). Each
surveyed release has the assets `realpages-<platform>.json` and `realpages-<platform>.md` (the table with
changes). A run's job summary has the same table; its pictures are the artifact `realpages-<platform>-pictures`
for 7 days.

Regressions (`compare.ts`): a crash (fails the job), a worse verdict, a number over 1.5 times the previous
one and above its noise floor (first frame 1 s, layout 50 ms, GPU 10 ms, idle CPU 10 points, script turn
100 ms, scroll 50 ms, RSS 200 MB), layout similarity down by more than 0.05. Unreachable, before or now, is
never a regression.

## Checks

`realpages_test.ts` (pure: log parsing, verdict, PNG decoding and similarity, comparison, the System entry
report) runs in test.sh's pure tests; `realpages_check.ts` (macOS, engine and window library: the two
run_html.ts options and the survey on one lab page, no network) in its engine section.
