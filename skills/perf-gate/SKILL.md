---
name: perf-gate
description: Foafnaut's performance gate. Original fixtures made by a committed generator (labs/demos/foafnaut/fixtures/perf), the one-sample harness tests/browser-wpt/perf-run.ts, the BubblePopJS page benchmarks (js_perf_bench.ts), and the cloud job (factoidal-builds perf.yml, a job in every Branch WPT check and every full run of main) that FAILS a branch when an exact counter or a wall time rises past the margins stated here, and records perf.csv on wpt-scores. Use before merging engine work, when the perf job fails, when you add a fixture or change a margin, or before quoting a speed number.
---

# The performance gate

On 2026-11-14 real pages became 2 to 15 times slower within one day and no check failed
(core issue 438). Since then **a slowdown does not merge**: every Branch WPT check runs this
gate, and a branch whose perf job fails is not merged until the cause is fixed or the cost is
accepted on purpose (section 5).

## 1. What is measured

Fixtures: `labs/demos/foafnaut/fixtures/perf/`, all written by `make_fixtures.py` (own PRNG,
invented words, no text or markup from any site). `manifest.json` gives each fixture's size and
the SHA-256 of every file; `set_sha256` names the fixture set, and rows of two sets are never
compared. The PNG files are not committed (the lab ignores `*.png`): `make_fixtures.py --png`
writes them, `--check` verifies the whole set (the driver does both before every run).

| fixture | what | scripted |
|---|---|---|
| `cascade` | 3,000 elements of short text, 2,000 rules (class, descendant, child, `:not()`, `:hover`, `:first-child`, `[data-x]`, `var()`): the cascade, not text | no |
| `article` | a long article, 3,000 elements, 2,000 rules with `@media` blocks, custom properties, `::before` | no |
| `longtext` | about 41,500 words in 60 sections, four rules: shaping and line breaking | no |
| `table` | 100 rows of 20 cells and a header row | no |
| `cards` | 500 cards: a grid of flex columns with flex rows | no |
| `images` | 34 PNG images (three sizes), 6 SVG files, 4 inline SVG | no |
| `form` | 240 controls in 12 fieldsets; a script fills and validates them | yes |
| `script` | 10 module scripts, a keyed reconcile loop over 400 items, 24 rounds, about 21,000 DOM calls, layout reads between rounds | yes |
| `reads` | 1,000 layout reads with nothing changed between (one layout is enough), then 40 write-and-read pairs (one layout each) | yes |
| `domloop` | a loop of DOM calls: 2,000 elements made, attributed, appended, queried, restyled by class, half removed | yes |
| `js-*` | the BubblePopJS page benchmarks of `labs/demos/foafnaut/bubblepop_perf/page/` (props, closures, strings, json, dom, reconcile, modules) by `js_perf_bench.ts` | yes |

One sample is one new process (`tests/browser-wpt/perf-run.ts`): the page is loaded as the
browser loads it (`prepareHTML` of the engine's own host sources, sheets, images and scripts over
HTTP from a loopback server, page scripts on BubblePopJS, Noto Sans), laid out at 1280x800, the
scripts settled (virtual time), laid out again, and laid out at 1024 wide. Every engine call is
timed; host work (fetching, JSON) is not in the engine times.

Metrics of a sample:

- **Exact counters** (the same on every run of one engine; they do not flake): `frame_layouts`
  (frameWork layouts), `script_layouts` (layouts that script reads forced), `script_instructions`
  (BubblePopJS steps), `script_jobs`, `script_tasks`, `engine_calls` (calls into the engine
  library), `js_steps` (steps of each benchmark).
- **Times** (ms): `first_layout_ms`, `settled_layout_ms`, `resize_layout_ms`, `script_ms` (start
  and settle turns), `engine_ms` (all engine calls), `js_ms` (each benchmark's turn less an empty
  page's).
- **Recorded only**: `primitives`, `settled_primitives`, `dom_changes`, `dom_calls`, `parse_ms`,
  `domcall_us` (per-call DOM times, a difference of two loops: too noisy to gate). Primitives and
  DOM changes are output, not cost: a rendering fix may change them.

Not measured yet (no counter in the engine): cascades per layout, styled elements, words shaped.
They are wanted: a counter in `frameWork` for each would let the gate see a cascade or shaping
regression exactly instead of by wall time.

## 2. The margins (the failing condition)

Head = the branch's engine; base = the newest Linux engine release of a main commit that the
branch contains. Both run on the same runner, three samples each, interleaved (base, head, head,
base, ...); medians compared.

- `frame_layouts`, `script_layouts`: **any rise fails**.
- Other counters (`script_instructions`, `script_jobs`, `script_tasks`, `engine_calls`,
  `js_steps`): a rise of **more than 2 %** fails.
- Times: fails only when all three hold: the head median is **more than 1.30 times** the base
  median, **more than 30 ms** above it, and **the fastest head sample is slower than the slowest
  base sample**.
- A fixture valid on the base and not valid on the head (load failed, scripts did not report
  that they finished, fewer DOM calls than stated) fails.
- A fixture not valid on the base is not compared (the report says so).

These numbers are in `release-tests/perf.py` of factoidal-builds (`COUNTER_PCT`, `TIME_RATIO`,
`TIME_MS`, `COUNTER_ZERO`). Change both places together. The margins live in the builds
repository so that a branch cannot loosen the gate that judges it.

## 3. Where it runs

- **Branch WPT check** (`branch-wpt.yml`): job `Performance gate`, beside the tests, after the
  build. Red = slower. The job summary has the table; artifact `perf-gate-branch` has
  `samples.jsonl`, `summary.json`, `report.md`.
- **Full runs of main** (`release-tests.yml`): job `Performance record` for each Linux run.
  Rows go to `perf.csv` on the branch `wpt-scores` (one row a fixture and metric: median, min,
  max, samples, kind; `invalid` rows say why). The job summary shows the change since the
  previous main engine, as a warning, not a failure.
- **By hand / backfill**: `gh workflow run perf.yml --repo danbri/factoidal-builds -f
  engine_tags=<12 hex>,<12 hex>` records those main engines.

Cost: one Linux runner, about 10 to 20 minutes for two engines.

## 4. Locally (macOS)

```sh
# engines: build-<12 hex>-foafnaut-engine-darwin-arm64 releases; host sources of the same commit
git archive <commit> labs/demos/foafnaut docs/web/hub/foafnaut | tar -x -C /tmp/host-<commit>
python3 ../factoidal-builds/release-tests/perf.py run --core . \
  --engine base=<base dylib>:/tmp/host-<base> --engine head=<head dylib>:/tmp/host-<head> \
  --out /tmp/perf --font third_party/fonts/noto-sans/NotoSans-Regular.ttf
python3 ../factoidal-builds/release-tests/perf.py compare --summary /tmp/perf/summary.json --out /tmp/perf
# one sample, one fixture:
deno run -A --unstable-ffi tests/browser-wpt/perf-run.ts --engine <lib> --host <host>/labs/demos/foafnaut \
  --fixture cascade --font third_party/fonts/noto-sans/NotoSans-Regular.ttf
```

The driver writes a stand-in for the Wasm runtime module that the host sources import
(`.build/native-html/runtime/web-render.mjs`): the harness runs the native library only. The
shared Mac is loaded by other agents: local times are for diagnosis, the cloud job decides.

## 5. When the gate fails

1. Read the summary: which fixture, which metric. A counter rise is exact: run that fixture
   locally with both engines and find the change (`script_layouts` up = a read that lays out
   again; `script_instructions` up = more script work per call, often the prelude).
2. Fix it, or, when the cost is wanted (a feature that must do more work), dispatch the check
   again with `-f perf_allow=<fixture>.<metric>,...`. The rise is then listed as accepted, the
   job passes, and the merge note must state the accepted cost with its numbers.
3. A new fixture or a generator change changes `set_sha256`: base and head still run the same
   (the branch's) fixture files, so the comparison stays valid.

## 6. Adding a fixture

Add a function to `make_fixtures.py` (original text from `word`/`sentence`, its own seed), add
it to `build()`, run the generator, commit the text files and the manifest. Scripted fixtures
log `perf-fixture-done {json}` when finished (and `domCalls` when the manifest states
`dom_calls_at_least`). Keep one sample under about 15 s on a cloud runner: the job runs every
fixture six times.

## 7. Baseline numbers

See core issue 444 for the first recorded numbers and `perf.csv` on `wpt-scores` for the
series.
