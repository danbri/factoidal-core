# Presenter timing protocol — 2026-11-17

The existing `--scroll-sweep` issues `native.testEvent` from the main loop. If that loop
stalls, it issues the next event late. Queue-to-present latency then omits the time before
injection. The existing sweep remains a pixel/cost oracle, but it cannot by itself establish
busy-engine input responsiveness.

`presenter_timing.ts` runs both presenter modes on one engine hash and source tree, under
`/tmp/foafnaut-timing.lock`. It runs one warm-up of each mode followed by five or more
interleaved inline/worker pairs for each scenario. Defaults: the offline `w3c-flexbox`,
`wp-spinal` and `wp-us` snapshots, each with scripts disabled and with an original bounded
script workload injected into the replayed input; plus an original synthetic long page.
The busy snapshots retain their existing scripts too. This is recorded as a modified test
input, not the unmodified real page.

The benchmark-only preload wraps `ng_next_event`. After the first successful frame it
sets 120 fixed scroll deadlines, 16 ms apart, starting 1.5 s later. Each scroll moves two
rows down, aiming to stay within the rastered band. The deadline is on `ng_event_clock`,
which the host already maps to `performance.now()`. An overdue event retains its deadline.
This avoids unsafe writes to the native window's unsynchronised queue from another thread.
It also includes stalls before the main loop can take input.

These results must be labelled **scheduled input to off-screen present return**, not device
latency or native enqueue latency. The operating system's input queue, display compositor
and panel are not measured. The fixed schedule also differs from the existing sweep's
wait-for-settlement schedule. The two measurements must not be compared as one series.

For the busy result, input epochs must overlap a measured script-session execution longer
than 50 ms. The host trace must supply `inputEpochMs` from the original input stamp, and
engine execution records must supply `startEpochMs` and `endEpochMs` on the same clock
(`performance.timeOrigin + performance.now()`). If only the older `leanMs` plus completion
trace is available, the harness records an inferred interval but marks the busy result
invalid. Message delivery delay otherwise creates a false overlap. A run also fails for
missing summaries, lost input samples, dropped events, a timeout or a nonzero process exit.

The idle condition disables scripts; resource completion and layout can still occur. The
raw execution trace must be checked before describing that condition as a fully idle engine.

Example, from the repository root:

```sh
deno run -A labs/demos/foafnaut/presenter_timing.ts \
  --engine /path/to/libweb-render.dylib \
  --snapshots /path/to/factoidal-builds/third_party/realpages \
  --out /tmp/presenter-timing
```

Each run keeps its command, environment, raw log, samples and validity reasons. The summary
gives pooled count/p50/p95/p99/max and median/worst/CV of each run's p95. It never averages
percentiles. Engine/source hashes, revision, working-tree status, machine load, power and
thermal reports are retained. The harness kills only its own child on the time limit.

Validation so far: both timing modules pass `deno check --no-config`; the three aggregation
and trace-parsing tests pass. A locked smoke run stopped before drawing: Deno reported no GPU adapter in this
launch context (exit 2, 0/120 input samples). No valid timing comparison has been made.
Neither performance gains nor execution-overlap results are claimed.

The inline baseline retains the existing engine worker, GPU raster and host offset
arithmetic. The checked-in code already uses an engine worker, despite the design table
describing a fully synchronous stage 0. The comparison must preserve that actual baseline.
Snapshot and busy-script hashes are recorded with the inputs; full logging retains the
engine execution epochs needed to validate overlap.
