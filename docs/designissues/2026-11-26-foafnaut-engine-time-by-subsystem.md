# Foafnaut: where the engine time of a page goes, by subsystem (2026-11-26)

Owner, 2026-11-26, verbatim: "where did we land on this issue? The latest release on mac feels
quite snappy. Probably JS is the thing holding us back now, I would guess." (Issue:
https://github.com/danbri/factoidal-core/issues/1031, engine per tab.) This record measures the
second part: what share of the engine's CPU time is page JavaScript (BubblePopJS), and what the
rest is.

Result: on the three demo pages measured, BubblePopJS is 9 to 21% of the engine's CPU time. The
larger costs are the canvas 2D raster (Particle Rex, 72 to 78%) and page paint, fonts and the
page layer (two DOM pages, 49 to 74%). On those DOM pages, the largest single JavaScript cost is
the script start turn (parse and first run), 227 and 437 ms. Pages with much more script than
these were not measured (section 4).

## 1. Method

- Rig: Linux cloud VM, 4 vCPU, no GPU (Mesa llvmpipe, a software Vulkan), Xvfb 1280x900. Engine
  library built from `main` `48aa98e6`. Host `run_html.ts` of `main` `994dd4ad` (the host
  commits after `48aa98e6` change Tor and the Wasm import only).
- Each page: `--watch-sweep 8 --log-all --perf-summary --engine-mode tasks`, no input. Particle
  Rex shows its title screen, which animates.
- Profile: `perf record -e cpu-clock -F 199 --call-graph dwarf,16384 -k CLOCK_REALTIME`
  (`/usr/lib/linux-tools-6.8.0-151/perf`), one run per page. `tasks` mode, because DWARF
  unwinding reads the library file and `copies` mode deletes its copies. The engine code is the
  same in every mode.
- Report: `labs/demos/foafnaut/tools/engine_time_split.py`. Each sample with a frame of the
  engine library goes to the nearest Lean namespace on its stack: allocation, reference counts,
  libc and the kernel go to their Lean caller; a generic List or Array function goes to its
  nearest named caller. Window `timers` (from 0.5 s after the first timer turn to the last one)
  for the animating page; `all` (the whole run, page load included) for the others. The trace's
  clock and perf's agree to 14 to 16 ms (quit record against the main thread's last sample).
- Plain runs (no profiler) of Particle Rex in `copies` and `tasks` mode give the turn times.

## 2. Results

Particle Rex (`pages/particle-rex.html`, title screen):

| Number | `copies`, no profiler | `tasks`, no profiler | `tasks`, profiled |
|---|---|---|---|
| Timer turns a second | 22.4 | 24.3 | 26.0 |
| Engine time a turn, p50 and p95, ms | 35.7, 49.9 | 34.9, 46.7 | 34.0, 48.3 |
| Engine busy (sum of turn times over the window) | 0.87 | 0.90 | 0.95 |

A turn runs about 2,175 BubblePopJS instructions (p50), sends 26 commands to the host and uploads
the whole canvas (1.39 MB, host replay 7 to 8 ms on the main thread). The engine is busy 87 to 95% of
the time, so the engine turn sets the frame rate on this VM.

Engine CPU by subsystem (share of the engine's samples):

| Subsystem | Particle Rex, animating (7.1 s of engine CPU) | Particle Rex, whole run (8.3 s) | spinal-tap-sparql, whole run (3.1 s) | foaf-explorer, whole run (1.6 s) |
|---|---|---|---|---|
| Canvas 2D raster (`L4Factoidal.PageCanvas`) | 78.3% | 71.6% | 0 | 0 |
| BubblePopJS (`L4Factoidal.JS`) | 17.0% | 20.7% | 9.1% | 14.5% |
| Page paint: pieces and tiles (`NativeSVG*`, `NativeGraphics`) | 0 | 0.4% | 44.8% | 24.9% |
| Fonts and text (`Rendering.Sfnt*`) | 0 | 0.8% | 16.7% | 11.4% |
| Page layer (`WebDocument`, `WebRender`, `WebPaint`) | 0.5% | 0.9% | 12.7% | 12.6% |
| CSS | 0 | 0 | 4.4% | 9.8% |
| Layout | 0 | 0 | 1.6% | 4.4% |
| DOM (`L4Factoidal.DOM`) | 0 | 0 | 0.5% | 2.2% |
| Other (frame JSON, Unicode tables, geometry, frame cost cache) | 3.6% | 4.1% | 6.8% | 15.8% |

The two DOM pages: `spinal-tap-sparql.html` has 75 KB of script in 16 scripts; its start turn
took 437 ms (12,793 instructions, 1 layout), its 37 timer turns 0.6 ms each (p50), its 31 frames
166 ms each (p50 of the whole frame). `foaf-explorer.html` has 21 KB of script; start turn 227 ms
(10,027 instructions), 47 timer turns 0.8 ms each, 36 frames 110 ms each.

Inside Particle Rex's canvas raster (inclusive shares of its samples; they overlap): coverage
(`coverageIn`, `rowSums`) 46%, source-over composite (`compositeOver`, `overSpan`) 30%, `drawImage`
21%. A third of the raster's samples have a runtime function as the leaf; the largest are
`lean_float_array_push` (9%), `mi_malloc_small` (8%) and `mi_free` (6%).

Whole process, the DOM pages: the software GPU (llvmpipe threads) took 19.4 s of CPU on
`spinal-tap-sparql` (6.3 times the engine) and 13.2 s on `foaf-explorer` (8.3 times). On a Mac
this is GPU work; these numbers do not say what it costs there.

## 3. Reading

1. On these pages, page JavaScript is not the largest cost of the engine. To remove all
   BubblePopJS time from a Particle Rex turn would make it at most 17% shorter (34 to about 28
   ms); the raster is 78% of it. The raster work is tracked in
   https://github.com/danbri/factoidal-core/issues/1098 (canvas 2D game frame rate).
2. On the DOM pages, the start turn is the JavaScript cost a person sees (227 and 437 ms before
   the page's script has run). Later timer turns are under 1 ms.
3. The engine CPU of the DOM pages is mostly page paint, fonts and the page layer.

## 4. What this does not show

- Pages with much more script (frameworks, everyday sites). There, the speed of BubblePopJS
  counts for more of the time: on the library corpus of `bubblepop_perf/realworld.py` it executes
  4 to 21 times the instructions of QuickJS-NG
  ([2026-11-16-lean-memory-overhead.md](2026-11-16-lean-memory-overhead.md)), and its JIT work is
  https://github.com/danbri/factoidal-core/issues/471. The realpages survey (factoidal-builds,
  branch `wpt-scores`, `realpages/trend.csv`) measures script turns on everyday pages; it was not
  read for this record.
- Particle Rex in play: issue 1098 reports a turn p50 of 76 to 91 ms in play, against 34 ms on
  the title screen here. The shares in play were not measured.
- The Mac: no Mac run. A Mac has a GPU and faster cores; the shares can differ.
- One profiled run per page. With 317 to 1,408 engine samples, a share near 15% has a sampling
  spread of about 1 to 2 points.

## 5. Repeat

```
perf record -e cpu-clock -F 199 --call-graph dwarf,16384 -k CLOCK_REALTIME -o run.data -- \
  deno run --no-check --no-config --no-npm --node-modules-dir=none --unstable-webgpu --unstable-ffi -A \
  run_html.ts --native-engine libweb-render.so --no-splash --no-state --perf-summary --log-all \
  --engine-mode tasks --html pages/particle-rex.html --watch-sweep 8 > trace.log
perf script -i run.data -F comm,pid,tid,time,ip,sym,dso > run.script
python3 tools/engine_time_split.py --trace trace.log --script run.script \
  --library libweb-render.so [--window all]
```

A run with `--steps` and the step `mark` does not suit an animating page: the host quit 0.3 s
after the first mark, and Particle Rex made one timer turn in that run. Use `--watch-sweep`.
