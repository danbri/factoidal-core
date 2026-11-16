---
name: perceived-performance
description: How fast Foafnaut feels to a person, as opposed to how fast a benchmark says it is. Principles from the research on perceived speed (response-time limits, input latency, frame pacing, waiting, variance, flicker, haptics), each with its evidence and a grade; a catalogue of Foafnaut metrics mapped to perception, with how to measure each in the native window, the Hub and Textnaut and what is missing; target thresholds with their justification; workflows for setting a goal over an existing or new time series, reading distributions and tails, A/B runs under the timing lock, and ratcheting. Use when setting or reviewing a speed or responsiveness goal, adding or changing a timing metric, budget or trend column, judging whether a timing change is an improvement, writing the timings of a hand-back, or working on typing, pointer, scroll, first paint, jank, flicker or idle cost.
---

# Perceived performance

A mean that got smaller is not the same as a browser that feels faster. People judge speed by the first sign of
a response, by how tightly the screen follows their hands, by the worst moments, and by whether the delay is the
same each time. This skill says what the research supports, which Foafnaut numbers stand for which perception,
what the targets are, and how to set and keep a goal.

Related skills: [`perf-benchmarking`](../perf-benchmarking/SKILL.md) (how to take a timing at all),
[`realpages-survey`](../realpages-survey/SKILL.md) (the real-page runs and their trend),
[`foafnaut`](../foafnaut/SKILL.md) (code map), [`wpt-runs`](../wpt-runs/SKILL.md).

## Rules

1. Report a distribution, never only a mean or a median: count, p50, p95, p99 (when the count is 100 or more), max.
2. Report spread across runs: at least 5 runs for a claim of improvement, with median, worst and coefficient of
   variation (CV, standard deviation over mean).
3. A regression in a tail (p95, p99, max, worst of N) is a regression, whatever the median did.
4. Name the end points of every latency: from which stamp (device event, enqueue, dequeue) to which (engine done,
   `present()` returned, shown on the display). A number without end points cannot be compared.
5. Timing runs take the timing lock, and both sides of an A/B run on the same machine, in the same session,
   interleaved.
6. A target cites its evidence and the evidence grade. Folklore may guide a design; it does not set a budget.
7. Perceptual tricks (progress display, placeholders) come after the real latency work, and never as engine
   behaviour that changes what a page does. The browser's own chrome may use them.

## Evidence grades

- **Solid**: controlled studies, replicated or consistent across several groups.
- **Moderate**: one controlled study, or large field data from one organisation.
- **Guideline**: a vendor's or standards body's threshold, with stated reasoning but little published data.
- **Folklore**: widely repeated, with no controlled evidence found in this review.

## Principles and their evidence

### 1. Three time scales, not three exact numbers

About 0.1 s feels immediate, about 1 s keeps the flow of thought, about 10 s is the limit of attention. The
numbers come from [Miller 1968, "Response time in man-computer conversational transactions" (doi:10.1145/1476589.1476628)](https://doi.org/10.1145/1476589.1476628)
and [Card, Robertson and Mackinlay 1991, "The information visualizer" (doi:10.1145/108844.108874)](https://doi.org/10.1145/108844.108874),
made popular by [Nielsen, "Response times: the 3 important limits"](https://www.nngroup.com/articles/response-times-3-important-limits/).
Miller's figures were expert estimates for different kinds of transaction, not experiments.
[Shneiderman 1984 (doi:10.1145/2514.2517)](https://doi.org/10.1145/2514.2517) reviews the early experiments;
[Dabrowski and Munson 2011, "40 years of searching for the best computer system response time" (doi:10.1016/j.intcom.2011.05.008)](https://doi.org/10.1016/j.intcom.2011.05.008)
concludes that no single number holds across tasks. Grade: the orders of magnitude are solid, the exact limits
are folklore.

- Discrete actions tolerate more than continuous ones. For key presses and mouse clicks on a 2001 desktop, people
  did not notice delays of about 150 ms and 195 ms:
  [Dabrowski and Munson 2001, "Is 100 milliseconds too fast?" (doi:10.1145/634067.634255)](https://doi.org/10.1145/634067.634255).
- For page loads, people in an experiment were willing to wait about 2 s without feedback, longer with it:
  [Nah 2004 (doi:10.1080/01449290410001669914)](https://doi.org/10.1080/01449290410001669914). See also
  [Galletta et al. 2004 (doi:10.17705/1jais.00044)](https://doi.org/10.17705/1jais.00044) and
  [Bouch, Kuchinsky and Bhatti 2000 (doi:10.1145/332040.332447)](https://doi.org/10.1145/332040.332447).
- [Attig et al. 2017, "System latency guidelines then and now" (doi:10.1007/978-3-319-58475-1_1)](https://doi.org/10.1007/978-3-319-58475-1_1)
  reviews the later work and finds the 100 ms guideline too lax for continuous input.

### 2. Continuous input needs far less than 100 ms

When the screen follows a moving finger, pen or pointer, people see the gap as a distance, and they see small
gaps. Grade: solid.

- Direct touch: with a rig that went down to about 1 ms, people preferred lower latency and kept noticing
  improvement well below 10 ms:
  [Ng et al. 2012, "Designing for low-latency direct-touch input" (doi:10.1145/2380116.2380174)](https://doi.org/10.1145/2380116.2380174);
  the same group's [demonstration video](https://www.youtube.com/watch?v=vOvQCPLkPt4).
- Pointing performance falls as touch latency rises:
  [Jota et al. 2013, "How fast is fast enough?" (doi:10.1145/2470654.2481317)](https://doi.org/10.1145/2470654.2481317).
- Direct and indirect devices, tapping and dragging compared in one study, with dragging the more sensitive task
  and indirect input (a pad or mouse, eyes on the screen) more forgiving than direct touch:
  [Deber et al. 2015, "How much faster is fast enough?" (doi:10.1145/2702123.2702300)](https://doi.org/10.1145/2702123.2702300).
  Later summaries give its indirect thresholds as about 55 ms for dragging and 96 ms for tapping, and say that
  improvements of about 8 ms (one 120 Hz frame) were noticed; this review read the abstract, not the full text.
- Stylus: [Ng et al. 2014, "In the blink of an eye" (doi:10.1145/2556288.2557037)](https://doi.org/10.1145/2556288.2557037).
- Mouse: at 225 ms of lag, movement time rose 64% and errors 214%:
  [MacKenzie and Ware 1993 (doi:10.1145/169059.169431)](https://doi.org/10.1145/169059.169431). Latency and
  spatial jitter both hurt pointing:
  [Pavlovych and Stuerzlinger 2009 (doi:10.1145/1570433.1570469)](https://doi.org/10.1145/1570433.1570469),
  [Teather et al. 2009 (doi:10.1109/3DUI.2009.4811204)](https://doi.org/10.1109/3DUI.2009.4811204).
- End-to-end pointer latency differs between toolkits and browsers, and rises with system load:
  [Casiez et al. 2015, "Looking through the eye of the mouse" (doi:10.1145/2807442.2807454)](https://doi.org/10.1145/2807442.2807454).

### 3. Typing: the effect shows in effort and in editing

The one controlled typing study found: 31 people, 20 ms against 200 ms from key to glyph. Copy-typing speed did
not change; correcting text was slower; frustration and effort were higher; fast typists noticed more:
[Schmid et al. 2023, "Effects of text input latency on performance and task load" (doi:10.1145/3626705.3627784)](https://doi.org/10.1145/3626705.3627784).
Grade: moderate (one study, two latency levels; the threshold between 20 and 200 ms is not measured).

Measurements of real machines: key press to screen is 30 to 200 ms on desktops, and the machines of 1977 to 1983
beat most modern ones: [Dan Luu, "Computer latency: 1977-2017"](https://danluu.com/input-lag/); the keyboard
alone can take 15 to 60 ms: [Dan Luu, "Keyboard latency"](https://danluu.com/keyboard-latency/); terminals:
[Dan Luu, "Terminal latency"](https://danluu.com/term-latency/); editors:
[Pavel Fatin, "Typing with pleasure"](https://pavelfatin.com/typing-with-pleasure/); a survey with an informal
budget: [Ink & Switch, "Slow software"](https://www.inkandswitch.com/slow-software/). These are careful
measurements of latency, not studies of perception. What follows for us: hardware and the display already spend
30 to 60 ms, so the browser's share has to be about one frame.

### 4. Smoothness is the worst frames, not the average rate

Grade: solid for "variation and spikes are seen", guideline for the exact thresholds.

- Frame-time variation of 12 ms lowered rated smoothness; 4 ms had little effect; play performance did not change
  between conditions rated equally smooth:
  [Klein et al. 2024, "Variable frame timing affects perception of smoothness in first-person gaming" (doi:10.1109/cog60054.2024.10645568)](https://doi.org/10.1109/cog60054.2024.10645568).
- Single long frames (225 and 675 ms) lowered rated smoothness and score, more than graphics quality did:
  [Tokey et al. 2026, "Impact of graphical fidelity and frame-time stutter in a first-person shooter game" (doi:10.1145/3804493)](https://doi.org/10.1145/3804493).
- Frame rate itself matters up to a point: 60 fps gave 14% better moving-target selection than 30 fps; 45 against
  60 was not significant: [Janzen and Teather 2014 (doi:10.1145/2559206.2581214)](https://doi.org/10.1145/2559206.2581214);
  [Claypool and Claypool 2007 (doi:10.1007/s00530-007-0081-1)](https://doi.org/10.1007/s00530-007-0081-1).
- Chromium rejects average fps for a percentage of dropped frames, reported as the average, the worst 1 s window
  and the 95th percentile of 1 s windows, with partial frames counted:
  [web.dev, "Towards an animation smoothness metric"](https://web.dev/articles/smoothness).
- Apple measures hitch time per second of animation: at or below 10 ms/s good, 25 warning, 50 critical:
  [Apple, "Understanding hitches in your app"](https://developer.apple.com/documentation/xcode/understanding-hitches-in-your-app).
- Android: a frame over 16 ms is slow, over 700 ms frozen ("no frame should ever take longer than 700 ms"):
  [Android, "Slow rendering"](https://developer.android.com/topic/performance/vitals/render);
  [JankStats](https://developer.android.com/topic/performance/jankstats).

### 5. Unpredictable delay costs more than its mean suggests

Grade: moderate for interactive software, solid in the general psychology of waiting.

- With simulated office software, fewer distinct response times made people faster, although the mean delay was
  longer, and rated experience did not fall:
  [Weber, Haering and Thomaschke 2013, "Improving the human-computer dialogue with increased temporal predictability" (doi:10.1177/0018720813475812)](https://doi.org/10.1177/0018720813475812);
  [Thomaschke and Haering 2014 (doi:10.1016/j.ijhcs.2013.12.004)](https://doi.org/10.1016/j.ijhcs.2013.12.004).
- People used to a fast system notice an added delay sooner than people used to a slow one:
  [Arapakis, Bai and Cambazoglu 2014 (doi:10.1145/2600428.2609627)](https://doi.org/10.1145/2600428.2609627).
  Getting faster raises the bar for consistency.
- A system made of many parts shows its tail to most users: [Dean and Barroso 2013, "The tail at scale" (doi:10.1145/2408776.2408794)](https://doi.org/10.1145/2408776.2408794).
  A page view is hundreds of frames and dozens of turns, so the p99 frame is seen on almost every page.
- Remembered experience follows the worst moment and the end, not the average:
  [Kahneman et al. 1993 (doi:10.1111/j.1467-9280.1993.tb00589.x)](https://doi.org/10.1111/j.1467-9280.1993.tb00589.x).
  This is an analogy from another field, not a result about software.
- A counter-result worth knowing: [Myers 1985 (doi:10.1145/317456.317459)](https://doi.org/10.1145/317456.317459)
  did not find a significant preference for constant over variable response time.

### 6. Waiting: perceived time is not clock time

- Satisfaction falls roughly with the logarithm of the wait, so halving a long wait buys what halving a short one
  does: [Egger et al. 2012, "Waiting times in quality of experience for web based services" (doi:10.1109/QoMEX.2012.6263888)](https://doi.org/10.1109/QoMEX.2012.6263888),
  [Egger et al. 2012, "Time is bandwidth?" (doi:10.1109/icc.2012.6363769)](https://doi.org/10.1109/icc.2012.6363769).
  Grade: moderate.
- People prefer a progress indicator: [Myers 1985 (doi:10.1145/317456.317459)](https://doi.org/10.1145/317456.317459).
  The way a bar moves changes the perceived duration:
  [Harrison et al. 2007, "Rethinking the progress bar" (doi:10.1145/1294211.1294231)](https://doi.org/10.1145/1294211.1294231);
  backwards-moving, decelerating ribbing cut perceived duration by 11%:
  [Harrison, Yeo and Hudson 2010, "Faster progress bars" (doi:10.1145/1753326.1753556)](https://doi.org/10.1145/1753326.1753556).
  Grade: moderate.
- Uncertain and unexplained waits feel longer: [Maister 1985, "The psychology of waiting lines"](https://davidmaister.com/articles/the-psychology-of-waiting-lines/).
  These are propositions from service management, not experiments.
- Field data: 100 to 400 ms added to search results cut searches per user by 0.2% to 0.6%, and the loss outlasted
  the delay: [Brutlag 2009, "Speed matters for Google web search"](https://services.google.com/fh/files/blogs/google_delayexp.pdf).
  Grade: moderate (one organisation). The revenue-per-100-ms figures quoted from conference talks are unpublished.
- Skeleton screens ([Wroblewski 2013, "Avoid the spinner"](https://www.lukew.com/ff/entry.asp?1797)): the one
  controlled study found no significant difference from a spinner in perceived speed, and slower task time:
  [Mejtoft, Långström and Söderström 2018 (doi:10.1145/3232078.3232086)](https://doi.org/10.1145/3232078.3232086).
  Grade: folklore.
- Optimistic UI, prefetch on intent and animation easing: common practice, no controlled evidence found in this
  review. Animation lengths of 100 to 500 ms are a guideline:
  [NN/g, "Animation duration"](https://www.nngroup.com/articles/animation-duration/),
  [Material 3 motion tokens](https://m3.material.io/styles/motion/easing-and-duration/tokens-specs).

### 7. The web's own metrics rest on the same sources

- [RAIL](https://web.dev/articles/rail): respond within 100 ms (so handle input within 50 ms), produce a frame in
  about 10 ms of a 16 ms slot, idle work in 50 ms pieces, interactive in 5 s. The 50 ms piece is the
  [Long Tasks](https://www.w3.org/TR/longtasks-1/) limit; see also
  [Long Animation Frames](https://w3c.github.io/long-animation-frames/) and
  [Event Timing](https://www.w3.org/TR/event-timing/).
- [Core Web Vitals](https://web.dev/articles/vitals) at the 75th percentile of visits:
  [LCP](https://web.dev/articles/lcp) 2.5 s, [INP](https://web.dev/articles/inp) 200 ms,
  [CLS](https://web.dev/articles/cls) 0.1. Their derivation,
  [web.dev, "How the Core Web Vitals metrics thresholds were defined"](https://web.dev/articles/defining-core-web-vitals-thresholds),
  cites Miller and Card for LCP and Kaaresoja for INP, then relaxes each to what 10% of sites could reach: the
  research said 100 ms for interaction, the threshold is 200 ms. CLS 0.1 comes from Chrome's unpublished internal
  tests. Grade: guideline. They are thresholds for sites of varying quality on varying devices; an engine should
  aim at the research figure, not the relaxed one.

### 8. Feedback in other senses, flicker, and motion

- Press feedback: perceived quality of a touchscreen button fell between 70 and 100 ms for tactile and audio
  feedback and between 100 and 150 ms for visual, and was very low at 300 ms:
  [Kaaresoja, Brewster and Lantz 2014 (doi:10.1145/2611387)](https://doi.org/10.1145/2611387). Grade: moderate.
  Platform guidance: [Android haptics design principles](https://developer.android.com/develop/ui/views/haptics/haptics-principles),
  [Apple, "Playing haptics"](https://developer.apple.com/design/human-interface-guidelines/playing-haptics).
- Layout shift and flashes: CLS as above; content that jumps under the pointer causes wrong clicks.
  [Scroll anchoring](https://drafts.csswg.org/css-scroll-anchoring/) keeps the reading position when content
  above it changes size. [`font-display`](https://developer.mozilla.org/en-US/docs/Web/CSS/@font-face/font-display)
  sets the trade between invisible text and a font swap. No more than three flashes in a second:
  [WCAG 2.3.1](https://www.w3.org/WAI/WCAG22/Understanding/three-flashes-or-below-threshold.html) (a safety limit).
- Reduced motion: [`prefers-reduced-motion`](https://drafts.csswg.org/mediaqueries-5/#prefers-reduced-motion) and
  [WCAG 2.3.3](https://www.w3.org/WAI/WCAG22/Understanding/animation-from-interactions.html). For these users a
  transition is a cost, not a comfort.
- Pointer: the operating system moves its own cursor on a display plane, ahead of any application frame. An
  application that draws its own cursor adds its whole frame latency to the most sensitive continuous input.
  Grade: engineering reasoning; no controlled comparison found. Momentum scrolling belongs to the platform for
  the same reason: people know its curve.
- Heat and battery: a throttled or low-power device lowers frame rate and timer rates, so the same build feels
  slower after ten minutes of high CPU: [WebKit, "How web content can affect power usage"](https://webkit.org/blog/8970/how-web-content-can-affect-power-usage/),
  [Android thermal API](https://developer.android.com/games/optimize/adpf/thermal),
  [Apple `ProcessInfo.thermalState`](https://developer.apple.com/documentation/foundation/processinfo/thermalstate-swift.enum).
  Idle cost is therefore a perceived-speed metric. Grade: guideline.

## Metric catalogue

Paths are under [`labs/demos/foafnaut/`](../../labs/demos/foafnaut/) unless stated. "Window" is the native window
(`run_html.ts` with `native_window.m`), "Hub" the web host in `docs/web/hub/foafnaut/`.

| Perception | Metric | Measured today | Missing |
|---|---|---|---|
| "It started" | first frame after navigation | Window: `native-html-splash{ms}`, survey `first_frame_s`, `first_layout_ms`; `spinal_bisect.ts --app` `first_frame_ms`; Hub: `hub_boot_breakdown.mjs --runs N`; Textnaut `--timing` (`start`, `load`, `layout`, `cells`) | first frame with page content (first contentful frame) and largest-content frame as separate stamps; not in `--perf-summary` |
| "It answers my keys" | key to present | Window: `--perf-summary` `inputLatency{from,count,p50Ms,p95Ms,maxMs}`, per-event `native-html-input-latency{kind,ms,frame,from}`; `press{overlay,frame}` | no typing sweep (keys into a text field at a human rate); text input events (kind 9) are not stamped; no p99; end point is `present()` returning, not display time |
| "The pointer is attached" | pointer move and hover to present | cursor is the system cursor (`NSCursor`), so the arrow itself is as fast as the platform; theorem `hover_never_layouts` | pointer-move events (kind 3) are not stamped: hover feedback and drag latency are unmeasured |
| "Clicks land" | pointer down/up to present | Window: `inputLatency` (kinds 2 and 4); Hub: `inputToFrameMs` with `?stats=1` | split by kind in the summary; Hub start stamp is the `postMessage` send, not the DOM event time |
| "Scrolling sticks to my hand" | scroll event to present | Window: `scrollPresents{count,totalMsP50,totalMsP95,maxMs}`, `--scroll-sweep`, `--scroll-end-sweep`; survey `scroll_latency_p50_ms`, `scroll_latency_p95_ms`; theorems `scroll_in_band_free`, `scroll_never_layouts` | p99; momentum-phase events measured separately from finger-driven ones; touch on the Hub |
| "It is smooth" | frame-time distribution | Window: `frames{presented,totalMsP50,totalMsP95}`, `pumpGapAfterFirstFrameMs{p50,p95,max}`, `native-html-pump-gap` (over 50 ms), `gpu{submitToDoneMsP50/P95}`; `spinal_perf.ts` `tick.engine_ms` median/p95/max; Hub: `hub_spinal_perf.mjs` `frames.draw_ms` median/p95/max, `late_over_early` | histogram; percentage of frames over 16.7 ms and 8.3 ms; hitch ms per s; worst 1 s window; frame-to-frame jitter; missed-vsync count (no display link or presented-time handler in the window) |
| "It never freezes" | longest turn, long-turn distribution | survey `script_turn_max_ms`; `slowCalls{name:{count,maxMs}}` (main-thread calls over 2 ms); `native-html-pump-stall` (over 30 ms); `script_turn_cost_test.ts` | count and total of turns over 50 ms (the Long Tasks measure); time blocked while input was waiting |
| "It is calm" | idle CPU and wakeups | `idle{turnsPerSecond,idleMs,…}`; survey `cpu_idle_pct`, `cpu_s`; `idle_loop_check.ts` (budget `window.empty.idle.turnsPerSecond`) | energy (macOS `powermetrics`), thermal state recorded with each run |
| "Nothing jumps or flashes" | layout shift, blank or changed frames | survey verdict "blank" (fewer than 20 primitives); `layout_similarity` against Chrome | a layout-shift score from the engine's own box movements; a flicker detector (a presented frame blank or far from both neighbours after the first contentful frame); count of full relayouts after first content (images arriving) |
| "It is the same every time" | spread across runs | none: the survey does one watch run and one scroll run per page; `spinal_perf.ts` is one run | N runs with median, worst, CV; run-to-run spread as a trend column |
| "It stays fast" | memory and heat over time | `rss_peak_mb`, `spinal_perf` RSS growth after warm-up | a 10 minute soak with frame-time percentiles per minute |

How to take the existing numbers:

- Window summary: `run_html.ts … --perf-summary --idle-checks-only` (without `--idle-checks-only` each sweep
  frame includes pixel checks of 100 ms or more). The JSON line `{"type":"native-html-perf-summary"}` is traced at
  exit in every run. Percentiles are nearest-rank. `--trace-input` adds the native event trace.
  `sweeps.sh` runs every sweep off screen.
- Engine without a window: `deno run -A --unstable-ffi spinal_perf.ts [--engine LIB] [--ticks 600] [--out FILE]`.
- Variants and the window: `spinal_bisect.ts` (`--app` for window fields); full mode `sh spinal_bisect_full.sh`.
- Hub: `node hub_spinal_perf.mjs [--seconds 45] [--adapter auto|gpu|swiftshader] [--live|--runtime DIR]`.
- Real pages: `deno run -A realpages/survey.ts --engine LIB --out DIR --lock /tmp/foafnaut-timing.lock`.
- Textnaut: `--timing`.
- Proved costs: `formal/lean4/L4Factoidal/FrameCost/Theorems.lean` with `frame_cost_test.ts` and
  `frame_work_test.ts`. A theorem that an input class does no layout is stronger than any percentile; prefer one
  where the property is structural.
- Pipeline order (not times): `run_html.ts --pipe-trace FILE` (pumps, GPU submissions, blocking GPU waits),
  checked against the Lean pipeline model by `pipeline_trace_check.ts` (`HostPipeline/Model.lean`).
- What a frame waited for: `run_html.ts --gate-trace FILE`, one JSON line per GPU submission (its cost and
  predicted GPU time), ask (when due, when asked, how long the call blocked the main thread), wait of a frame
  for the GPU gate, band count of a frame, and pump. A frame that is slow with a fast engine is read here:
  asks long after their due time (the loop turned late), predictions several times the measured GPU time (the
  gate slept too long), or long blocks (the prediction was short).

What an end point means here. Window latencies start at the enqueue stamp taken in `native_window.m`
(`from:"queued"`) or at dequeue, and end when `present()` returns. They leave out the device and OS before the
stamp (often 10 to 40 ms) and the compositor and display after it (one to two frames). Add about 30 to 60 ms to
compare with camera measurements such as Dan Luu's. A camera or photodiode measurement of the whole path is the
only check on that estimate.

## Targets

Software share only (stamp to `present()`), on the reference Mac, release engine. "Now" figures are in
`fncg/status.md` and the survey trend, not here.

| Metric | Target | Ceiling (fail) | Why |
|---|---|---|---|
| Key to present, typing in a field | p50 ≤ 8 ms, p95 ≤ 16.7 ms | p99 ≤ 50 ms | hardware and display already spend 30 to 60 ms (Luu); effort rises somewhere between 20 and 200 ms in total (Schmid); one frame keeps the total under about 80 ms |
| Hover and drag feedback | p95 ≤ 16.7 ms | p99 ≤ 33 ms | continuous input; improvements of one 120 Hz frame are noticed (Deber), and lower is preferred below 10 ms (Ng 2012) |
| Click or tap to visible feedback | p95 ≤ 50 ms | p99 ≤ 100 ms | visual feedback quality falls between 100 and 150 ms in total (Kaaresoja); RAIL's 50 ms handling |
| Scroll to present, within the laid-out band | p95 ≤ 16.7 ms | p99 ≤ 33 ms | continuous input, as hover; proved to need no layout |
| Scroll to present, any | p95 ≤ 100 ms | max ≤ 300 ms | the present 300 ms p95 goal is a staging post; 300 ms is "very low quality" for a press (Kaaresoja) |
| Frames over budget during animation or scroll | ≤ 1% over 16.7 ms; tracked at 8.3 ms | ≤ 5% | Chromium's percent dropped frames; Android slow frames |
| Hitch time | ≤ 10 ms per s | ≤ 25 ms per s | Apple's good and warning levels |
| Frame-time jitter (p95 minus p50) | ≤ 4 ms | ≤ 12 ms | Klein et al.: 4 ms little effect, 12 ms degrades |
| Longest frame after first content | ≤ 100 ms | ≤ 700 ms | Tokey et al. (225 ms spikes are felt); Android frozen frame |
| Turns over 50 ms while input is possible | none at p95 | none over 1 s | Long Tasks; the present "no turn over 1 s" goal is the ceiling |
| First frame (any acknowledgement) | ≤ 100 ms | ≤ 1 s | the 0.1 s and 1 s scales; feedback extends tolerance (Nah) |
| First contentful frame, local snapshot | ≤ 1 s | ≤ 2.5 s | Card's 1 s; LCP's 2.5 s is the relaxed figure |
| Layout shift after first content | ≤ 0.1 (CLS definition) | ≤ 0.25 | Core Web Vitals; weak evidence, kept because sites are judged by it |
| Blank or flashed frames after first content | 0 | 0 | a flash is a defect, not a rate; WCAG 2.3.1 as the safety limit |
| Idle CPU on a settled page | ≤ 2% | ≤ 10% | heat and battery turn into lost frame rate later; 10% is the present goal |
| Run-to-run CV of each metric above | ≤ 10% | ≤ 25% | predictability (Weber et al.); also makes regressions detectable |
| Worst of N over median of N | ≤ 1.5 | ≤ 3 | tails are what is remembered and what most page views hit |

When a target is far from the present number, set a dated staging target and keep this table as the end point.
At 120 Hz the frame figures halve (8.3 ms); track both.

## Workflows

### Setting a goal

1. Name the perception (a row of the catalogue), the scenario (page, input script, host) and the end points.
2. Take the baseline: 5 or more runs under the timing lock; record count, p50, p95, p99, max, and median, worst
   and CV across runs.
3. Choose the target from the table, or a dated staging target between the baseline and it. Write the evidence in
   one line.
4. State the goal on the tail: "typing in the Wikipedia search field: key to present p95 ≤ 16.7 ms, p99 ≤ 50 ms,
   worst of 5 runs ≤ 1.5 × median, by release X". A goal on a mean or a single run is not accepted.
5. Put it where it is enforced: a budget entry (below) or a survey column with a regression rule, and one line in
   `fncg/status.md`.
6. If the property is structural (this input never causes layout), state it as a theorem in `FrameCost` and a
   host counter test, and keep the timing as the second line of defence.

### Which time series

| Series | Where | Good for | Limits |
|---|---|---|---|
| Real-page trend | `realpages/trend.csv` on branch `wpt-scores` of `danbri/factoidal-builds` (columns `first_frame_s`, `first_layout_ms`, `gpu_p50_ms`, `cpu_idle_pct`, `script_turn_max_ms`, `scroll_latency_p50_ms`, `scroll_latency_p95_ms`, `rss_peak_mb`, `load_ms`, `cpu_s`, …) | first frame, longest turn, scroll tail, idle cost on real pages, per release | one run per page; CI runners are noisy; rule is 1.5 × previous and above a noise floor |
| Spinal Tap budgets | `fixtures/spinal-perf/budgets.json` (`native`, `hub`), `fixtures/spinal-bisect/budgets.json` (`native`, `window`), ratchet in `spinal_budgets.mjs` | frame cost, tick median and p95, first layered frame, RSS, idle turns; fails a PR | one page; one run |
| WPT and Test262 runs | `runs.csv`, `runs/<id>/meta.json` on `wpt-scores` | wall time, crashes, stalls and timeouts as a stability series | not a responsiveness measure |
| CI timing | branch `ci-metrics` of the builds repository (`runs.csv`, written by `ci-metrics.py`; work on `wip/ci-cache`) | time to a tested build | developer-facing, not user-facing |
| Hub frame stats | `hub_spinal_perf.mjs` output, budget section `hub` | draw median and p95 in a real browser host | headless Chrome; adapter differs by machine |

Series to add, in the order of the gaps below: typing latency per page (p50, p95, p99); frame histogram columns
(`frames_over_16_pct`, `frames_over_8_pct`, `hitch_ms_per_s`, `frame_max_ms`); `long_turns_over_50`;
`layout_shift`; `flicker_frames`; and for every timing column a `_cv` and `_worst` companion from N runs.

### Reading distributions

- Look at p95, p99 and max before the median. Then at the count: a p99 of 40 samples is the max.
- Plot or print a histogram when two runs disagree; two humps mean two code paths (band scroll against relayout),
  and each needs its own number.
- Percentiles do not average. To combine runs, pool the samples, or report the median and worst of the per-run
  percentiles.
- Compare tails as ratios to the median (p99 over p50). A falling median with a rising ratio is a system getting
  less predictable.
- A regression is: a tail above its ceiling; or a tail worse than the base by more than the base's run-to-run
  spread (use 2 × the base's range over 5 runs when no better estimate exists); or the CV crossing its ceiling.
- Faster on average with a worse tail is not an improvement. Say so in the hand-back and let the reviewer decide.
- Record machine load, power source and thermal state with every run; a run at load 12 is not data.

### A/B under the timing lock

1. Log the run in the coordination log before starting.
2. Take `/tmp/foafnaut-timing.lock`: `survey.ts --lock FILE` and `spinal_bisect.ts` take it themselves (a Deno
   file lock); wrap anything else the same way. macOS has no `flock(1)`.
3. Same machine, same session, mains power, release engines, `--idle-checks-only` on window sweeps.
4. Interleave: A B A B A B …, 5 or more of each, discarding one warm-up of each. Never all of A then all of B.
5. Report per side: pooled p50, p95, p99, max; median, worst and CV of the per-run p95. Call a difference real only
   when the ranges of the per-run values do not overlap, or the gap is over 2 × the larger range.
6. Give both end points, the engine hashes, the load average and the command lines.

### Ratcheting

- A met target becomes a budget in the same PR: a `max` in the budgets file, with the tail (p95) budgeted, not
  only the median. `spinal_budgets.mjs` fails a PR that loosens a budget without a new `accepted` text, and fails
  a known failure that now passes until it is moved into the budgets.
- Tighten to the worst of the last 5 good runs plus the run-to-run range, not to the best run.
- Survey columns ratchet by the trend rule; when a column gains N-run spread, move its rule from "1.5 × previous"
  to the spread-based rule above.
- Never loosen a tail budget to land a gain in a median. Record the trade and ask.

## Gaps, in priority order

1. **Typing latency in the window.** Stamp text input (kind 9) as keys are stamped; add a `--type-sweep` that
   types into a focused field at about 8 keys per second; report p50, p95, p99, max in `--perf-summary`; add
   survey columns. This is the most used continuous input and has no number.
2. **Frame-pacing histogram.** Per run: buckets of frame time, percentage over 16.7 and 8.3 ms, hitch ms per s,
   worst 1 s window, p95 minus p50, max. Needs a display-link or presented-time stamp in `native_window.m` to
   count missed refreshes; until then from `present()` intervals.
3. **N runs and spread in the survey and `spinal_perf.ts`.** `--runs N` (default 5 for timing columns), median,
   worst and CV per column in the trend.
4. **Pointer-move and hover latency.** Stamp kind 3; a `--hover-sweep` and a drag sweep; split `inputLatency` by
   kind in the summary.
5. **Flicker and layout-shift detection.** The engine reports box movement between frames (a CLS-like score from
   its own layout); the host counts presented frames that are blank or differ from both neighbours after the first
   contentful frame; count full relayouts after first content.
6. **First contentful frame** as its own stamp in the window, Hub and Textnaut, and in `--perf-summary`.
7. **Long turns as a distribution**: count and total over 50 ms, and time input spent queued behind a turn.
8. **Display-time end point**: a presented-time stamp, and one camera or photodiode calibration of the whole path
   per reference machine.
9. **Scroll anchoring** (not implemented), so late images do not move the reading position; and momentum-phase
   scroll latency reported separately.
10. **Reduced motion passed through**: the host reads the OS setting but the engine's `env.reducedMotion` stays
    `no-preference`; pass it, and test that page media queries see it.
11. **Soak and energy**: a 10 minute run with per-minute frame percentiles, RSS, `powermetrics` energy and thermal
    state.
12. **Hub touch**: touch-to-frame latency with a DOM event start stamp; a haptic response is a platform matter and
    comes after the visual number exists.
