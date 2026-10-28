# SMIL 3.0: the timing and synchronization model as a Lean engine

Date: 2026-10-28. Status: design, no code. Tracking:
https://github.com/danbri/factoidal/issues/1165 (section "Front end: design
first", SMIL 3.0).

## Result

The SMIL timing model is a pure computation: a timing tree, the events that
occurred, and a document time give the intervals of each element and the
state of each element at that time. Lean computes this. A test needs no
renderer: the expected intervals come from the specification text. The
browser later plays media and shows or hides elements from the state that
Lean computes; it makes no timing decision.

Nothing for SMIL exists in the tree today (a search for `smil` in
`formal/lean4` finds no module).

## 1. Target specifications (version-aware)

| Name in Lean | Specification | Use |
|---|---|---|
| `Smil30` | SMIL 3.0, W3C Recommendation 2008-12-01: the Timing and Synchronization modules, Time Manipulations, and the Animation modules | target |
| `SmilAnimation` | SMIL Animation, W3C Recommendation 2001-09-04 | the timing that SVG 1.1 animation elements (`animate`, `set`, `animateMotion`, `animateTransform`) use |

The two share the interval model. Theorem 4 below states where they agree,
so the SVG path reuses the SMIL 3.0 results.

## 2. Scope of the engine

In: clock values (full, partial, timecount) and wallclock values; `begin` and
`end` value lists (offset, syncbase `id.begin`/`id.end` with offset, event
`id.event`, `accesskey`, `repeat(n)`, `wallclock`, `indefinite`); `dur`,
`repeatCount`, `repeatDur`, `min`, `max`, `fill`, `restart`, `endsync`;
time containers `par`, `seq`, `excl` (with `priorityClass`); simple, active
and repeat duration; the interval life cycle (first interval, next interval,
pruning when a syncbase changes); time manipulations `speed`, `accelerate`,
`decelerate`, `autoReverse` as a map from active time to simple time; the
animation function of the Animation module (`from`, `to`, `by`, `values`,
`calcMode`, `keyTimes`, `keySplines`, `additive`, `accumulate`) over numeric
values.

Out: media decoding, layout regions, transitions as drawing, content control
(`switch` test attributes are a later stage: they are a pure function of
system settings and can be added the same way).

## 3. Engine shape

```
structure TimingNode where     -- read from the SMIL or SVG document (XML parser)
  id : String; kind : par | seq | excl | leaf
  begins ends : List TimeValue; dur ... ; kids : List TimingNode

def schedule : TimingNode → EventLog → Time → Schedule      -- intervals per element up to the given time
def stateAt  : Schedule → Time → ElementId → State         -- active or frozen or inactive, simple time, repeat iteration
```

- Time is an exact rational number of seconds (reuse the rationals of
  `MathML/Rat.lean` and `Math/`), plus `indefinite` and `unresolved`. No
  floating point, so the theorems are about equalities.
- The event log is an input value. A live player appends events; a test
  gives a fixed log. This makes the engine deterministic.
- Syncbase dependencies form a graph; resolution is a loop over a work list
  with a fuel bound from the number of elements and events, never one stack
  frame per item (tail recursion rule). A cycle of syncbase dependencies is
  handled as the specification says (instance times that depend on
  themselves are not resolved).
- Wallclock values convert through `XSD` `dateTime` and a document start
  time given as input.

## 4. The model and rendering split

| Part | Where |
|---|---|
| Parse the SMIL or SVG document | Lean (XML parser; HTML parser for SVG in HTML) |
| Interval computation, state at a time, animation values | Lean |
| The clock (the current time) and user events (click, key) | Host: it sends `(time, element, event)` to the engine |
| Play, pause and seek media; show or hide elements; set animated attribute values | Browser JS, from `stateAt` output only |
| Native SVG SMIL animation in the browser | Optional output path: Factoidal writes SVG with SMIL animation elements and the browser runs it. Then Lean's schedule is a reference to compare with the browser (a differential test), not the driver |

## 5. Test corpus

- **From the specification**: every example in the SMIL 3.0 Timing and
  Synchronization chapter and in SMIL Animation that states a result
  (intervals, active duration, the effect of `restart`, `fill`, `endsync`,
  `excl` pause and resume) becomes a case: the document fragment, an event
  log, and the expected intervals or states. Each case names the section.
  The active duration table (combinations of `dur`, `repeatCount`,
  `repeatDur`, `end`, `min`, `max`) becomes a set of cases with one row each.
  Stored in `tests/smil/` with a README that says the cases are authored from
  the Recommendation (the same pattern as `third_party/testing/mathml/`).
- **W3C SMIL test suites**: the SMIL 2.1 and 3.0 test suites at w3.org are
  documents that a person watches in a player. Stage 1 checks what is
  available and its licence; cases whose pass condition is a time or an order
  become machine cases with a sidecar of expected intervals, as for the XForms
  1.1 suite.
- **web-platform-tests `svg/animations/`**: script tests that set the
  document time and read animated values (for example with
  `setCurrentTime`). Their assertions convert to `stateAt` and animation
  value cases for `SmilAnimation`. Vendor with provenance.
- **Reference implementation for differences**: the Ambulant player (SMIL
  3.0) and browsers (SVG SMIL) are external oracles for disputed cases, never
  for the expected values themselves.

## 6. Theorems to aim for

1. **Active duration**: the computed active duration equals the formula of
   the specification (the minimum of the repeat and end constraints, then
   clamped by `min` and `max`), for every combination of attributes.
2. **Intervals are ordered and disjoint**: the intervals of one element do
   not overlap and are in increasing begin order; the children of a `seq` have
   intervals that do not overlap; in an `excl` at most one child is active at a
   time.
3. **Causality**: an event at time `t` does not change `stateAt` at a time
   before `t`. So a live player can compute forward with no backtracking, and
   a seek forward equals playing to that time.
4. **SMIL Animation and SMIL 3.0 agree** on documents that use only the
   attributes of SMIL Animation (2001): the same intervals and the same
   animation values. Named versions in the statement.
5. **Time manipulation inverse**: with `autoReverse` false and `speed` 1, the
   simple time equals the active time modulo the simple duration; with
   `accelerate` and `decelerate`, the map from active time to simple time is
   monotone and onto the simple duration.
6. **Termination with fixed memory**: resolution ends within the fuel bound
   for any document, and the fuel bound is linear in elements plus events.

## 7. Staged plan

| Stage | Work | Measure |
|---|---|---|
| 1 | Survey and vendor (W3C SMIL test suites, WPT `svg/animations/`) with provenance; author the spec-example corpus | case counts in the ledger |
| 2 | `Smil/ClockValue.lean` (parse clock and wallclock values) and `Smil/ActiveDuration.lean`; theorem 1 | corpus cases for durations |
| 3 | `Smil/Interval.lean`: begin and end lists, syncbase and event values, first and next interval, `restart`, `fill`; theorems 2 (single element) and 6 | `l4smil` runner: pass, fail (out of N) |
| 4 | Time containers `par`, `seq`, `excl`, `endsync`; theorem 2 (containers) and 3 | runner score |
| 5 | Time manipulations; theorem 5 | runner score |
| 6 | Animation function (`SmilAnimation`) and WPT `svg/animations` cases; theorem 4 | runner score |
| 7 | Wasm op `smilSchedule`; a hub page that plays a small presentation from `stateAt`; the optional native SVG SMIL output with a differential test against headless Chromium | browser sweep |

## 8. Decisions recorded here (coordinator, not owner)

- Time is exact rational seconds, not floating point.
- The event log is an input, so the engine is a function and the browser only
  supplies the clock and the events.
