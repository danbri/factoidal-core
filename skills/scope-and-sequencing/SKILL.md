---
name: scope-and-sequencing
description: Nothing is out of scope for Foafnaut; areas not worked on yet are a matter of order ("walk, then run"). The wording to use for deferred work (later, not yet, reported separately; never "out of scope"), the rule that headline numbers count everything with secondary numbers beside them, the deferred areas and their plan issues (Test262 excluded features and stage 3 proposals, Intl non-ISO calendars, WPT encoding/, OWL profile identification, WebXR, media and 3D, non-Latin text layout). Use when writing a report, issue, hand-back, dashboard label or plan that leaves something out, when choosing what to work on next, or when a number is quoted with part of a suite removed.
---

# Scope and sequencing

Foafnaut aims at the whole World Wide Web: every format at every URI, every script and language, every
device. Nothing is out of scope. When an area is not being worked on, that is a decision about order: walk,
then run. The area stays visible in the numbers and keeps a plan, so that it is picked up when its turn comes
and nobody reads its absence as a decision to drop it.

The wider principle (the Web is more than the web platform; formats such as XSLT, RDF syntaxes or PostScript
are not "legacy, not worth investment") is in
[issue 451](https://github.com/danbri/factoidal-core/issues/451).

## 1. Words

| Say | Don't say |
|---|---|
| later; not yet; next after X | out of scope; won't do; not a goal |
| reported separately (and say where) | excluded; ignored; doesn't count |
| deferred until X lands, plan in issue N | not worth it; legacy; niche |
| the built-in engine refuses it today (feature off) | unsupported forever; never |

This applies to code comments, commit messages, issues, PRs, dashboards, skills and hand-backs. A refusal in
the engine (a feature turned off because an op is missing) is a fact about today, and its message says so.

## 2. Numbers

- **The headline counts everything.** A suite's headline share has the whole suite as its denominator,
  including the parts not yet worked on. Never shrink the denominator to make the number look better.
- **Secondary numbers sit beside it**, never instead of it, each labelled with what it leaves out:
  - WPT: the share, and the share without `encoding/` ([`wpt-runs`](../wpt-runs/SKILL.md) section 1).
  - Test262: the share, and the share without the excluded features (`release-tests/test262-excluded-features.txt`
    in `danbri/factoidal-builds`, plus the stage 3 proposals of `features.txt`) ([`wpt-runs`](../wpt-runs/SKILL.md)
    section 9).
  - Real pages: every page in the survey, including pages in scripts we do not draw well yet
    ([`realpages-survey`](../realpages-survey/SKILL.md)).
- A deferred area that has a test suite keeps running in that suite. Its result is recorded on every run even
  while nobody works on it, so a regression or an accidental gain is seen.
- Counting rules in general: [`counting-coverage`](../counting-coverage/SKILL.md).

## 3. Every deferred area has a plan entry

A plan entry is a GitHub issue that says what the area covers, what works today, what is measured and where,
what comes first when work starts, and what it waits on. When you defer something new, open the issue in the
same step and link it from the report. When a deferred area has no issue, open one (rules:
[`issue-management`](../issue-management/SKILL.md)).

Deferred areas on 2026-11-16 (core = `danbri/factoidal-core`, old = `danbri/factoidal`):

| Area | What is counted today | Plan entry |
|---|---|---|
| Test262 excluded features: host hooks and harness features (`agent`, `IsHTMLDDA`, ...) and stage 3 proposals | in the Test262 headline; the second number leaves them out | Intl: [core 505](https://github.com/danbri/factoidal-core/issues/505); stage 3 proposals and host hooks: no issue yet, open one |
| Intl: non-ISO calendars, time zones beyond UTC, locale data | `intl402/` in the Test262 headline | [core 505](https://github.com/danbri/factoidal-core/issues/505) (BubblePopJS Intl plan) |
| WPT `encoding/` (legacy East Asian encodings, half the WPT denominator) | in the WPT headline; the second number leaves it out | old [1184](https://github.com/danbri/factoidal/issues/1184), [1183](https://github.com/danbri/factoidal/issues/1183), [1185](https://github.com/danbri/factoidal/issues/1185) |
| OWL 2 profile identification (EL, QL, RL checkers) | OWL test suites as run | old [773](https://github.com/danbri/factoidal/issues/773) |
| WebXR | WPT `webxr/` in the headline | no issue yet, open one |
| Media and 3D: audio, video, WebGL, WebGPU 3D, canvas 3D | WPT `media*/`, `webgl/`, `webgpu/` in the headline; real pages with media | core [447](https://github.com/danbri/factoidal-core/issues/447) (WebGL stream at the handover); media and 3D as a whole: no issue yet, open one |
| Non-Latin text layout: complex shaping, bidi, vertical writing, CJK and South-East Asian line breaking, Mongolian | WPT `css/css-text`, `css/css-writing-modes`, `css/css-fonts`, `i18n/` in the headline; our own cases in [`i18n-layout-testing`](../i18n-layout-testing/SKILL.md) | old [1274](https://github.com/danbri/factoidal/issues/1274) (fallback fonts), [1285](https://github.com/danbri/factoidal/issues/1285) (SVG vertical writing), [1259](https://github.com/danbri/factoidal/issues/1259) (SVG line breaking and bidi); an umbrella issue: open one |

Keep this table current: when a plan issue is opened, closed or replaced, edit the row in the same PR.

## 4. Choosing the order

Walk, then run: the order follows what everyday pages need and what the current goal names
(`skills/foafnaut/AGENT-BRIEF.md`). A deferred area moves up when real pages depend on it, when a cheap step
unblocks many tests, or when the owner says so. Moving an area up is a plan change: say so in the coordination
log and in the plan issue.

## 5. In a report

- Name what was left out, why (order, not scope), and where it is reported: "Intl calendars: later, plan in
  core 505; counted in the headline."
- Quote the headline first and the secondary number beside it, with the same commit, date and engine.
- Don't call a deferred failure "expected" in a way that hides it from the totals; expected-failure lists
  follow [`test-suites`](../test-suites/SKILL.md) and stay visible.
