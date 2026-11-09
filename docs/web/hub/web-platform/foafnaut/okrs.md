---
title: Foafnaut objectives and key results
description: Four objectives of equal weight (standards, security, privacy, performance), with key results measured at each milestone on the way to 90% of the Web Platform Tests.
layout: hub.njk
---

<p class="hub-crumbs"><a href="{{ '/web/hub/' | url }}">Hub</a> › <a href="{{ '/web/hub/web-platform/' | url }}">Web platform</a> › <a href="{{ '/web/hub/web-platform/foafnaut/' | url }}">Foafnaut</a> › Objectives</p>

# Foafnaut objectives and key results

Set on 9 November 2026. The four objectives carry **equal weight**: standards
compliance, security, privacy and performance. A milestone is reached only when the
key results of **all four** are met for it, not when the WPT score alone is. All numbers
are measured with BubblePopJS, the engine's own JavaScript engine.

## Milestones

| Milestone | WPT share (of the most subtests a front-page browser runs on wpt.fyi) | What gets it there |
|---|---|---|
| M0 (now) | about 15%, estimated; measured 1.75% on 8 November | the 9 November merges; a whole-suite BubblePopJS run replaces the estimate |
| M1 | about 32% | same-origin iframe documents |
| M2 | about 45% | Dedicated Workers, WebIDL bindings generated from the specifications, fetch and networking in Lean |
| M3 | 65–70% | form submission, navigation, WasmVM SIMD |
| M4 | 90% or more | CSS, HTML, editing and the long tail |

The shares are projections until measured. Each is checked with
`tests/browser-wpt/wpt-score.py` against the denominator Apple's EU rule uses (2,267,658
subtests for Chrome 157 stable on 8 November 2026).

## O1. Standards compliance

- **KR1.1** Whole-suite WPT score measured and published on the Hub at least weekly, with every directory's score and the runner's known gaps.
- **KR1.2** The milestone WPT shares above, measured on BubblePopJS, with the full WPT server (`wptserve`) and with worker variants run, not skipped.
- **KR1.3** Test262, full suite, run on an Apple-silicon Mac with no JIT: 80% or more by M2, 90% or more by M3 (Apple's EU bar is 80%).
- **KR1.4** Real sites (Wikipedia, gov.uk, BBC News, and at least 10 more by M2) render with no refusals in strict mode by M3. Liberal mode is not counted.
- **KR1.5** No gains from test-specific code. Features come from the specifications (IDL, CSS property data, Encoding, URL), and a review checks each large gain.

## O2. Security

- **KR2.1** Every algorithm that handles web content is in Lean. Any C that remains is listed, with a reason, in one place: HACL\* (verified), the C glue (audited) and sandboxed WasmVM guests. No new C enters the web-content path without that review.
- **KR2.2** Every native boundary (FFI or extern) is checked mechanically for arity, types and preconditions (the glue audit) and fuzzed under AddressSanitizer and UndefinedBehaviorSanitizer before release: 100% of boundaries at every milestone.
- **KR2.3** Isolation is proved, with theorems:
  - WasmVM guests stay within their memory;
  - page GPU commands are validated;
  - sandboxed frames get no script session without `allow-scripts`;
  - workers can't reach the page's heap;
  - crypto keys can't leak (noninterference outside a key's usages).
  
  The theorem list is published and grows with each feature, and no milestone ships a new web-content feature without its isolation statement.
- **KR2.4** No regression in proof hygiene: `partial def` count does not rise; the tail-recursion and unbuilt-module gates pass on every release.
- **KR2.5** Same-origin policy, CORS and CSP are decided in Lean with theorems when fetch lands (M2). Mixed content is blocked.
- **KR2.6** By M2: a published vulnerability disclosure policy and a page of fixed issues per version; exploited issues fixed within 30 days. By M3: a process-separation design with validated IPC, and a prototype.
- **KR2.7** Every third-party component is pinned, with provenance and a licence record, and is checked for known vulnerabilities at each release.

## O3. Privacy

- **KR3.1** From the first cookie implementation (M2): third-party cookies blocked by default, with a theorem that a cross-site request carries no cookie unless the user allowed it.
- **KR3.2** From the first storage implementation (M2): all storage and observable state partitioned per top-level site, with a theorem that one site cannot read another's partition.
- **KR3.3** Nothing leaves the device without a user action. No telemetry. Browser-state sync (Linked Web Storage) stays opt-in, and the default makes no network requests of its own.
- **KR3.4** Default referrer policy `strict-origin-when-cross-origin`; no device identifiers to sites; clipboard, fullscreen and similar APIs need user activation, decided in Lean.
- **KR3.5** The WPT privacy-related directories (cookies, storage partitioning, referrer-policy, permissions, storage-access) are tracked as their own score, from M2.

## O4. Performance

- **KR4.1** Pages without a feature pay nothing for it. Every new API installs lazily, and start and frame costs of the demo pages do not rise by more than noise.
- **KR4.2** Real sites, native, M2: first frame under 1 s and relayout under 200 ms for Wikipedia and gov.uk (today 11.8 s and 4.8 s; 7.8 s and 7.7 s). M3: the same on the Hub.
- **KR4.3** Interaction: input-to-feedback p95 under 50 ms natively; scrolling never re-lays out (cost theorem); animations and transforms paint-only at 60 fps (frame-cost ratchet).
- **KR4.4** BubblePopJS: first page start under 10 ms natively (reached on 9 November). By M2, an interpreter at least 3× faster on `fib(24)` and on a WPT page start, through bytecode, inline caches and a collector. By M3, on the Hub too.
- **KR4.5** Every hot path has a cost test that fails if it turns quadratic: DOM writes, Array push, selector matching, shaping, live collections.
- **KR4.6** Cost theorems and host counters run in CI. A regression over 5% blocks the release unless it is stated and accepted.

## How progress is reported

Weekly, on the Hub: the WPT score by directory; the Test262 score; the real-site timings;
the list of security and privacy theorems; the boundary audit and fuzz results; and the
cost-ratchet numbers. Each milestone note says which key results are met and which are not.
