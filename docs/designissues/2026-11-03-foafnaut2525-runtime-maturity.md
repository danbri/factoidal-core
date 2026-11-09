# foafnaut2525: JS, WASM, XSLT and native delivery

> Note, 2026-11-09: This assessment is of 3 November. Most of its "not yet" items have landed since (page scripts in the engine, a macOS app, XSLT in the demo pages). Do not quote it as current. Current state: [Foafnaut handoff](2026-11-09-foafnaut-handoff.md) and
> [skills/foafnaut/SKILL.md](../../skills/foafnaut/SKILL.md).

Requested by the owner on 3 November 2026. This record was prepared in a
side conversation. It updates documentation; it does not start the main
thread's implementation or establish a release date.

The inspected browser checkout was `b578816b0`; the qualified renderer
artifacts came from `63a73ff4a`. Recheck the source, artifact witnesses and
test reports before treating this dated assessment as current.

The [side-conversation handoff](../20261103-foafnaut2525-side-thread-handoff.md)
also records demo/native evidence, external tests, HTTPS and recovery,
embedded LWS and the owner's standalone-app requests.

## Existing implementation and evidence

The [script architecture](2026-11-03-script-engine-architecture.md) and
[development bundle record](../20261103-browser-development-bundle.md)
contain the implementation details and recorded runtime checks.

| Component | Implemented at this checkpoint | Remaining boundary |
| --- | --- | --- |
| HTML/CSS/SVG renderer | Lean parsing, DOM, supported CSS/layout and shared scene; native CLI and WASM artifacts with recorded parity and GPU checks | Incomplete web compatibility; a native CLI is not a native browser window |
| JavaScript execution | QuickJS-NG 0.18.0 WASI reactor in a worker; ordered classic scripts, retained script state, click callbacks, bounded logs and interrupt/restart controls | QuickJS is external C code, not Lean-verified; no current Test262 result for this browser embedding is established here |
| DOM binding | Lean node projections; `getElementById`, simple `#id` queries, text/attribute mutations and click listeners | Cached ancestor text and connected-node lookup can become stale after subtree mutations; no complete live DOM |
| Event loop | Serialized script/click turns and a host watchdog | Parser scheduling, modules, timers, Promise job draining, `fetch`, animation frames and general event propagation are outside this profile |
| Layout queries | Lean computes style/layout for rendering | `getComputedStyle`, `getBoundingClientRect` and related synchronous APIs are not exposed to page scripts |
| WASM | Lean and QuickJS execute in separate instances with separate heaps | No page-facing `WebAssembly` API, general guest-module loader, verified WASM runtime or proof-attestation verifier is established by this implementation |
| Native delivery | macOS ARM64 renderer CLI; development bundle uses an external WebGPU browser, Node and font dependencies | This bundle is not a standalone `foafnaut2525.app`; iPhone/iPad integration remains a separate build and UI task |

The same-turn DOM and layout contract is tracked in
https://github.com/danbri/factoidal/issues/1232
(scripts must observe their own mutations; define layout-query behavior).
Tests must exercise the actual QuickJS guest and Lean document, not the host
browser's DOM. A successful counter fixture does not establish general DOM
or event-loop compatibility.

## Next JS and WASM work

1. Establish synchronous DOM reads and mutations with stable node identity,
   connectedness and invalidation. Specify layout-query flush behavior against
   the current document, style and font state. Ordinary mutations need not
   repaint immediately, but subsequent script reads must see their effects.
2. Define tasks, microtask checkpoints and rendering opportunities. Add timers,
   Promise job draining and animation frames with navigation cancellation and
   termination tests. Keep the UI responsive when a guest does not return.
3. Add a bounded guest-WASM loader and then the chosen page-facing API. Keep
   runtime heaps private; pass typed messages or use an explicit import ABI.
   Imports, memory, execution budgets and cancellation need their own tests.
4. Add an integrated demo: JS controls, a WASM computation, a WGSL visual and
   an LWS save/reopen cycle. Treat this as an acceptance target, not existing
   functionality. WASM supplies CPU computation; WGSL supplies GPU shaders.

Running an engine in WASM establishes neither formal verification of that
engine nor formal verification of its guest programs. A future proof
attestation must identify the exact module digest, specification, theorem,
checker and assumptions. A Lean source theorem with a trusted compiler must
be described that way. A signature authenticates a claim; it does not prove
the claim. Proof status must not silently grant extra host capabilities.

## XSLT requested for browser use

The owner requests classic Mozilla-style XSLT: opening an XML document with
an associated stylesheet should transform and display it. The browser should
also expose an `XSLTProcessor`-compatible script interface when its XML DOM
bindings can support that interface.

Factoidal already has reusable Lean engines:

- `formal/lean4/L4Factoidal/XSLT/Transform.lean`, exported as
  `xsltTransform(stylesheetXml, sourceXml): Promise<string>` by the npm API.
- `formal/lean4/L4Factoidal/XSLT4/`, exported as
  `xslt4Transform(stylesheetXml, sourceXml)`, returning the principal output,
  serialization method, secondary results and messages.
- `docs/web/hub/data-compositor/pipeline.mjs` already calls
  `xslt4Transform` on SPARQL results XML. The
  [compositor worknote](../20261030-hub-data-compositor.md) records its runtime
  checks. This does not establish foafnaut browser integration.

At the inspected checkpoint the foafnaut document loader and QuickJS guest
do not provide `xml-stylesheet` transformation or `XSLTProcessor`. The public
XSLT4 wrapper accepts one stylesheet module and refuses unresolved
`xsl:include`/`xsl:import` with `XTSE0165`; it does not fetch dependencies.
Do not describe the existing string API as a complete browser XSLT binding.

Implement the integration in this order:

1. Load XML, retain its base URI and discover the prolog
   `<?xml-stylesheet type="text/xsl" href="view.xsl"?>` association.
   Fetch the stylesheet through the resource broker. Use the
   [W3C association rules](https://www.w3.org/TR/xml-stylesheet/).
2. Transform through a named Lean engine/version and feed supported HTML,
   XHTML or SVG output into the Lean renderer; show text output as text.
   Preserve the original document and transformation diagnostics. Report
   unsupported output and transformation failures explicitly.
3. Add `XSLTProcessor` methods for stylesheet import, parameters and document
   or fragment results, with correct namespaces and ownership. The
   [Mozilla API description](https://developer.mozilla.org/en-US/docs/Web/API/XSLTProcessor)
   describes the classic interface. Its methods are synchronous; the npm
   Promise API cannot simply be exposed as the same browser API.
4. Define resource resolution for includes/imports and document reads, plus
   limits on recursion, time and output. Keep secondary output writes under
   explicit host authority. Test resolution and refusal paths.
5. Run pinned external XSLT cases and browser integration cases: stylesheet
   association, relative URLs, parameters, namespace handling, errors and
   HTML/SVG results. Record unsupported, failed, crashed and timed-out cases
   separately. Engine corpus scores and browser integration scores are
   separate measurements; do not reuse old F* scores as Lean evidence.

Start with XSLT 1.0 compatibility for the classic-browser use case. Select
the existing 1.0 engine or a demonstrated compatibility mode by tests;
do not assume that the newer engine is automatically a drop-in replacement.
XSLT can present RDF/XML or SPARQL XML; the transformation alone is not an
RDF parsing, graph-equivalence or entailment claim.

MDN currently marks the browser API deprecated. This does not prevent an
independent engine from implementing the requested feature, but tests must
not silently delegate its execution to Chrome or WebKit and call that Lean
XSLT support.

## Apple distribution constraints checked on 3 November 2026

The existing [mobile native library proposal](2026-10-29-mobile-native-library.md)
is a compilation and integration proposal, not an App Store approval.
Lean-generated C, a native GPU surface and an interpreter are technically
separate from Apple's distribution policy.

[App Review guideline 2.5.6](https://developer.apple.com/app-store/review/guidelines/#software-requirements)
requires WebKit for web browsing except where an alternative-engine
entitlement applies; Apple currently identifies EU and Japan routes. No UK
route is established by these documents. Northern Ireland is not an EU
exception: Apple's [eligible EU regions](https://support.apple.com/121575)
include Ireland, not Northern Ireland or the UK. The
[CMA work programme](https://www.gov.uk/guidance/the-cmas-programme-of-work-across-mobile-platforms)
still describes removal of the WebKit restriction as work to progress.

The [EU engine entitlement](https://developer.apple.com/support/alternative-browser-engines/)
requires at least 90% of WPT, using Apple's specified denominator, and 80%
of Test262, plus security requirements. Our fixture and corpus evidence does
not establish eligibility. Default-browser status is a separate entitlement.
Do not assume an interpreter, a WASM wrapper or a different product name
removes these requirements or the downloaded-code rules.

For early device development, use an Xcode iOS/iPadOS target with the native
Lean library, a Swift UI/Metal host and bundled test documents. A
[Personal Team](https://developer.apple.com/help/account/basics/about-your-developer-account)
supports testing on one's own devices with periodic reprovisioning. Paid
membership enables distribution workflows; external
[TestFlight](https://developer.apple.com/testflight/) testing requires beta
review and does not promise App Store acceptance. Confirm the proposed
custom-engine distribution with Apple before presenting an iPhone release
date as achievable under current rules.

### Nonprofit route and a possible DMA challenge

The owner asks whether a nonprofit with some EU presence can demand access.
Separate three questions: recognized nonprofit status, eligibility for a
distribution route, and approval of the browser engine. An EU connection
does not answer all three, and nonprofit status does not waive the engine
requirements above. Apple's published engine requirements focus on EU
distribution; they do not themselves require EU incorporation.

There is a specific nonprofit benefit. Apple's current
[Web Distribution requirements](https://developer.apple.com/support/web-distribution-eu/)
list an approved Developer Program fee waiver as one eligibility route.
Do not present the two-year membership/million-install route as mandatory
for every applicant. The
[fee waiver requirements](https://developer.apple.com/help/account/membership/fee-waivers)
require a recognized nonprofit legal entity and restrict sales of digital
goods or services through its apps. Web Distribution still requires
authorization and notarization; engine approval is a separate matter.

The Commission's [April 2026 DMA review, sections 2.2.5 and 2.2.6](https://digital-markets-act.ec.europa.eu/document/download/788ff6d9-f0bf-47d2-80a8-611d5ee5bc51_en?filename=DMA+Review_Commission+Staff+Working+Document_SWD_2026_123_1_EN.pdf)
explains Article 5(7)'s restriction on imposed browser engines, Article
6(4)'s alternative-distribution obligation and the proportionality limit on
security restrictions. It acknowledges technical and contractual obstacles
for browser-engine providers and invites stakeholder reports.

A possible argument is that broad compatibility thresholds exclude safe,
limited engines without a proportionate security justification. This is a
proposed challenge, not a finding that Apple's thresholds are unlawful or
that foafnaut2525 must be admitted. Prepare measured compatibility results,
security evidence and the exact requested access; obtain Apple's written
position and seek specialist advice on enforceable remedies. The
[DMA business contact](https://digital-markets-act.ec.europa.eu/contact-us-business_en)
accepts submissions as market information; submitting one does not ensure
an investigation or approval. No application or complaint was sent here.
