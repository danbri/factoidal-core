# Reusable author CSS slice for the SVG lab

A source search under `formal/lean4/L4Factoidal` found HTML tokenizer/tree
builder modules, but no existing CSS declaration parser or cascade module to
reuse. `labs/demos/foafnaut/SVGCSS.lean` therefore introduces a small pure Lean
module, without renderer imports. It accepts caller-supplied property names and
a mandatory property-value validator. The SVG reader now consumes this shared module.

## Supported and refused syntax

The baseline is [CSS Syntax 3](https://www.w3.org/TR/css-syntax-3/) and
[CSS Cascade 5, cascade ordering](https://www.w3.org/TR/css-cascade-5/#cascade-sorting).
This is an explicit-refusal subset, not a conforming implementation of their
complete parsing/error-recovery algorithms.

Supported: ASCII type selectors and comma-separated type lists; case-sensitive
SVG type matching; whitespace and non-nesting comments; case-insensitive property
names; simple semicolon-separated declarations; duplicate properties; repeated
rules in source order. Comments separate tokens and never concatenate identifiers.

Priority is presentation attributes below matching stylesheet rules below inline
style. All accepted stylesheet selectors have equal type-selector specificity,
so later declarations win. The returned property list has unique names. This
module does not implement inheritance; the SVG consumer must apply inherited
values using its existing style evaluator.

Explicit refusals include !important, at-rules, selector combinators, namespaces,
classes/IDs, universal selectors, pseudo-classes, string/escape syntax, unknown
properties, empty values, malformed braces/colon structure and unterminated
comments. Strings, escaped tokens and values containing colon/semicolon are
outside the slice. Limits: 65536 input characters, 256 stylesheet rules and 1024
declarations per block. CSS error recovery normally ignores invalid declarations;
this profile instead refuses the stylesheet/document. That narrower contract is
intentional and must remain visible to callers.

The caller must supply a value validator to `cascade`. It validates every
presentation, stylesheet and inline declaration before selecting winners,
including declarations overridden later or in unmatched rules. Do not replace
this validator with unconditional success in production: otherwise unsupported
or invalid syntax could disappear behind another declaration. The caller must
also implement the supported property vocabulary; accepting the string
stroke-dasharray in parsing does not implement dashed strokes.

## Focused evidence and next integration

Compiled with Lean 4.33.1 to `/private/tmp/SVGCSS.olean`; `SVGCSSTests.lean`
passes 18 executable guards plus parsing/assertions over the unchanged WPT
`percentage.svg` and `percentage-attribute.svg` style blocks at revision
`70dae60789ef6220d9b4e60c92c5b2107b4e2b93`. They contain one rect rule with
five and two declarations respectively. Tests cover source order, inline priority,
presentation fallback, selector case, comments, type validation before selection,
and refusal boundaries. These are finite executable tests, not cascade proofs.

Original parser compilation (historical):

```sh
lean +leanprover/lean4:v4.33.1 -o /private/tmp/SVGCSS.olean SVGCSS.lean
# The fixture tests now use the normal formal/lean4 working directory.
# From formal/lean4, after compiling SVGCSS into the lab olean directory:
LEAN_PATH=../../labs/demos/foafnaut/.build/olean:.lake/build/lib/lean \
  lean -R ../../labs/demos/foafnaut ../../labs/demos/foafnaut/SVGCSSTests.lean
```

The SVG adapter collects inert style text in document order (including later
style elements), parses inline declarations, validates each value through the
existing Lean property readers, and gives winning properties to its style
evaluator. CSS declarations on groups inherit using the existing style machinery;
shape opacity remains per-shape, and unsupported group opacity remains a refusal.
Style type accepts absent/empty/text/css; media accepts absent/empty/all. Other
types/media are refused rather than applied unconditionally. Metadata subtrees
do not contribute styles. Heavy builds and GPU runs were not performed. Stylesheet fetching,
CSS layout and full selector/cascade semantics remain unsupported. Both official
percentage tests also require dashed-stroke support before visual agreement can
be claimed.


`SVGCSSIntegrationTests.lean` also passes against freshly compiled SVG source.
It checks stylesheet/presentation/inline priorities, later source order and later
style elements, group inheritance, explicit inherit, CDATA, type/media, opacity
and refusal boundaries. Both unchanged official percentage documents now reach
an explicit stroke-dasharray/stroke-dashoffset refusal instead of style rejection.
This is parser progress, not a visual conformance pass. Percentage, affine and
path source regressions were rerun. `build-engines.sh` now compiles SVGCSS before
SVG, links its object into svg-engine, records the source in provenance and runs
both CSS test modules. Rebuilt artifact verification remains outstanding.

Coordinator validation: corrected both fixture paths for the build script
working directory formal/lean4, freshly compiled SVGCSS and SVG, and reran
CSS parser, CSS integration and percentage tests there: all passed. Updated
WASM regression expectations and README; those WASM tests await rebuilt assets.

A subsequent local diagnostic used current checked SVG/CSS source through
SVGArtifact.lean and raw WebGPU on Chrome156/Apple metal-3 (non-fallback).
The rendered image has the expected inline-blue rectangle, inherited-green
circle and white background at interior control pixels; all six emitted CPU
sample checks also passed. Evidence: /private/tmp/svg-css-gpu-check/candidate.json
and00-actual.ppm. This is a local GPU regression, not an independent full-image
CSS conformance comparison or a rebuilt WASM producer test.
