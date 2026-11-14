# MathML Core in the browser: style and layout (2026-11-14)

Branch `wip/xml-specs-mathml`. Specification: MathML Core, https://w3c.github.io/mathml-core/.
Measure: WPT `mathml/` (Chrome 4,321 subtests at WPT 2358bd4835).

## State before

Full run of main 19fb349c1 (Linux, run 20261114T0314Z-wpt-linux-x86_64-gh43550560855a1): `mathml/` passes
445 of Chrome's 4,321 subtests (10.3%). The engine had no MathML layout and no MathML style: an element in the
MathML namespace was an inline box with the text of its children. The feature probes of the tests
(`mathml/support/feature-detection.js`) read boxes with `getBoundingClientRect`: `mspace` sizes, a stacked `mfrac`,
a stacked `munderover`, a wider `msqrt`, operator spacing. With none of them true, almost every layout and
style test stops at its first assertion ("mspace is supported", 1,400 subtests in the older message corpus).

## Design

New modules under `formal/lean4/L4Factoidal/Rendering/Math/`; the shared files have small hooks marked
"MathML hook".

- `Math/Box.lean`: the arithmetic of each construct as pure functions over boxes (inline size, ascent, descent)
  in **layout units, 1/64 px, as integers**. Integers make the functions exact, so the theorems are about the
  numbers the engine computes. Row (§3.1.3.2), fraction (§3.3.2), scripts (§3.4.1), under and over scripts
  (§3.4.2), radical (§3.3.3), stretched size (§3.2.4.3), `mspace`, `mpadded`.
- `Math/Attributes.lean`: the user agent style sheet of appendix A and the attributes MathML Core maps to CSS,
  as one function of the element, its parent and its place among its element siblings (`hints`). The sheet is a
  function because the layout profile's cascade does not read child or `:nth-child` selectors. Each declaration
  has a level (user agent, user agent `!important`, presentational hint) with a cascade key in the order both
  cascades use. `math-depth` (`auto-add`, `add(n)`, integer), MathML lengths.
- `Math/Layout.lean`: the walk of a MathML subtree. It reads the document and the layout profile's styles, asks
  its caller for the inline content of a token element, and answers boxes relative to the root's left edge and
  baseline, the rules to paint (fraction bar, radical overbar) and the token content with its place.
- Hooks: `Style.lean` (`Computed.mathDepth`, `Computed.mathCompact`; the declarations of `hints` enter the
  cascade before the rules; `math-style`, `math-depth` and `font-size: math` are resolved),
  `ComputedGeneric.lean` (the same declarations in `cascaded`, so `getComputedStyle` answers `display`,
  `direction`, `color`, `background-color`, `math-style`, `math-shift`, `writing-mode`, `text-transform` for a
  MathML element; `math-depth` is the profile's integer), `Layout.lean` (a MathML element in a line is one atomic
  box, `mathSpecial`; a block-level one is centred; its intrinsic width is its box's), `CssValues/Data.lean`
  (`display-inside` gains `math`, so `display: block math` and `inline math` parse; `inline math` already had
  its short form `math` in `Properties.lean`).
- `getBoundingClientRect` and the other layout reads find MathML elements because the walk records the border
  box of every element in the layout result, as block layout does.

A page with no element in the MathML namespace: one namespace comparison per element in the cascade, per
inline element and per block box, and one closure call per inline-block; nothing is allocated. `Math.hints`,
`Math.layoutNode` and the font-size scale run only for MathML elements.

## Theorems

Proved (no `sorry`; `Math/Box.lean`, `Math/Attributes.lean`, `Style.lean`):

| Theorem | Says |
|---|---|
| `rowWidth_eq_sum` | a row's inline size is the sum of its children's advances (box plus operator space before and after) |
| `row_child_fits` | each child's ascent and descent are at most the row's |
| `rowAscent_tight`, `rowDescent_tight` | the row's ascent (descent) is zero or one child's: the maximum |
| `fraction_contains` | numerator and denominator lie inside the fraction's box on both axes |
| `fraction_bar_between` | with gaps and thickness of zero or more, the numerator's bottom is not below the bar's top and the denominator's top not above the bar's bottom |
| `fraction_num_above_baseline` | with the axis at or above the baseline, the numerator is wholly above the baseline |
| `scripts_contains` | base, subscript and superscript lie inside the element's box |
| `scripts_gap` | with both scripts, the gap between them is at least the font's minimum |
| `underOver_contains` | base, under script and over script lie inside the element's box |
| `radical_contains` | the content lies inside the radical's box, which is wider by the sign |
| `stretchSize_ge_base` | stretching never makes an operator smaller than its unstretched size |
| `stretchSize_reaches` | with a glyph assembly the stretched size is at least the target |
| `space_nonneg`, `padded_none` | an `mspace` box has no negative size; `mpadded` with no attributes is its content |
| `place_idem` | giving a cascade slot the same declaration twice is giving it once (attribute mapping is idempotent) |
| `author_over_hint` | any author declaration (any importance, context, specificity, order) takes a slot that holds a mapped attribute |
| `hint_over_ua` | a mapped attribute takes a slot from a normal user agent declaration and keeps it against one |
| `lexLE_eq_keyLE` | the layout profile's key order is the order those three theorems are stated for |
| `depthScale_same` | an unchanged `math-depth` leaves the font size as inherited |

Not true, so not stated: "a fraction's baseline lies between numerator and denominator". The bar is on the math
axis, above the baseline, and with a thin gap the top of the denominator is above the baseline. The true
statement is `fraction_bar_between`.

Tested only (`#guard`): the cases of the feature probes (fraction of 50px and 60px spaces, three stacked 20px
spaces, `lspace`/`rspace` of 20px), `scriptlevel` and `math-depth` values, MathML lengths, cascade key order.
The tree walk (`Math/Layout.lean`), the hooks, and everything that uses `Float` (the conversion to and from
layout units, the font size scale 0.71 to the power n) are tested by the WPT run only.

## Open

- No OpenType MATH table is read (`Rendering/SfntMath.lean` is not written): every font parameter is the
  fallback of a font with no MATH table, from the font size (x-height half an em, rule thickness 1/16 em, axis a
  quarter em). The tests that load `mathml/support` and `/fonts/math/` fonts and check exact numbers need it.
- No operator dictionary (appendix B): an `mo` has `lspace` and `rspace` from its attributes, else 5/18 em.
  No stretching, no `largeop`, no `movablelimits`, no `form`. `stretchSize` is proved but not called.
- The radical sign is not drawn (its overbar is). Fraction bar and overbar are drawn.
- `mtable`: a grid of centred cells; no spans, no `TableLayout` reuse, no `columnalign`.
- A math box in a line has its baseline on the line's baseline; a descent below the line's own does not grow
  the line.
- CSS `width`, `height`, `min-*`, `max-*` on MathML elements are not applied (§3.1.2 says they are).
- The MathML DOM (`MathMLElement`, its event handlers, `style`, `dataset`, `focus`) is not on main: it is
  commit af39f16fc on `wip/dom-html`. `mathml/relations/html5-tree` (1,529 subtests) waits on it.
- `text-transform: math-auto` is computed but text is not transformed.
- `mtd` padding, `mfrac` `padding-inline` of appendix A are not read by the layout profile (lengths in `ex` and
  `em`); the walk gives an `mtd` with no padding the appendix's padding.

## Measured

See the table at the end, filled from the cloud checks.
