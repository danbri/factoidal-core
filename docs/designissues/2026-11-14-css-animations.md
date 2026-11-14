# CSS animations, CSS transitions and Web Animations in the engine (2026-11-14)

Scope: the animation model of the page (Web Animations 1, CSS Animations 1, CSS Transitions 1, CSS
Easing 1), the interpolation of computed values, and the script interfaces. Code:
`formal/lean4/L4Factoidal/Rendering/Animation/*.lean`, `Rendering/Style.lean` (`withAnimated`),
`WasmVM/Hosts/Page.lean` (`animOp`, `measureNow`), `labs/demos/foafnaut/WebDocument.lean` (`measure`),
`tools/wasmvm/quickjs/prelude.js` (section "animations").

## Why

The full WPT run of 2026-11-13 (engine 78d9a6d05) lost 56,890 subtests in 322 files that use
`css/support/interpolation-testcommon.js`, 4,192 of 4,256 in `web-animations/`, about 3,400 in
`css/css-transitions` and 1,400 in `css/css-animations`. The engine had no animation of any kind.

What one interpolation subtest needs, read from the helper:

1. `CSS.supports(property, value)` is true for the `from`, `to` and `underlying` values. 38,796
   subtests failed here on `from` and 3,433 on `to`: 253 properties, 30 of them in the old style
   profile. This is the property table (`Rendering/CssValues`, a separate piece of work).
2. One of six ways to be half way through an animation:
   - CSS Transitions: the value is set, the style is read (`getComputedStyle`), then
     `transition-duration: 100s`, `transition-delay: -50s`, a timing function, `transition-property`
     (the property, or `all`) and the new value are set. Twice more with
     `transition-behavior: allow-discrete`.
   - CSS Animations: a `@keyframes` rule is appended to a `style` element and the element gets
     `animation-name`, `animation-duration: 100s`, `animation-delay: -50s` and a timing function.
   - Web Animations: `element.animate(keyframes, {fill: 'forwards', duration: 100000, easing})`,
     `pause()`, `currentTime = 50000`.
3. `getComputedStyle(target)` for the property equals `getComputedStyle` of a second element whose
   `style` holds the expected value, both rounded to two decimals.

The timing function is `steps(1, end)` for 0, `steps(1, start)` for 1, `linear` for 0.5, and
`cubic-bezier(0, b, 1, b)` with b = (8y - 1)/6 for any other progress y: at input 0.5 that curve's
parameter is exactly 0.5 and its output exactly y.

## Design

### Numbers (`Fix`)

Every number of the model is an `Int` in units of 10⁻⁹: times in ms, progress, lengths, colour
channels. One rounding (`roundDiv`). The reason is proof: the end points, the identity and the range of
an interpolation are theorems about integers, with no test of floating point. A cubic Bézier is solved
by bisection over exact integers (numerators over 10²⁷), so the tests' curve gives exactly 0.3, 0.6,
1.5, -0.3.

### Values (`Value`)

The cascade gives a property's computed value as canonical CSS text. `Value.parse` reads it into a
flat list of tokens (number, dimension, colour, mixed length-percentage, identifier, function name,
parenthesis, comma, slash). Two values interpolate when the lists have the same shape: numeric
components move, everything else must be equal; `px` and `%` combine to `calc(P% + Lpx)` (also at the
two ends, as browsers compute it); colours interpolate premultiplied in sRGB. Other pairs are discrete
(flip at 50%). The result is text again, and goes back through the cascade, so `getComputedStyle`
serializes it with the same code as any value.

A property's `Kind` (`Engine.kindOf`) says what its definition adds to that:

| Kind | Properties | Rule |
|---|---|---|
| `generic` | most | component-wise by shape, else discrete |
| `nonNegative`, `integer`, `positiveInteger`, `unit`, `fontWeight` | sizes, `z-index`, `column-count`, `opacity`, `font-weight` | the range or rounding of the property |
| `visibility`, `avoid` | `visibility`; `display`, `overlay`, `content-visibility` | the shown value holds between a hidden one and another |
| `discrete` | images, counters | always flips |
| `transformList`, `filterList` | `transform`; `filter`, `backdrop-filter` | functions of one name pair up; the shorter list is padded with identities; `add` joins the lists, `accumulate` sums over the neutral value |
| `shadowList n` | `box-shadow` (4), `text-shadow` (3) | shadows pair up, padded with transparent ones; blur not negative |
| `translate`, `scale`, `rotate` | the individual transforms | missing components filled; `rotate` about one axis, or the shortest arc between two (quaternions, `Float`) |
| `sides` | `border-image-*`, `mask-border-*` | one to four values as four |
| `gridTracks` | `grid-template-columns/rows` | each track size by itself, discrete where two do not combine; no auto-repeat |
| `repeatable`, `gapList` | `background-position/size`, `mask-position/size`; gap rules | lists repeated to their least common multiple |
| `ratio` | `aspect-ratio` | by the logarithm (`Float`) |
| `offsetRotate` | `offset-rotate` | `reverse` is `auto` + 180deg |
| `shape` | `clip-path`, `shape-outside`, `offset-path` | `inset()`, `rect()`, `xywh()` as one form; `path()` data as absolute commands, number by number; no keyword radii |
| `radius`, `fontStyle` | corner radii; `font-style` | two equal radii once; `normal` is `oblique 0deg` |

The value layer was written against the tests' own cases: the 2,345 cases of the 322 interpolation
files were extracted with a stubbed `test_interpolation` and run through `CssValues.computed`,
`Value.interpolate` and the helper's `normalizeValue` with no engine (the sources compiled as one file,
`lean --run`). That check is a development tool, not a score.

Not done: modern colour spaces, `shape()`, grid line names, `corner-shape`.

### Transform lists (`Matrix`, `Value`)

CSS Transforms 2 §9. A transform list is read into functions by primitive (`Value.TF`: translate,
scale, rotate, skew, matrix, perspective). Two lists pair up function by function, the shorter padded
with identity functions (`identityFn`). A pair of one primitive interpolates by component
(`lerpFn`): translations, scales and skews directly; rotations about one direction by the angle, a
rotation by 0 taking the other's axis, two directions as matrices; perspectives by the reciprocal of
the distance (the entry of the matrix; `none` is 0); `matrix()` and `matrix3d()` by decomposition.
From the first pair of two primitives, the rest of each list is one 4×4 matrix and the two matrices
interpolate (`Matrix.blend`). Lists whose functions have the same names and argument counts and no
matrix, perspective or `rotate3d()` keep the old argument-by-argument path and their function names
(so a percentage stays a percentage of the box).

`skew()`, `skewX()` and `skewY()` share no primitive (CSS Transforms 1 §13): a pair of two of them
goes to the matrix path (`transform-skew-composition.html` expects exactly that for an accumulated
`skewX` and `skewY`). The individual `rotate` property adds two rotations about one direction by their
angles, and about two directions as the product of their quaternions.

`Matrix` is the arithmetic alone, in `Float`: products, the matrices of the functions, an inverse
(Gauss–Jordan, for the perspective part), the 3D decomposition of CSS Transforms 2 §9.2 (perspective,
translation, scale, three skews, a quaternion), spherical interpolation along the shorter arc, and
recomposition; and a 2D decomposition (translation, rotation, one shear, scale) with the rules of CSS
Transforms 1 §12.2.2 for flips and the short way round, used when both matrices are 2D. The 2D form
was chosen from the expected values of `transform-interpolation-005.html` (the remainder matrix of
the 2D pseudo-code in the specification does not compose back when there is a shear; a single shear
does, and gives the tests' numbers). A matrix with no inverse does not interpolate: the values flip
at 50%.

Accumulation (`accFn`, `Matrix.accumulate`): translations and skews add, scales add about 1,
rotations about one direction add their angles, perspectives add reciprocals, matrices accumulate
their decomposed values (rotations follow one another). Addition joins the lists.

### Resolved values of the transform properties

`getComputedStyle` gives `transform` as one `matrix()` or `matrix3d()` (CSS Transforms 1 §15; the
matrix is 2D when its entries say so), and the percentages of `transform-origin` and
`perspective-origin` as lengths (`Animation.Computed.resolvedAt`). The reference box is the element's
border box from its computed width, height, padding and border when those are lengths
(`Computed.boxOf`): no layout is made for it; with an `auto` or percentage size the computed value
stands. The engine itself keeps reading the list of functions (`valueOf`), which is what
interpolates. Matrix entries are written with six significant digits (`Fix.formatSig`).

### Easing functions (`Easing`)

Keywords, `cubic-bezier()`, `steps()` and `linear()` (CSS Easing 2 §2.2: the stops as points, a
missing input spread evenly between its neighbours, an input never below the one before it, a stop
with two inputs as two points; outside the points the first and the last segment continue).
Serialization writes every point with its input.

### Timing, effects, playback (`Timing`, `Effect`, `Model`)

Each procedure of Web Animations 1 is one pure function named for its section: phases and progress
(§4.6–§4.10), computed keyframe offsets and the effect value (§5.3), `play`, `pause`, `finish`,
`cancel`, `reverse`, the setters and "update the finished state" (§4.4). A procedure's effects on the
animation's promises and its events are a list of acts that the script objects apply in order.

### CSS (`Css`, `Engine`)

`@keyframes` rules are read from the sheets' text (again only when the text changes). The
`animation-*` and `transition-*` longhands of an element are a small cascade of their own over the
rules that matched it and its `style` attribute, with both shorthands expanded.

A style change (`Engine.styleChange`) runs when a script reads style or layout after a change:
CSS animations follow `animation-name`; a transition starts for each property whose computed value
differs from the value at the last style change (the answers of the previous layout are kept as the
before-change style), when the values interpolate or `allow-discrete` is set.

The effect stack (`Engine.overrides`) gives, for each element and property, the value of the top
animation in composite order (transitions, CSS animations, script animations).

### In the cascade

Animated values are not patched onto answers. They enter the cascade as declarations
(`CSS.withAnimated`): an animation's value has origin 2 (above the `style` attribute's normal
declarations, below every `!important`), a transition's has origin 3 and is important (above all), as
CSS Cascade 4 §6.1 orders them. So layout, paint, inheritance and `getComputedStyle` take the same
values, and a descendant inherits an animated value.

### Time

The document timeline's time is the event loop's clock at the start of the current task or frame
(`Host.tickTimeline`). It does not move while a script runs, so an animation made and read in one task
is read at exactly its start, as in a browser.

### Script interfaces

`Element.animate`, `Element.getAnimations`, `Document.getAnimations`, `document.timeline`,
`Animation`, `AnimationEffect`, `KeyframeEffect`, `DocumentTimeline`, `AnimationPlaybackEvent`,
`CSSAnimation`, `CSSTransition`. The objects hold a number; each call is one JSON request to Lean
(`node_query` ops 60 to 68). The part of "process a keyframes argument" that reads the script's object
(its own enumerable members, in order, as text) is in the prelude; every check and the merge are Lean.

## Cost

Cost test (`Animation.Computed`, `restyledCount`): styling one element again on a page of 10 and of
400 paragraphs styles the same two nodes (counted from outside, by rules that mark every element they
are asked for).

A page with no animation and no `animation`/`transition` declaration: per layout read after a change,
one pass over the rules' declarations (two prefix tests each) and one over the elements' `style`
attributes (two substring searches each). No table is built, no second cascade runs
(`State.idle`, `withAnimated_none`). Timings: see "Measured".

A page with animations: two cascades per style change (one without the animated values, one with),
and the engine's work per animated element.

## Proved, tested, open

Proved (axioms: propext, Classical.choice, Quot.sound):

- `Fix.lerp_zero`, `lerp_one`, `lerp_self`, `lerp_between`, `mul_one`, `mul_between`, `roundDiv_mono`,
  `clamp_between`, `clamp_idem`.
- `Easing.evalSteps_mono` (a step function does not decrease, over all inputs), `stepOf_range`,
  `eval_linear`, `eval_ends` (keyword and cubic easings map 0 to 0 and 1 to 1).
- `Easing.evalPoints_identity` (`linear(0, 1)` is the identity at every input), `evalPoints_ends`
  (two points at 0 and 1 give their outputs there).
- `Easing.segment_mono`, `segment_between`, `evalPoints_two`, `evalPoints_two_mono`: one segment of
  `linear()` whose output does not fall is monotone in its input at every input, and between its two
  inputs it stays between its two outputs; a two-point `linear(a, b)` with a ≤ b does not decrease.
- `Reads.wrote_other`, `Reads.wrote_version` (`Hosts/Page`): a write that is not of a `style`
  attribute forgets the noted elements, and every `wrote` leaves the note exact for the new version;
  a write path that raises the version another way leaves `styleVersion` behind, and the next measure
  is of the whole document.
- `Easing.bezNum_mono`: the x of a cubic Bézier with x1 and x2 in [0, 1] does not decrease with the
  parameter, exactly (over integers): the assumption of the bisection, and the reason CSS Easing 1
  restricts x1 and x2. Proof: the difference is affine in x1 and in x2, so it is a weighted sum of the
  four corner cases, each `(t - s)` times a sum of squares or of products of non-negative numbers
  (`bez_mono`, the polynomial identity by `grind`).
- `Value.lerpTok_zero`, `lerpTok_one` (at progress 0 and 1 each component of a component-wise result
  is the start or end component, or that component as a mixed length-percentage with the other part 0),
  `discrete_ends`, `interpolate_self`, `lerpTok_num`, `lerpTok_dim`, `lerpList_length`,
  `nonNegative_range`, `unit_range`.
- `Timing.simple_range`, `directed_range`, `at_idle`, `before_no_fill`, `after_no_fill`.
- `Effect.fromTo_zero`, `fromTo_one` (the effect value of from/to keyframes at 0 and 1 is the
  interpolation of the two computed values there).
- `Player.idle_iff`, `cancel_idle`, `hold_fixed`, `running_time`.
- `CSS.withAnimated_none`, `Css.nth_lt`.
- Transform functions: `lerpFn_scale_zero`, `lerpFn_scale_one`, `lerpFn_scale_self`,
  `lerpFn_scale_between` (each component between the two for a progress in [0, 1]),
  `lerpFn_skew_ends`; `samePrimitive_identityFn` (padding never sends a pair to the matrix path),
  `identityFn_idem`; `accFn_scale_identity` (the identity scale is neutral for accumulation),
  `accFn_skew_add` and `addTok_num_assoc` (accumulated angles and added numbers are sums: commutative
  and associative). `Matrix.build_size`, `mul_size` (a product has 16 entries).

Tested only (`#guard`): the Bézier values of the tests' easings; parse then serialize of easings and of
computed values; the three test paths over a model page; the cascade order of animated values; the
keyframes argument; the timing dictionary's checks; the playback sequences of the tests.

Open:

- That `solveT`'s bisection ends at the nearest parameter is tested, not proved (the x it searches
  is proved monotone: `Easing.bezNum_mono`).
- parse∘serialize = id for values and easings is tested, not proved.
- Reversing-adjusted start values of transitions; `animation-range` and timelines other than the
  document's.
- `rotate` between two axes and `aspect-ratio` use `Float` (sqrt, sin, acos, log, exp): tested, not
  proved. The list kinds (padding, joining, least common multiple) are tested, not proved.
- Matrices are `Float`: decomposition then recomposition gives the matrix back, the ends of
  `Matrix.blend` are its two matrices, and the numbers of the WPT cases are `#guard`s within 10⁻⁶; none
  of that is a theorem. A transform list with a percentage and two primitives does not interpolate
  (it would need the box at the time of the style change).
- Animated values are in the cascade that scripts read (computed style, layout reads). The frame the
  window paints does not take them yet: an animation is visible to scripts, not on screen.
- An animation object is never freed while its page lives.
- The frame's part of the model is driven from a frame callback the prelude asks for, so it runs with
  the page's own frame callbacks in request order, not before all of them.

## Measured

To be filled from the cloud checks (subtests before and after per directory, timings).
