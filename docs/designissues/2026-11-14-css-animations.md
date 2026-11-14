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

### Style changes with no read by a script

A style change is made when a script reads a style or a layout (`Host.measured`). A browser also
makes one in every frame (HTML §8.1.7.3 "update the rendering"), so there a transition starts and
its events come even when the script only wrote a style and then waits. A script can see that
difference without a read in one way: by the events. So a page gets the frame's style change exactly
when a script of it listens for an animation or transition event (`Page.animationEventTypes`,
`Reads.animEvents`, set by the listener import): after the listener, and after each later write that
may change a style, the page asks for its animation frame (`Host.afterWrite`), and the frame makes
the styles of the document as written (`Host.frameStyles`) before it runs "update animations and send
events". A frame after no such write (the time alone, timers, listeners, a script's change of an
animation: `Reads.styleWriteAt`) measures nothing. A page with no such listener is as before
(`Host.afterWrite_quiet`, `Host.frameStyles_quiet`).

Found on `css/css-transitions/events-001.html` to `-008`, `css/css-animations/animation-iteration-event-001.html`
and some thirty more files, all TIMEOUT with no subtest: they set a style, add a listener and wait.
Not covered: a script that neither reads nor listens and later reads a time (`getAnimations()` makes
the style change then, so the animation starts late), and the window, which does not paint animated
values yet.

### Which elements a style change looks at

CSS Transitions 1 §3 compares, for each element, the before-change style with the after-change
style, and takes the before-change style "with any styles derived from declarative animations
updated to the current time". So an element whose declarations did not change has two equal styles,
whatever time passed and whatever a script did to an animation: nothing starts for it and nothing
is cancelled. The host therefore makes the style change for the written elements only
(`Host.measureNow`): when nothing was written (a frame, or a script's `cancel()`, `currentTime`,
`play()`), there is none, only the effect stacks at the new state; on a page with no kept styles
the whole style change is skipped when nothing a style reads was written since the last measure
(`Reads.styleWriteAt`). Before, a time or an animation changed by a script made the style change of
every element against the kept styles of an earlier time: a transition a script had cancelled
started again from its last value, and an element following an ancestor's running transition
(an `em` length under a font-size transition) started one of its own at each such step.

A frame is also needed while an animation holds acts that no script object took (a promise to
resolve or reject): an animation made and cancelled by style in one task has never been ticked, and
its `finished` promise was left pending (`Engine.needsFrame_out`).

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

Found by timing one case of `css/support/interpolation-testcommon.js` (transitions, transitions of
`all`, CSS animations; 18 targets, 89 nodes) through `Host.measureNow` under the interpreter (a whole
cascade of that document: 31 to 41 ms there), and fixed:

| step | before | after |
|---|---|---|
| forced read after the style writes of a transition target (`transition-property: rotate`) | 34 to 50 ms | 6 to 8 ms |
| the same with `transition-property: all` | 37 ms | 16 ms |
| the first read after the sheet changed and 18 animations exist | 1,397 ms | 320 ms |
| a read after a write of another element's `style` attribute | 3 to 5 ms | 2 to 3 ms |
| the same after the page made a node in no tree (`createElement`, as the tests' URL comparison does) | a whole cascade | 1 to 3 ms |
| a read in a frame where only the time moved (18 animations) | about 320 ms (a whole style change) | 51 ms |

- The declarations text of an element (`Computed.declarationText`) held the animated values of the
  style it was read from, so the style without them never compared equal to the kept style with them:
  every element with an animation had each of its declared longhands computed twice at every style
  change. The animated values (origins 2 and 3) are now left out of it.
- The two styles of an element are compared only when one of its transitions is of `all`; a
  transition of named properties looks at those properties.
- When the rules that match an element are the same and neither its font, colour nor flow changed,
  the longhands compared are those its two `style` attributes declare differently
  (`Computed.styleAttributeDiff`).
- A frame in which nothing was written and no script changed an animation makes no style change:
  the effect stacks at the new time and the animated elements styled again (`Host.measureNow`).
- A write that changes nothing in a document's tree (a new node, a clone, a change of a node that is in
  no tree: `Page.detachedWrite`) keeps the kept styles; `CSS.restyleWith` takes an arena that grew.
- A write of an element's `class` is noted under the element's parent (`Reads.wrote`, `subtree`).
  When no rule of the page has `:has()` (`CSS.attributesReachParentOnly`, kept as `Carry.parentOnly`)
  and the noted subtrees hold at most `Page.subtreeLimit` (512) nodes, the next measure styles those
  subtrees again and makes the style change for the elements in them, as for a `style` attribute
  write; otherwise the styles are made whole, as before. Why the parent: without `:has()` the matching
  of an element reads its ancestors, the earlier siblings of itself and of its ancestors, and for
  `:nth-child(… of …)` the siblings of those, so a class is read only for elements under its
  element's parent. Found on `css/css-transitions/properties-value-001.html` and its two `inherit`
  companions (STALL in check 43586303902): each of 580 tests writes `class` on two elements five
  times and reads after each, and every read made a cascade of the document and a style change over
  the 50 running transitions of its slice (`transition: all`: both styles of each compared).
  Timed on the start phase of that harness through `Host.measureNow` under the interpreter (per
  measure, same values read on both paths): 10 tests in a slice 187 ms whole, 56 ms partial; 50 tests
  3,634 ms whole, 279 ms partial. What is left grows with the slice because every rule of the slice
  ends in the same class (`#test-N .transition`), so each element tries all of them (the rule buckets
  are by the last compound); the whole path paid that for every element.

## Bounds

What a page controls, and what bounds it:

- The animations and the effects of a page's state: at most `Engine.maxAnimations` (65,536) of each,
  counting those that ended (none is freed while the page lives). At the bound a constructor answers
  `QuotaExceededError` and the state is unchanged (`Api.create_full`, proved); a CSS animation or
  transition does not start (`Engine.startTransition_full`, proved; `updateAnimations` reads the same
  `State.full`, tested by reading only). One addition is one record (`addEffect_size`, `addAnim_size`).
- The work of a style change and of a frame: one pass over those records and over the elements that
  declare an animation or a transition; bounded with them, not proved as a count.
- The keyframes of one effect, the stops of `linear()`, the commands of a `path()`: bounded by the
  text they come in (a `node_query` text is at most `Hosts.Dom.maxString`; a sheet at most its
  reader's limit); every loop over them is a `for` over that text or list. No count of their own.
- The partial path after `class` writes: at most `Page.subtreeLimit` (512) nodes are read for it
  (`subtreesWithin_length`, proved); a larger subtree, or more than 32 noted elements, takes the whole
  path. The partial path after `style` attribute writes has no such count: the subtree of the written
  element, whatever its size.
- Recursion: none in `Rendering/Animation` survives as a call (the tail-recursion gate passes).
- Missing: a bound on the time of one style change as a number of steps; ended animations are kept.

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
- `Value.channel_range` (a written colour channel is in 0 to 255), `snapWidth_pos`, `snapWidth_le`
  (snapping widens a line by no more than the slack of a rounding boundary), `snapWidth_idem`;
  `Engine.withCurrentColor_plain` (a value with no `currentcolor` is itself: the colour is not read).
- `Page.detachedWrite_connected`: a write whose node (or parent) is in a document's tree is never taken
  as changing nothing there. `CSS.restyleWith_nil` (same arena: the styles given), `restyleWith_nil_size`
  (an arena that grew: a style for every node). `Computed.styleAttributeDiff_same`: a longhand two
  `style` attributes declare alike is not in their difference.
- `Page.subtreesWithin_length` (the nodes the partial path reads after `class` writes are at most
  `subtreeLimit`), `Reads.wrote_subtree`, `Reads.wrote_keeps_subtree` (a `class` write marks that a
  subtree is to be read again, and only a measure takes the mark away).
- `Engine.needsFrame_out` (an animation with untaken acts keeps the page asking for a frame);
  `Value.add_shape_replace` (two shapes that do not interpolate do not add or accumulate: the
  keyframe's value replaces); `Value.originWords_dims` (an origin of lengths is not rewritten).
- `Host.afterWrite_quiet`, `Host.frameStyles_quiet` (a page with no listener for an animation or
  transition event: a write asks for no frame and a frame measures nothing), `Host.afterWrite_listens`
  (a new listener marks the page), `Host.frameStyles_fresh` (a frame whose kept layout is of the last
  style write or later measures nothing), `Reads.wrote_neutral`, `Reads.wrote_style` (only a write that
  may change a style moves `styleWriteAt`), `Host.askAnimationFrame_reads`.
- `Reads.wrote_other`, `Reads.wrote_version` (`Hosts/Page`): a write that is neither of a `style`
  nor of a `class` attribute forgets the noted elements, and every `wrote` leaves the note exact for the new version;
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

- That the styles after a `class` write are those of the parent's subtree styled again when no rule
  has `:has()` is argued from the selector grammar and tested (three documents against a sheet with
  descendant, child, `+`, `~`, `:not()`, `:is()`, `:nth-child(… of …)`, `:nth-last-child(… of …)` and
  attribute selectors, compared with the whole cascade); it is not proved over `DOM.Selectors.matches`.

- That `solveT`'s bisection ends at the nearest parameter is tested, not proved (the x it searches
  is proved monotone: `Easing.bezNum_mono`).
- parse∘serialize = id for values and easings is tested, not proved.
- Reversing-adjusted start values of transitions; `animation-range` and timelines other than the
  document's.
- Corner shapes (`Value.lerpCorner`: powers and logarithms of 2 in `Float`) are tested against the
  WPT numbers, not proved; `shape()` against `path()` does not interpolate yet.
- A number of a declaration block kept as text has six decimals, so an easing set through
  `element.style` is read back rounded; results within a thousandth of a rounding boundary are taken
  as on it (`Value.slack`). The block could keep the numbers as written instead (css-values).
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

Branch checks (`branch-wpt.yml`, Linux; development checks of the selected names, not scores). Names:
`/web-animations/`, `/css/css-transitions/`, `/css/css-animations/`, `/css/css-easing/`, the 68 path
prefixes of the files that use `css/support/interpolation-testcommon.js`, and every 40th name of the
full list. Baseline: the full run of main d799500c7 (before any of this was on main).

| check | ref | interpolation files (56,185) | web-animations (4,252) | css-transitions (3,439) | css-animations (1,431) | css-easing (167) |
|---|---|---|---|---|---|---|
| baseline | main d799500c7 | 14,823 | 117 | 467 | 685 | 95 |
| 43574527916 | 4 commits on the cascade branch | 48,829 | 3,668 | 1,228 | 983 | 116 |
| 43575885979 | + `linear()`, Oklab, line widths | 48,623 (3 pages STALL) | 3,675 | 1,229 | 1,007 | 121 |
| 43582584406 | + the cost fixes, corner shapes, arc flags, rounding slack: merged as cee52ef58 | 50,161 | 3,675 | 1,405 | 1,007 | 121 |

Merged: main 335ab3b69..cee52ef58, +40,182 subtests on these names in the check.

Timings of the 774 pages of those names (wall time of the test processes, Linux runners): 3,138 s in
the first check, 1,740 s in the merged one; pages of 30 s or more: 20, then 8; the three pages of
URL-valued properties that took 264 s or stalled past 300 s (`mask-image-`, `border-image-source-`,
`mask-border-source-interpolation`) take 7.9 s, 4.0 s and 4.8 s. Others, first check then merged, with
the time before the engine existed (when most of their subtests failed) in brackets:
`rotate-interpolation` 16.4 s, 7.7 s (5.8 s); `border-image-width-interpolation` 112 s, 7.1 s (28 s);
`line-height-interpolation` 54.8 s, 8.5 s (24.5 s); `row-rule-inset-interpolation` 72 s, 15.8 s (48 s). The slowest is
`css-transitions/properties-value-inherit-001.html` (219 s: a hundred transitions read every frame).

A page with no animation and no `animation`/`transition` declaration: the every-40th sample (2,347
names) took 1,320 s before the engine and 1,366 s with it on a later main (other merges are in that
difference; no page of the sample became a STALL or a TIMEOUT by this work).
