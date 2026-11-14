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
components move, everything else must be equal; `px` and `%` combine to `calc(P% + Lpx)`; colours
interpolate premultiplied in sRGB. Other pairs are discrete (flip at 50%). A property's `Kind` adds its
range: not negative, whole number, [0, 1], font weight, `visibility`. The result is text again, and
goes back through the cascade, so `getComputedStyle` serializes it with the same code as any value.

This is one representation for every property the table computes: a property needs no code here unless
its animation type is more than its value's shape. Transform lists of different functions, filters and
shadows against `none`, and `path()` strings are not done yet (open list).

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
- `Value.interpolate_zero`, `interpolate_one`, `interpolate_self`, `lerpTok_num`, `lerpTok_dim`,
  `lerpList_length`, `nonNegative_range`, `unit_range`.
- `Timing.simple_range`, `directed_range`, `at_idle`, `before_no_fill`, `after_no_fill`.
- `Effect.fromTo_zero`, `fromTo_one`.
- `Player.idle_iff`, `cancel_idle`, `hold_fixed`, `running_time`.
- `CSS.withAnimated_none`, `Css.nth_lt`.

Tested only (`#guard`): the Bézier values of the tests' easings; parse then serialize of easings and of
computed values; the three test paths over a model page; the cascade order of animated values; the
keyframes argument; the timing dictionary's checks; the playback sequences of the tests.

Open:

- x-monotonicity of a cubic Bézier with x1, x2 in [0, 1] (the bisection assumes it) is not proved.
- parse∘serialize = id for values and easings is tested, not proved.
- CSS animation and transition events; reversing-adjusted start values of transitions; `linear()`.
- Transform lists of different functions (matrix interpolation), filter and shadow lists against
  `none`, `path()`, repeatable lists of different lengths.
- An animation object is never freed while its page lives.
- The frame's part of the model is driven from a frame callback the prelude asks for, so it runs with
  the page's own frame callbacks in request order, not before all of them.

## Measured

To be filled from the cloud checks (subtests before and after per directory, timings).
