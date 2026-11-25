# Keyboard focus outlines

The browser's default style sheet assigns a two-pixel automatic outline to
elements matching `:focus-visible`. The same CSS cascade handles author
outlines and suppression. The automatic ring uses adjacent light and dark
bands. An author-supplied colour can override the automatic colours.

The scene draws outlines outside the box's own overflow clip and inside any
ancestor clip. The paint has no hit-test source. Layout and scroll calculations
continue using the original border box. An inline element spanning several
lines draws one ring per fragment. Rounded solid outlines reuse the renderer's
rounded border painter.

Lean statements in this change cover the ordinary declaration path for
`outline-style: none`, absence of outline paint for that style, and equality
of block frame boxes, glyph runs, height and bottom margin under a change to
the outline record. An executable guard exercises the cascade and compares
scene paint and geometry for focused, unfocused, pointer-focused and
author-suppressed links. The statements and the guard must compile in the
native and corpus checks. Rendering across nested stacking contexts and
nonrectangular multiline outlines still need separate verification.

Validation should include the pinned programmatic focus pair and CSS outline
tests, plus visible desktop input and author override controls.

[CSS Basic User Interface, outline properties](https://www.w3.org/TR/css-ui-4/#outline-props)
