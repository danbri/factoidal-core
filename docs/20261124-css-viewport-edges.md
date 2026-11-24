# Resolve margins and padding with viewport units

W3C uses a full-width breakout with negative `margin-inline: -50vw` and a centred wrapper with `padding-inline: 5vw`. The rendering cascade previously converted these declarations against the property table's 800px default. In a fixed W3C homepage capture, equivalent explicit pixel rules changed the headline's left edge from 480px to 160px at a 1440px viewport and from -120px to 24px at 480px.

Preserve simple `vw` and `vh` edge declarations through the cascade and resolve them before percentage margins, intrinsic sizing and box-sizing conversion. This uses the same longhands for physical, shorthand and logical declarations. Preserve viewport edges through CSS-wide copying, and clear the earlier edge when a later value replaces it. Layout and repaint reuse compare the deferred margin and padding state.

The Lean equivalence for a breakout with two viewport-width margins and one viewport-height padding edge states that resolving that style gives the explicit pixel style, including all untouched fields. A separate theorem covers the layout fast path for empty deferred edges. Native geometry checks and WPT results are separate evidence. Viewport calculations such as `calc(1vw + 2px)` still need general edge calculation support.

Related to [desktop acceptance](https://github.com/danbri/factoidal-core/issues/712).

The shared-snapshot W3C replay showed the restored hero and logo at 480 and 1440 px. Its stricter CSSOM assertion found that the script width and height request subtracted padding from the unresolved cascade. Apply the same viewport edge conversion as the layout before subtracting padding in that request. The explicit pixel comparison uses physical sides, so it also serves as an independent reference for the viewport shorthand declarations.
