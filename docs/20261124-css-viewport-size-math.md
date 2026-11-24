# Resolve CSS sizing functions against the layout viewport

The W3C homepage sizes its header logo with a clamp combining rem and viewport units. In an independent flex header built from a square SVG and a responsive logo wrapper, the November 22 engine gave the wrapper and image the same 89.744 CSS px width at 1280px and 480px. Explicit pixel controls produced the widths expected for those viewports.

Keep the parsed calculation and the element's font size through the cascade. When the layout viewport is known, use the existing CSS Values evaluator to turn the calculation into a nonnegative pixel size. This applies to width, height and their min and max values, including logical declarations that are mapped to these properties by the cascade.

The stored value uses the CSS Values evaluator's existing font-unit model. Expressions with a containing-block percentage basis continue through the existing size paths. Repaint shape comparison conservatively rejects reuse when a compared size includes the new value. The existing representation and path for simple pixels, percentages, and affine percentage calculations are retained.

The included Lean theorem states that every pixel size returned by the evaluator is nonnegative. Six guards cover three viewport widths, min, the nonnegative range, and exclusion of a function needing a containing-block percentage. At a 16px root font, the result at 1280px is 119.4944px and reaches the 120px cap at 1440px. The native build checks which declarations and guards compile. Browser geometry and visual acceptance need separate measurements.

Related to [desktop acceptance](https://github.com/danbri/factoidal-core/issues/712).

An ordinary computed-value calculation such as `calc(10px * 2)` stays on the existing path. The deferred path tests the calculation tree for units whose pixel conversion changes with the viewport. Native CI on the preceding candidate compiled the nonnegative proof and then caught the constant-calc regression in the existing cascade tests.
