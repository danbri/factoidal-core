# Measured first refusal reasons

From the corrected full601 stable baseline. These are first observed reasons,
not counts of independent feature coverage; later dependencies may be masked.
Original paths below are unchanged. Counts concern scored unsupported/rejected
rows after independent browser-oracle availability checks.

## unsupported

- 41: `Error: page.evaluate: Error: SVG profile: unsupported SVG element: defs`; `svg/linking/reftests/url-processing-whitespace-002.svg`, `svg/painting/currentColor-override-pserver-fill.svg`, `svg/painting/currentColor-override-pserver-stroke.svg`.
- 25: `Error: page.evaluate: Error: SVG profile: foreign/non-SVG element: meta`; `svg/coordinate-systems/viewBox-zero-disables-rendering-marker.svg`, `svg/coordinate-systems/viewBox-zero-disables-rendering-pattern.svg`, `svg/coordinate-systems/viewBox-zero-disables-rendering-symbol.svg`.
- 15: `Error: unsupported CSS property: border`; `svg/coordinate-systems/abspos.html`, `svg/linking/reftests/svgview-attribute-order.html`, `svg/linking/reftests/svgview-escaped-semicolon.html`.
- 14: `Error: page.evaluate: Error: SVG profile: unsupported CSS property: width`; `svg/styling/nested-svg-sizing-auto.tentative.svg`, `svg/styling/nested-svg-sizing-calc-size.tentative.svg`, `svg/styling/nested-svg-sizing-calc.tentative.svg`.
- 12: `Error: unsupported HTML layout element: img`; `svg/as-image/external-resource-inline-sheet.html`, `svg/coordinate-systems/outer-svg-intrinsic-size-003.html`, `svg/coordinate-systems/outer-svg-intrinsic-size-004.html`.
- 11: `Error: page.evaluate: Error: SVG profile: unsupported SVG element: text`; `svg/text/reftests/lang-attribute.svg`, `svg/text/reftests/multiple-textpaths.svg`, `svg/text/reftests/textpath-path-attr-ancestor-transform.svg`.
- 8: `Error: unsupported CSS property: fill`; `svg/extensibility/foreignObject/isolation-with-html.html`, `svg/extensibility/foreignObject/isolation-with-svg.html`, `svg/linking/reftests/href-use-element.html`.
- 8: `Error: page.evaluate: Error: SVG profile: unsupported CSS property: rx`; `svg/shapes/ellipse-01.svg`, `svg/shapes/ellipse-02.svg`, `svg/shapes/ellipse-03.svg`.
- 7: `Error: unsupported CSS property: overflow`; `svg/extensibility/foreignObject/foreign-object-scale-scroll.html`, `svg/extensibility/foreignObject/scroll-transform-nested-stacked-children.html`, `svg/extensibility/foreignObject/stacking-context.html`.
- 7: `Error: page.evaluate: Error: SVG profile: unsupported CSS property: cx`; `svg/geometry/reftests/circle-001.svg`, `svg/geometry/reftests/circle-002.svg`, `svg/geometry/reftests/circle-003.svg`.

## rejected

- 3: `Error: page.evaluate: Error: SVG profile: viewBox dimensions must be positive`; `svg/coordinate-systems/viewBox-zero-disables-rendering-001.svg`, `svg/coordinate-systems/viewBox-zero-disables-rendering-002.svg`, `svg/coordinate-systems/viewBox-zero-disables-rendering-003.svg`.
- 2: `Error: page.evaluate: Error: SVG profile: negative ellipse radius`; `svg/geometry/reftests/ellipse-005.svg`, `svg/geometry/reftests/ellipse-006.svg`.
- 2: `Error: invalid CSS number`; `svg/linking/reftests/href-textPath-element.html`, `svg/painting/reftests/mask-percentage.html`.
- 1: `Error: viewBox dimensions must be positive`; `svg/coordinate-systems/viewBox-zero-disables-rendering-contexts.html`.
- 1: `Error: page.evaluate: Error: Invalid SVG input ABI`; `svg/embedded/image-large-bitmap.svg`.
- 1: `Error: numeric magnitude exceeds profile bound`; `svg/painting/reftests/non-scaling-stroke-precision-loss.html`.
- 1: `Error: page.evaluate: Error: SVG profile: negative pathLength`; `svg/path/distance/pathlength-path-negative.svg`.
- 1: `Error: page.evaluate: Error: SVG profile: invalid path token`; `svg/path/error-handling/render-until-error.svg`.
- 1: `Error: page.evaluate: Error: SVG profile: negative rectangle dimensions`; `svg/shapes/reftests/disabled-shapes-01.svg`.
- 1: `Error: page.evaluate: Error: SVG profile: invalid SVG number: var(--length,100px)`; `svg/styling/css-var-on-length-attributes-03.svg`.
