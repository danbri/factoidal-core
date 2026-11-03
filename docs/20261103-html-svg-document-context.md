# Original HTML document context for embedded SVG

The HTML frontend now constructs one namespace tree from the original Lean DOM
arena and shares one source-bound SVG reference context across its embedded
roots. Hidden roots still contribute fragment IDs. The selected root's source
path retains every text/comment child index; root attribute normalization does
not change the indexed document or referenced targets. No host DOM extraction,
XML serialization or reparsing supplies candidate geometry.

This addresses the missing cross-root target in the pinned original
`svg/linking/reftests/href-use-element.html`. Seven new source guards cover
hidden-root lookup, href precedence, mutation, preserved comment/text paths,
global SVG paint rules and explicit resource/style refusals. The whole updated
HTML/DOM/CSS/layout/font/SVG closure passes `build-web-render.sh --source-only`
(`/tmp/factoidal-web-context-source.log`), and the latest guards pass separately
in `/tmp/factoidal-web-context-guards.log`.

External HTML stylesheets are refused until supplied resource transport exists.
HTML base href is refused for SVG documents until explicit document/base URL
transport exists. SVG style sheets affecting HTML elements or HTML-owned outer
SVG computed properties are refused rather than silently omitting their cascade.
SVG paint rules within the admitted SVG profile still use its global context.

These are source/CPU regression results. A newly linked native/WASM candidate
and original-source browser image comparison are required before recording a
new WPT pass. This work is tracked in
[issue 1230](https://github.com/danbri/factoidal/issues/1230).

The subsequent sizing checkpoint also fixes the generic missing-dimension
calculation exposed by original `svg/coordinate-systems/viewBox-fractional-valid.html`:
height 200 and viewBox 100.5 by 100 now produce width 201, in both block and
inline flow. SVG presentation width/height enter the cascade before author CSS;
auto dimensions derive from a positive viewBox ratio. Ratio-only SVG uses the
definite containing width. Without a usable ratio the existing 300 by 150
fallback remains. This follows [SVG intrinsic sizing](https://www.w3.org/TR/SVG/coords.html#IntrinsicSizing)
and [CSS replaced-element sizing](https://www.w3.org/TR/CSS22/visudet.html#inline-replaced-width).

Thirteen independent sizing guards cover fractional ratios, px/percentage
widths, CSS overrides including auto, missing dimensions and invalid/zero ratio
fallbacks. The original fractional-ratio guard caught premature Float division;
the implementation retains numerator/denominator until the final calculation.
Fresh whole closure source checks pass in
`/tmp/factoidal-web-context-size-source.log`. Fractional final viewport sizes,
percentage height without a definite container, unsupported CSS units and
unsupported numeric syntax remain explicit profile errors. These guards do not
prove general CSS layout or browser raster equivalence.
