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
