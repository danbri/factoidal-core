# Positioned text and vertical alignment

CSS 2.2 §10.8.1 applies `vertical-align` to inline-level boxes and table cells. Absolute and fixed boxes are out of flow. Foafnaut was still using a positioned element's own `sub` or `super` to move its glyphs. The cascade now preserves the value but omits its own glyph shift for absolute and fixed boxes. Inline text keeps the existing subscript and superscript behavior.

The two pinned WPT reftests `css/CSS2/linebox/vertical-align-sub-001.xht` and `vertical-align-super-001.xht` overlay equally positioned red and green text. The green text should cover the red text in both cases. Compare the parent and candidate with the same WPT pin and renderer. The source theorem states that positioned elements contribute zero baseline shift in `finishEffects`. It does not prove pixels or spec conformance.

https://www.w3.org/TR/CSS22/visudet.html#propdef-vertical-align  
https://github.com/danbri/factoidal-core/issues/747
