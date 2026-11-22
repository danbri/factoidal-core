# Visible CSS control characters

The same-pin CSS comparison from core `e0666850902b` to `b9f6c92bd022` lost 90 reftests. Sixty are `css/css-text/white-space/control-chars-*` mismatch cases. Each became pixel-identical to its reference, so the expected visual distinction is absent. The comparison alone does not establish why the old reference pair differed.

CSS Text 3 §4 calls for a visible glyph when control text other than tab or segment breaks reaches rendering. Use one printable presentation character per control code so the glyph stream can represent it without moving DOM offsets. C0 and DEL use Unicode Control Pictures. C1 uses the replacement symbol. This pass keeps the existing tab and segment handling and does not change source or DOM text.

Verify representative C0, DEL and C1 mismatch tests using the same renderer as the full CSS reftests. Include adjacent white-space testharness coverage.

- [CSS Text 3](https://www.w3.org/TR/css-text-3/#white-space-processing)
- [Same-pin CSS comparison](https://github.com/danbri/factoidal-builds/actions/runs/45053563282)
