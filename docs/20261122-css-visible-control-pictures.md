# Visible CSS control characters

The same-pin CSS comparison from core `e0666850902b` to `b9f6c92bd022` lost 90 reftests. Sixty are `css/css-text/white-space/control-chars-*` mismatch cases. Each became pixel-identical to its reference, so the expected visual distinction is absent. The comparison alone does not establish why the old reference pair differed.

CSS Text 3 §4 calls for a visible glyph when control text other than tab or segment breaks reaches rendering. Use one printable presentation character per control code so the glyph stream can represent it without moving DOM offsets. Use the Unicode replacement glyph for C0, DEL, and C1. This pass keeps the existing tab and segment handling and does not change source or DOM text.

The first paired run recovered 32 of 60 cases with the replacement glyph for C1. Control Pictures did not produce visible pixels for the 28 C0 and DEL cases. The next candidate uses the replacement glyph throughout and reruns all 60 cases. The first candidate and baseline each passed 341 of 431 adjacent white-space and line-breaking testharness subtests.

- [CSS Text 3](https://www.w3.org/TR/css-text-3/#white-space-processing)
- [Same-pin CSS comparison](https://github.com/danbri/factoidal-builds/actions/runs/45053563282)
