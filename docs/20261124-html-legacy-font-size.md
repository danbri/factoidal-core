# Apply the legacy HTML font size presentational hint

The matched FrogFind desktop replay showed a noticeably smaller heading than Chrome. The heading contains a font element with size 7, which had no effect in the layout cascade. Map the legacy size to the standard CSS font-size keyword as a presentational hint below author rules. The parser handles leading ASCII whitespace, signed sizes relative to three, decimal prefixes and the size range from one to seven. Large values saturate in the digit loop; the Lean equivalence covers that saturation.

The cascade guards cover inheritance, a relative size, malformed spacing and an author override. These checks are separate from a browser replay. FrogFind's nested legacy color hint is a separate rendering difference.

[HTML legacy font size parsing](https://html.spec.whatwg.org/multipage/rendering.html#rules-for-parsing-a-legacy-font-size) · [Desktop page acceptance](https://github.com/danbri/factoidal-core/issues/712)
