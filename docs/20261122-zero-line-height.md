# Zero CSS line height

Extract the line-height work from the image sizing draft (#680). The style
reader accepts zero lengths, percentages and unitless factors. Negative
values remain invalid. The exact `0px` declaration is proved through the
existing cascade path and preserves every field except the line-height
fields. The other values are checked by executable cascade guards.

The latest valid full CSS pixel baseline has failures in each of the ten
CSS2 line-height unit fixtures with zero height at WPT
`4b26db8978f6024d3184ca483d74afbc354b35de`. The paired comparison selects the
whole CSS2 line-height group on the same native renderer and WPT revision.

The proof reduction steps were compiled in a local Lean probe. Native CI will
check the theorem on the actual Style module and print its axioms. The pixel
comparison tests line placement independently of that theorem.
