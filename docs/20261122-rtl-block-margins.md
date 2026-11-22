# RTL block margins

The horizontal block layout now uses the containing block's direction to solve
the used left margin of a fixed-width or otherwise over-constrained box. This
places the actual painted child at the appropriate edge before CSSOM computes
scrollable overflow. An imposed width still leaves placement to its formatting
context. Normal auto margins still absorb positive free space.

The pinned scroll extent fixture showed 184px where a horizontal RTL flow root
should report 204px. The child's -100px right margin and 300px width in an 80px
containing block require a left position of -120px. The engine previously used
the authored -100px left margin. The separate vertical writing-mode cases
are outside this horizontal correction.

Four focused Lean arithmetic guards passed against the cached layout interface.
The exact native CSSOM run and pixel check are pending.
[CSS 2.2 block width](https://www.w3.org/TR/CSS22/visudet.html#blockwidth)
