# Transfer height into automatic block width

An ordinary horizontal block with an automatic width and a preferred aspect ratio can derive its width from a definite height. With automatic height, definite vertical limits transfer as width bounds. Explicit horizontal limits still apply. Border-box ratios use the full border box, including edges that consume the declared height. The `auto <ratio>` fallback on an ordinary element uses content-box dimensions.

A width derived from a definite height uses its min-content automatic minimum when overflow is visible or clipped without forming a scroll container. The explicit maximum can cap that minimum. Repaint reuse tracks the distinction between `overflow: clip` and `hidden` because a style change between them can alter layout.

The implementation covers normal horizontal block flow and definite vertical lengths, including percentages resolved by the existing block layout. Replaced sizing and parent-imposed dimensions continue through their existing paths. Chrome verified fixed and capped card dimensions, border-box edge floors, explicit width bounds, and the overflow distinction. Lean 4.33.1 evaluated 13 guards on the exact transfer helper with the engine's `AspectRatio` and `LayoutUnit` modules. The position-layout module adds normal entry-point geometry regressions whose complete build and WPT runs are recorded in the pull request.

[CSS Sizing 4](https://drafts.csswg.org/css-sizing-4/#aspect-ratio) · [Issue #1096](https://github.com/danbri/factoidal-core/issues/1096)
