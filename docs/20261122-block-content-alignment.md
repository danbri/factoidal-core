# Block content alignment

Horizontal block layout now aligns its contents as a unit using the existing CSS alignment values. Non-normal alignment establishes a formatting context, so child margins do not collapse through its edges and neighboring floats stay outside it. Alignment also applies to inline blocks, table captions and table cells. The container's own edges and explicit absolute insets retain their geometry.

Lean 4.33.1 compiled the alignment module with warnings as errors against the locally compiled CSS property modules. Its guards cover center, safe overflow, default scrolling overflow, explicit unsafe overflow and safe distribution fallback. Full native and pinned WPT checks are separate.

[CSS Box Alignment Level 3 §5.1.1](https://drafts.csswg.org/css-align-3/#align-block)
