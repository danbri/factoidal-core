# Counters and list markers through boxless wrappers

In the three CSS Lists slot-order reftests, retaining slots for the cascade also retained them as parents for counters and native list markers. Default slots generate no box. The slots must remain in the styled tree so assigned children still inherit from them.

Apply the existing contents flattening to the counter walk only, with parent links adjusted on that temporary projection. Use the same box parent when looking up an ordered list's siblings. The existing computed styles, source node IDs, and original ancestry are retained.

A Chrome 157 control matched the three pinned WPT references exactly. It also rendered two sibling items through ordinary boxless wrappers as 1 and 2, through block wrappers as 1 and 1, and ignored counter resets and increments on boxless wrappers. The Lean guards cover those cases and ordered list marker positions. The exact candidate's pixel checks are pending.

[CSS Lists](https://drafts.csswg.org/css-lists-3/#inheriting-counters) · [CSS Shadow](https://drafts.csswg.org/css-shadow-1/#slots-in-shadow-tree) · [Chrome control](https://github.com/danbri/factoidal-builds/actions/runs/45532447430) · [Regression issue](https://github.com/danbri/factoidal-core/issues/982)
