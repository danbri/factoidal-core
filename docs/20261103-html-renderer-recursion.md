# HTML renderer compiled recursion checks

The full verification of [the HTML renderer](https://github.com/danbri/factoidal-core/pull/308)
at `50f7358029010531e53de0a78948c8d1f9f36bdd` stopped at the
[compiled recursion audit](https://github.com/danbri/factoidal-core/actions/runs/41559153231/job/125665264104).
It identified layout of block children, collection of inline items, lowering
the common scene tree, and extraction of endpoints from a linear contour.

The layout now stores pending inline visits and block parent frames explicitly.
When a block child is reached the parent flushes pending inline content. It
resumes at the next sibling after appending the child's result. The existing
nesting budget is consumed on child visits as before. If an arena has at most
`k` children at any node, at most `(k+1)^d` node occurrences can be visited
from one root at depth budget `d`, including the depth-zero visit. The block
loop allows four actions per occurrence and completes when the root returns.
This is a bound on iterations, not a list of that length.

Scene lowering uses a stack of sibling lists with their transforms, group
paths and clips. The correctness statements compare the output with the
existing declarative lowering, including order. The linear-contour reader
accumulates endpoints in reverse and keeps the original nonlinear error.
No recursion audit rule or allowance, rendering tolerance or scene limit
is changed.

The new layout guards check mixed inline and block flow, visitation order on
failure, and rejection at the depth boundary. The existing layout, font, RDF,
scene and proof guards remain in the build. The integration also preserves
the renderer-specific navigation label and main's published 0.29.0 label.

The submission workspace lacked the pinned Lean toolchain. These source
changes are proposed for CI verification. A successful Lean build, compiled
recursion and compiler-replacement checks, and comparison of fresh renderer
artifacts against the checked examples are required before publication.
Nothing here is a release or a new rendering-conformance measurement.
