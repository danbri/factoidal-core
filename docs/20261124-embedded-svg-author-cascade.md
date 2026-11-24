# Share the author cascade with embedded SVG paint

The GOV.UK homepage draws its popular-service arrows and circles from inline SVG. Its linked stylesheet sets the circle fill by a descendant selector. The old renderer ignored that stylesheet in SVG paint and drew both the circle and the arrow black. The reduced exact reproduction and the 13 CSS reference cases are in [issue #918](https://github.com/danbri/factoidal-core/issues/918).

Runtime HTML rendering resolves style elements in either namespace with the same stylesheet order, layers, selector matching and custom properties. Its own author winners go into the SVG view of each SVG element. The view retains presentation attributes and positions in the original tree. Normalized styles go through the existing SVG attribute reader, and SVG-local style elements in that view give way to the document cascade. Standalone SVG still owns its stylesheet processing. No page fetch is added.

The Lean statement covers preservation of presentation attributes by this projection. The reference cases cover actual pixels and include author importance, inline importance, specificity, layers, mixed sheets, inheritance, variables and media. Exact builds and frozen GOV.UK replay are pending.
