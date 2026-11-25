# Do not reserve an inline row for static-position markers

The W3C homepage replay had two extra 23.4 px rows above its language navigation. The native geometry probe placed the header at y=23.4 and the language bar at y=46.8. They each follow collapsible whitespace and an absolutely positioned accessibility element, in two different containers. The inline builder keeps those elements' static-position markers, but a row of just those markers was receiving the normal line-height strut.

CSS 2.2 §9.4.2 gives such a row zero height. Return only its static-position requests, with no baseline or paint. Rows carrying in-flow items still use the existing baseline and line layout. The Lean theorem states the result for any marker-only row and any enclosing strut.

[W3C geometry probe](https://github.com/danbri/factoidal-builds/actions/runs/45424983155) · [CSS 2.2 inline formatting](https://www.w3.org/TR/CSS22/visuren.html#inline-formatting)
