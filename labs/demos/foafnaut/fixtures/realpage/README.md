# Real-page causes: original fixtures

Each page shows one group of the causes that made live pages look wrong (record
`docs/designissues/2026-11-14-real-pages.md`). The pages are original; none is copied from
a site. A line is green when the engine does what the line names and red when it does
not, so a capture of a page reads as a list of what works.

| Page | Cause group |
|---|---|
| `selectors.html` | selectors of the cascade: combinators, attributes, structural and functional pseudo-classes |
| `values.html` | values: `rem`, `em`, `pt`, `var()`, `calc()`, colour forms, CSS-wide keywords |
| `atrules.html` + `imported.css` | `@supports`, `@layer`, `@media` in `@media`, `@import`, a fallback declaration |
| `flex.html` | a header bar, a row of cards, a column with `gap` |
| `grid.html` | a page frame with `grid-template-columns`, `fr`, `gap`, `grid-area` |
| `position-float.html` | `position`, offsets, `float` with text beside it, `box-sizing` |
| `images.html` + `logo.svg` | an SVG file as `img` (own size, sized by attributes, by a style, in a `data:` URL), inline SVG with metadata attributes, an inline SVG root sized in `em` |
| `scripted.html` + `scripted-*.css` | elements made or changed by scripts: a removed link, an appended link, a link whose `rel` a script set, an `img` a script made |
| `hidden.html` | what is not rendered: the `hidden` attribute (and an author `display` over it), `noscript`, a closed `details`, `hidden` set and removed by a script |
| `text.html` | `font-weight`, `font-style`, list markers, `white-space`, `text-transform` |

Captures: `run_html.ts --html PAGE --shot OUT.png --offscreen --offscreen-size 1280x1600@1
--text-size 100`.
