# Real pages: why eight live pages looked wrong, and what changes

Record of 2026-11-14. Measured with the macOS engines of release 25c3a4510 and of main
19fb349c1, through the browser host's own page path (`prepareHTML`, then a compile), at a
window of 1280 by 1600 CSS pixels and text size 100%. The pages were fetched live into
scratch and are not committed. Pages: Hacker News, gov.uk, w3.org, a Wikipedia article, BBC
News, a developer.mozilla.org reference page, lean-lang.org, schema.org.

## The finding

On a full run of the Web Platform Tests the engine passes 83% of Chrome's subtests, and of
the eight pages only Hacker News looked close to right. The two facts do not conflict: the
tests and the pages go through different code.

| What most CSS tests exercise | What draws a page |
|---|---|
| `DOM/Selectors.lean`: Selectors 4, for `querySelector` and the CSSOM | `Rendering/Style.lean`: type, id, class, five pseudo-classes, the descendant combinator. A rule with any other selector was dropped |
| `Rendering/CssValues/*`: the property table, for `getComputedStyle`, `element.style`, `CSS.supports` | `Style.apply`: 40 properties; lengths in `px`, `%`, `vw`, `vh`; hex and `rgb()` colours |
| | `Style.Display`: none, block, inline, inline-block and the table values. `Layout.lean`: no floats, positioning, flex or grid |

The style sheets did reach the engine. The renderer read little of them.

## Causes, by pages affected

Counted over each page's own sheets (linked and inline), whole text, by a scratch tool that
follows the reader of main 19fb349c1.

| Cause | Pages | Size |
|---|---|---|
| Selector not read, so the rule is dropped | 7 | of style rules: MDN 69%, w3.org 44%, Wikipedia 37%, gov.uk 35%, BBC 35%, lean-lang 30%, Hacker News 24% |
| Value not read (`var()`, `em`, `rem`, `pt`, `calc()`, `rgba()`), so the declaration is dropped | 8 | `var()`: gov.uk 550, Wikipedia 388; `em`/`rem`: gov.uk 347, Wikipedia 187; Hacker News sets its font sizes in `pt` |
| Property with no field in the layout profile | 8 | most used: `position` and offsets, `font-weight`, custom properties, `content`, the flex properties, `box-sizing`, `border-radius`, side borders, `float`, `white-space`, `list-style`, background images, logical properties |
| Layout mode missing (flex, grid, positioning, floats) | 7 | `display:flex`: gov.uk 55 rules, w3.org 32, Wikipedia 30; `position`: gov.uk 187, BBC 127 |
| Only the first 131,072 characters of all sheets joined were read | 3 | read: gov.uk 32%, Wikipedia 55%, BBC 60% |
| `@supports`, `@layer`, `@media` in an at-rule skipped | 5 | `@supports`: MDN 119 rules, Wikipedia 78, gov.uk 66 |
| Host limit of 16 linked sheets | 2 | MDN links 18, lean-lang.org 31 |
| A `media` attribute the reader refuses skips the sheet | 1 | w3.org's layout sheet (`pointer`, `hover` in a list) |
| Text drawn at 200% of its CSS size, boxes at 100% (the default text size of a new window) | 8 | a comparison with another browser needs text size 100% |

Images:

| Cause | Pages |
|---|---|
| The host fetches images of the page's own origin only | Wikipedia 22 of 28, BBC 64 of 64 |
| An SVG file as `img` was not read (PNG, JPEG, GIF only) | Hacker News' logo, w3.org 6 of 9, lean-lang.org 11 of 19 |
| One budget of 1,048,576 decoded pixels a document; an image past it showed its alt text | lean-lang.org (3.1 million pixels), w3.org |
| Inline `svg` refused for a metadata attribute (`focusable`, `class`, `data-name`) | gov.uk 13, MDN 2, lean-lang.org 12, BBC |
| Inline `svg` with a percentage height | BBC 179 |
| CSS images (`background-image`, `mask-image`) | Wikipedia, MDN, gov.uk |

The "Partial page" note is drawn when a page has any liberal-mode diagnostic. On main it
comes from inline SVG refusals (gov.uk, BBC, MDN, lean-lang.org), sheets past the host's
limit (MDN, lean-lang.org) and w3.org's `media` attribute. Module scripts no longer cause
it.

## Who changes what

The cascade causes (selectors, values, whole sheets, conditional at-rules, custom
properties) are the work of the CSS values branch, which reads rules through
`DOM.Selectors` and values through the property table. Flex and grid are the layout
branches. This record's changes are the page pipeline around them.

### Inline SVG: metadata attributes

`NativeSVG.inertAttribute`: `focusable`, `class`, `role`, `tabindex`, `lang`, `aria-*` and
`data-*` say nothing about what is drawn, and the reader reads past them. Before, each
refused its whole `svg`. An embedded root sized in `em` or `rem` takes the box that the
HTML layout computed, as a root sized in `vw` does.

### Linked sheets

The host fetches up to 64 linked sheets a page (16 before). The engine bounds the bytes of
all sheets.

### Images held reduced

A document's images share one budget of pixels, the paint table of a scene. When the
images have more pixels than the budget, each image above 4,096 pixels is held reduced by
one whole factor for the document (`NativeImage.factorFor`): a pixel of the held bitmap is
the mean of a block (`reduce`). Layout takes the image's own size
(`Store.natural`, `Layout.Picture.natural`), so the page is laid out as with the whole
image and the picture is drawn softer. A document whose images fit the budget is not
changed. The sizes come from the files' headers (`naturalSize`), so the factor is known
before any image is decoded.

### SVG files as images

`WebRender.vectorPicture` reads an SVG document with the forgiving reader, with nothing
from outside the document, and draws it on the CPU (`SVGRaster`) into a bitmap: twice the
image's size on each side while that is within 262,144 pixels
(`NativeSVGForgiving.imageRaster`). The scene shader draws on an opaque ground, so the
document is drawn on white and on black, and each pixel's alpha is one minus the
difference (`alphaFrom`). The size of the image is that of its root (`imageSize`). The
picture then goes the way of any image.

### Captures

`run_html.ts --offscreen-size WIDTHxHEIGHT[@SCALE] --text-size PERCENT` takes a capture at
the window and text size other browsers use. The default text size of a new window is not
changed.

## Proved, tested, open

Proved (Lean theorems; no `sorry`, no axiom beyond the three of core):

- `NativeImage.factorFor_bounds`: the factor is from 1 to 16.
- `NativeImage.factorFor_fits_one`: images that fit the budget are held as they are.
- `NativeImage.factorFor_fits`: when a factor up to 16 fits, the images held at the chosen
  factor fit the budget.
- `NativeImage.reduce_one`, `reducedSize_one`: factor 1 changes no bitmap.
- `NativeImage.decodeWith_none`: with no vector reader the store decodes as before.
- `Layout.Picture.size_whole`: a picture not held reduced has the size of its bitmap.
- `NativeSVGForgiving.imageRaster_fits`: the picture of an SVG image has at most 262,144
  pixels.

Tested only (`#guard`):

- the size read from a PNG, GIF and JPEG header equals the size the decoder gives;
- `reduce` gives the mean of each block and a bitmap of `reducedSize`;
- a picture held reduced is painted in the same rectangle, with a map that reaches fewer
  pixels (`ReplacedTests`);
- an SVG file as `img` is drawn as an image with alpha, with the size of its root;
- inline SVG with metadata attributes is read in strict and liberal mode.

Open:

- Images of another origin. The host's subresource fetches (sheets, images, fonts,
  scripts) are plain fetches that follow redirects and have no address check, so the
  same-origin rule for images stands until image requests go through `Net/PageFetch` as a
  no-cors transfer.
- `srcset` and `picture`: only `img[src]` is requested.
- An animated GIF shows its first frame: the decoder gives the frames and delays, nothing
  plays them.
- `@import` sheets are not fetched.
- Inline `svg` with a percentage height (CSS 2.1 §10.5: `auto` when the containing height
  is not definite) is still taken out; BBC's icons need it.
- CSS images (`background-image`, `mask-image`, `content: url()`).
- The alpha of an SVG picture is not proved to be the alpha a compositor would give; the
  rounding of two 8-bit pictures bounds its error to about one part in 255.
- The pixel budget is one for a document. A page of many photographs is drawn soft. The
  way out is image tiles kept on the GPU, not a larger table.

## Timings

First layout and compile of the page (no scripts), M1, window 1600 by 1000 device pixels,
engine 25c3a4510:

| Page | ms | primitives |
|---|---|---|
| Hacker News | 137–151 | 2,339 |
| gov.uk | 199–228 | 1,717 |
| w3.org | 1,129–1,139 | 1,100 |
| Wikipedia | 780–914 | 731 |
| BBC News | 443 | 1,007 |
| MDN | 717 | 2,767 |
| lean-lang.org | 1,579 | 301 |
| schema.org | 59–87 | 1,167 |

The numbers after the changes are added when an engine with them has drawn the pages.
