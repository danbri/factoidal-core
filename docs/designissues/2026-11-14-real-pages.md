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

## Later the same day: what the first engines with these changes showed

The first macOS engine with flex, positioning and the changes above drew the eight pages
(captures of each round: the scratch directory named in the night notes; not committed).
Four more causes came out of those captures and of original fixtures
(`labs/demos/foafnaut/fixtures/realpage/`), and one cost.

### A script that removes a linked sheet

`WebDocument.validateResources` refused a request when a supplied resource's node was no
longer a connected style sheet link. The host fetches sheets for the tree as parsed; when a
script then removed the link, or changed its `rel`, every render was refused and the page
was not drawn. Such a resource is now left out when the request carries script commands
(`staleResourceLeftOut`; with no commands the refusal stands).

### Elements made by scripts

The host asked the engine once, before scripts ran, which sheets and images the page wants.
A link a script appended, a link whose `rel` a script set to `stylesheet` (the preload
pattern) and an `img` a script made were never fetched. The window now asks again with the
scripts' commands after a turn that changed the tree and fetches what is newly listed
(`page-load.mjs newlyListed`): one check at a time, and the wait between checks doubles to
4 s while they find nothing.

### Subresources of another origin

The engine side is `Net/Subresource.lean` and the document op `subresource` (the
networking record). The hosts' side is `page-load.mjs loadSubresource`: the loop over the
op's steps, used by the window for images (six at a time), the tab icon, web fonts and
linked sheets. An engine without the op keeps the page's own origin. The Hub reads its own
site only, by design, and is unchanged.

### The cost of images, and the store made ahead

A page's scripts start before its first frame. Each layout that a script's read asked for
made the image store again (no layout had kept one yet): every image decoded per layout.
With SVG image files drawn on the CPU and large images reduced, the first script turn of
lean-lang.org went from 8 s to 152 s for the same 163,000 instructions. The store is now
made once at `scriptSession start` (`WebRender.storeAhead`, `WebDocument.keepStoreAhead`)
and found by every layout after it.

What remains is the first decode itself, which is slow for what it does (M1, one page each,
other work running on the machine):

| Image | First layout with it |
|---|---|
| JPEG 786 by 486 | 1.7 s |
| SVG illustration, 500 by 285, 81 paths, drawn at 500 by 285 | 5.7 s |
| SVG logo | 1.6 s |
| JPEG 1920 by 1280 | not decoded: past the 1,048,576 pixels of one image |

The picture of an SVG image is therefore drawn with at most 65,536 pixels (it was
262,144): icons and logos up to 128 by 128 CSS pixels are still drawn at twice their size,
a larger drawing is held smaller than it is shown.

### Bold and italic

`Rendering/FontSynthesis.lean`: `font-weight` and `font-style` values, and the faces the
engine makes from its one regular face: bold is the outline filled and stroked (the stroke
1/24 to 1/32 of the font size), oblique a shear of 1/4 about the baseline. The cascade
fields and the paint are a separate change on top of the cascade work.

### What is not rendered

Three things were laid out that a browser does not render: the content of `noscript`
(scripts run here; lean-lang.org began with its noscript notice), an element with the
`hidden` attribute (gov.uk's cookie notice showed the paragraphs of both of its answers,
and any panel a page keeps hidden was drawn open), and the content of a `details` that is
not open. They are part of the start style of an element in `CSS.computedFrom`, so an
author rule for `display` wins, as over a user agent rule. `details`, `summary`, `hgroup`
and `search` start as blocks.

The search for a `details` element's `summary` reads at most 64 children
(`CSS.firstSummary`): the first version looked through all children once for each
`summary` child, a quadratic cost of a page's choosing.

### Bounds (work driven by a page)

| Work | Bound | State |
|---|---|---|
| picture of an SVG image | 65,536 pixels (`imageRaster_fits`, for sizes up to 4,096 a side, which `imageSize` gives); the document read is at most 1,048,576 characters; 64 repairs | proved for the pixels; the time for a pixel grows with the drawing's paths and is measured, not bounded |
| images of a document | 64 images, 1,048,576 decoded pixels in all (`factorFor_bounds`, `factorFor_fits`), each image at most 1,048,576 pixels before it is decoded | proved |
| summary of a `details` | 64 children read (`firstSummary_work`) | proved |
| replay of script commands in a render | 65,536 commands (`Hosts.Dom.maxCommands`), refused past it | tested by a guard; the cost is linear: 3.7 s a layout at 26,319 commands |
| a subresource transfer in a host | 64 steps (`loadSubresource`), 20 redirects in the engine | host code, tested |
| sheets and images asked for again after script turns | one check at a time, the wait doubling to 4 s; 64 sheets, 64 images | host code, tested |
| `font-weight` number | 4 digits read | by construction (`digits?`) |

### Proved, tested, open (this part)

Proved: `closedDetailsContent_root`, `closedDetailsContent_open`, `closedDetailsContent_other`,
`firstSummary_work`; `staleResourceLeftOut_no_commands`; `WebRender.storeAhead_made` (the store made
ahead is `pageStore` of the document's own keys and the images given);
`WebDocument.keepStoreAhead_rest` (nothing else the engine keeps changes);
`FontSynthesis`: `bolder_bounds`, `lighter_bounds`, `bolder_isBold`, `relative_examples`,
`weight?_bounds`, `embolden_le`, `shear_baseline`, `shear_height`, `shear_leans`.

Tested only: the `hidden` attribute and `noscript` in the start style (guards and the
fixture `hidden.html`); that a layout finds the store made ahead (`==` on byte arrays has no
lawfulness instance, so the lookup is not proved to hit); the host loops
(`host_parity_test.ts`: a stand-in for the op, `newlyListed`); the fixtures by capture.

Open:

- SVG images should be drawn as vectors with the page (the scene of the document placed
  in the image's box, as inline `svg` is), not as a CPU picture: no decode time, sharp at
  every size. Until then large SVG drawings are soft and cost seconds.
- Images decode in the first layout, before the first frame. They should arrive after it,
  one at a time; the store is keyed by all keys and all bytes together, so adding one
  image decodes all again. A store per image is the way.
- A JPEG or PNG of more than 1,048,576 pixels is not decoded (decode at a reduced scale).
- WebP (every photograph of BBC News) and AVIF have no decoder.
- A page whose scripts pass 4,096 commands (lean-lang.org: 26,319) is now drawn whole,
  and each render replays the commands: 3.7 s a layout there. The render should read the
  session's arena.
- BBC News: 85 to 100 s before its first frame, spent between the host and the network
  inside the script session's start (41 module scripts), not in the engine.
- The session's layout request is fixed at start: sheets and images fetched later for
  script-made elements reach the renders, not the scripts' layout reads.
- `srcset` and `picture` for the image list (the selection is in `HTML/ImageSource.lean`).

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

## The afternoon: what the pages still lacked, and the time to a first frame

### Animated values on screen

The cascade that scripts read has the values of running animations and transitions; the
frame a host painted did not: `opacity: 0; animation: fade-in .3s forwards` stayed
invisible. Three pieces were missing. A render's layout request is filtered by
`WebDocument.layoutFields`, and `animated` was not in the list, so the field never reached
`elementState` in a render. No host carried the list: `page-load.mjs takeAnimated(page, turn)`
keeps a turn's `animated` on the host's record of the page, `pageLayoutFields` gives it to
every request, and the window, Textnaut and the Hub draw again when it changed. And no
turn answered it: `WebScripts.animatedOf` gives the animated values of the session's last
layout when that layout is of the page as it is now and of the timeline's time now, and
nothing when the layout is older (a host keeps the list it has; an old value is never
given as the present one). A render replays the session's commands over the parsed page
and keeps the arena's node numbers, so the session's numbers are the render's.

Open: a page whose scripts read no layout in a turn gets no new values, and a page with
no script has no session at all. Both need the style change made at each frame.

### `@import`

No `@import` was followed: the sheet reader left the rule out and no host fetched its
sheet. `Rendering/ImportTree.lean` walks the imports of a sheet depth first from the
sheets a host has given: an import whose sheet is given is read in place of its rule,
under the rule's layer, `supports()` condition and media query list (`wrapImport`), its
own imports first; one that is not given is listed for the host (`inspect` answers
`imports`). The host fetches what is listed and asks again (`page-load.mjs loadImports`),
and the request field `imported` carries the sheets to every layout. A sheet imported
twice applies once, at its first place.

### Sheets and images that arrive after the scripts started

The script session's layout request was fixed at its start. A session action may now
carry `layout` (`WebScripts.takeLayout`): the session's layout reads use it from then on,
and what it kept of the old layout is dropped. The window sends it when a sheet, an
imported sheet or an image arrived after the start.

### `srcset` and `picture`

An `img` was its `src`. The source is now chosen by `HTML.ImageSource` in one nominal
environment (1280 by 800, one device pixel a CSS pixel), so that the list a host fetches
and every layout name the same image; candidates in a format the engine does not decode
(WebP, AVIF) are passed over, and the `src` stands when nothing else is left. BBC News
then asks for its JPEG candidates instead of WebP.

### The time to a first frame in the window

Measured on a quiet M1 with the macOS engine of main ca652ad26, the window off screen at
1280 by 1600 and text size 100%, in ms from the start of the process to the first frame
presented; the engine is the same in both columns, only the host differs:

| Page | host of main | host with the changes below | the same, with the images after the first frame |
|---|---|---|---|
| Hacker News | 5,931 to 7,559 | 3,454 to 5,383 | 4,232 to 5,246 |
| gov.uk | 15,581 to 15,990 | 5,680 to 5,786 | 5,897 to 6,159 |
| w3.org | 15,352 to 15,779 | 11,658 to 12,134 | 3,763 to 4,071 |
| Wikipedia | 17,455 to 18,258 | 11,047 to 17,737 | 11,101 to 11,956 |
| schema.org | 5,029 | 1,696 | |
| MDN (grid) | 52,842 | 38,787 | |
| lean-lang.org | none in 200 s | none in 200 s | |
| BBC News | none in 200 s | none in 200 s | |

The first four rows are two runs of each host on each page, the hosts one after another on
the same page while other work ran on the machine (the times are longer than on a quiet
machine and comparable within a row); the last four are single runs on a quiet machine.
The third column is a host that gives the engine every page's images after the first
frame: it is not what is merged (see below), and shows what the images cost before a first
frame: 8 s on w3.org, whose nine images are three photographs and six SVG files drawn on
the CPU.

What the host did that it need not have done:

- It read the QuickJS guest (1.25 MB) and gave it to the engine, which decodes and
  validates it, at every start: 0.55 to 1.3 s before the first fetch. The guest is now
  loaded when a page first runs on it.
- Its first compile of a page, made before the window's size is known and never shown,
  asked for the CPU probe, which draws the page's inline SVG on the CPU: 8.5 s on gov.uk.
  It asks for none now.
- It waited for every image's bytes, and the engine decoded each, before the first
  frame. For a page that runs no script the window now reads the bytes while the page is
  laid out, shows the page with the alternative texts, gives the engine the images once
  a frame is on screen, and draws again (`setImagesAfterFirstFrame`, `startImages`, the
  page's `revision`). A page whose scripts run still starts them with its images: the
  scripts' layout reads and the load event are of the page with its images, in every host
  alike (the host parity check holds the window to that). Runs that compare frames or
  replay input wait for the images as before. The way to take the images out of the
  path of a page with scripts is a store that knows each image's size without its pixels:
  the scripts' layout and the first frame need the sizes, and only painting needs the
  pixels (open, below).
- It fetched linked sheets and scripts one after another: 3.1 s for the 31 sheets of
  lean-lang.org, 0.57 s six at a time (`inOrder`, the document's order kept).
- The `fontFaces` question computed the style of every element to find the faces the
  text uses, also when the page's rules name every face and the answer does not depend
  on it: 0.46 s on gov.uk, 1.6 s on lean-lang.org (`WebDocument.facesFetched`).
- After the page was inspected its images, its icon and its scripts waited for its sheets,
  one group after the other; they are asked for at once now (Hacker News: 3.4 s to 1.9 s
  before its scripts start, of which its own response is 0.8 s).
- The first call of the main-thread engine takes 0.4 to 0.6 s. It was the history entry
  made after the page was ready; it is made while the page is fetched now.

Tried and dropped: warming the worker with an empty page in place of the unshown first
compile of the page. The engine keeps most of a first layout's work for the next one (the
second layout of a page costs a half to a third of its first), so the unshown compile is
not paid twice, and the first frame came no sooner.

What is left, by page: MDN is the scripts' start turn (25 to 37 s for 1.42 million
instructions: every layout read after a write is a cascade of the page) and 4.2 to 4.8 s
a layout; lean-lang.org and BBC News do not end their start turn in 200 s (BBC's 62
module scripts are fetched inside the turn, one host round trip each); Wikipedia is its
layout, 1.7 s.

### The WPT runner held no page font

The engine lays text out with the font a host holds, and draws with a page's web fonts
only inside that font's profile; with none held every page is laid out in the bitmap
face and no web font is used. The hosts hold Noto Sans. The WPT runner held nothing, so
a page's own font (Ahem in most layout tests) was fetched, checked and held, and its text
was still measured in the bitmap face: nine letters of `font: 10px/1 Ahem` were 77.14px
wide, not 90px. The runner now holds the font the hosts hold; the canvas text tests keep
their own font in its place. On ten pages that link `/fonts/ahem.css`: 87 to 174 of 300
subtests.

### Bounds (work driven by a page), this part

| Work | Bound | State |
|---|---|---|
| sheets read for one sheet's imports | 64 (`ImportTree.maxSheets`; `sheetsOf_length`, `lackingOf_length`), 8 deep (`maxDepth`), each URL once | proved for the counts; the depth and the once-only rule by construction, tested |
| imported sheets of a request | 256 sheets, 4 MiB of text (`importedSheets`) | by construction, tested |
| rounds of asking a host for imports | 9 rounds, 64 sheets (`loadImports`) | host code, tested |
| the animated values of a turn | those of the last layout; no cascade, no layout made (`animatedOf`) | proved (`animatedOf_fresh`, `_written`, `_earlier`) |
| the `fontFaces` question | no cascade when every face is named by a rule (`facesFetched_declared`) | proved |
| fetches at once in the loader | 6 (`inOrder`), no work started after a failure | host code, tested |

### Proved, tested, open (this part)

Proved: `ImportTree.sheetsOf_length`, `lackingOf_length`, `walk_no_imports`, `walk_zero`;
`WebDocument.wrapImport_plain`, `animated_imported_layout_fields`, `facesFetched_declared`;
`WebScripts.takeLayout_start`, `takeLayout_absent`, `animatedOf_fresh`, `animatedOf_written`,
`animatedOf_earlier`; `WebRender.imageSource_plain`.

Tested only: the import walk's order, cycles and limits (guards in `ImportTree.lean`); the
host side (`host_parity_test.ts`: `takeAnimated`, `loadImports`, images after the first
frame with a stand-in engine, `inOrder`); the runner's page font (ten WPT pages, and a
cloud check of the layout directories).

Open:

- The style change at each frame for a page whose scripts read no layout, and for a page
  with no script (animations there never show).
- A generic `monospace` face. Code on MDN and lean-lang.org is drawn in the proportional
  face. The initial `font-family` of the engine is `monospace` (from the bitmap face), so
  a held monospace font would draw all unstyled text until the initial value changes.
- SVG images as vectors (see above); the picture drawn on the CPU costs about 19 µs a
  pixel.
- A store per image; JPEG and PNG over 1,048,576 pixels; WebP and AVIF.
- Images after the first frame for pages with scripts. A store of sizes (each image's
  header, an SVG file's root) made at the scripts' start, and the pixels decoded after the
  first frame: nothing moves when they arrive, and the scripts read the same layout as
  now. Or the session starts without the images and fires `load` when the host says they
  are in.
- The engine could use a page's web fonts with no page font held (the runner's case).
