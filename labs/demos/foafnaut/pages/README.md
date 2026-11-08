# foafnaut2525 demo pages

Test pages for the Lean engine, and the start page of `foafnaut`. `manifest.json`
lists each page and what the engine must do with it.

- `tools/build-demo-pages.py` writes the `.html` files from `source/`, the status note
  and `../svg-fixtures`. Do not edit them by hand.
- `tools/check-demo-pages.py WEB_RENDER_NATIVE` renders every page. `test.sh` runs both.
- A `.xml` page is its own source. It names a stylesheet with `<?xml-stylesheet?>`, and
  Lean runs it: `version` 1.x uses `XSLT/`, and 2.0, 3.0 and 4.0 use `XSLT4/`.
- A page marked `refused` is an expected failure with an open issue; the check fails
  when it starts to render.
- The showcase pages (`showcase*.html`, issue 1268) are linked from `showcase.html`, not
  from the start page. A page marked `handwritten` is edited by hand. A page with a
  `generator` comes from `../tools/showcase-pages.py` (needs fontTools; run it again after a
  change). A page marked `appRefused` renders in `check-demo-pages.py` but the window
  refuses it, so the bytes test skips it. `showcase_gaps_test.ts` holds one expected
  failure for each gap these pages show, with its issue.
- `showcase-images.html` (handwritten) shows HTML `img` drawn by Lean. Its pictures,
  `images-landscape.png` and `images-badge.png`, come from `../tools/image-pages.py`
  (Python standard library only); `images-missing.png` does not exist on purpose, so
  the page shows alt text for it.
- `source/foaf-graph.svg` comes from `native-webgpu-ui-darwin-arm64 --demo foafnaut
  --emit-svg`, and `source/solving-showcase.svg` from the macOS package. The interactive
  demos (spring network, vector playground, responsive layout) are Lean UI programs with
  their own event loop; they are not pages yet.

## Combinations

The pages in the "Combinations" group of the index put several parts together, mostly an XML file, an XSLT 3.0
stylesheet that Lean runs, SVG, CSS tables and fonts. Each page says what it shows and what it does not, and
`manifest.json` holds the same as `shows` and `doesNotShow`.

- `foaf-people.xml`, `sparql-results.xml`, `feed.xml`, `sitemap.xml`, `lab-files.xml`, `engine-pipeline.xml` and
  `typography-lab.xml` are XML with a stylesheet of the same name. `print-poster.html` is HTML for the print path.
- The engine does not draw SVG `<text>` yet (https://github.com/danbri/factoidal/issues/1270). So these stylesheets
  label their SVG with the XSLT function `ty:text`, which sets one SVG `<path>` for each character from a table of
  glyph outlines and advance widths, with no kerning and no shaping. `../tools/combination-pages.py` writes that table
  into each stylesheet, between the comments `typeset:begin` and `typeset:end`, from the Noto Sans and Noto Sans
  Armenian files in `third_party/fonts/` (SIL Open Font Licence 1.1). Run it again after a change to the data
  (needs fontTools).
- The data is self-written or comes from this repository: the FOAF people are invented; `sparql-results.xml` is the
  output of `factoidal query` over `foaf-people.xml` (the comment in the file gives the query and the commands);
  `feed.xml` entries are commits on the main branch; `sitemap.xml` dates and `lab-files.xml` counts were read
  with git on 2026-11-08.
- "Needs the next engine": `timers-and-clicks.html` needs page scripts in foafnaut and an event loop;
  `svg-text-labels.html` needs SVG text (an expected refusal until then). Each says so on the page and in `needs`.
