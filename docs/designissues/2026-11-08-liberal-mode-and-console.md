# Liberal mode and the console tab

Owner's request for the next release (8 November 2026): a `--be-liberal-in-what-we-accept`
option on the command line and a checkbox in Settings; the browser console as another tab;
page problems logged by "System" to the console.

## What was wrong

Foafnaut refused a whole page at the first feature it does not support. On 8 November,
with the bleeding-edge app of that evening (`real_sites_probe.ts`; its commit was not recorded, main `0fb2e20b7` or `bfbed32a8`):

| site | strict, before |
|---|---|
| en.wikipedia.org/wiki/FOAF | refused: unsupported stylesheet media condition (`media="(min-width: 500px)"` and others) |
| www.gov.uk | refused: unsupported JavaScript module script |
| www.bbc.co.uk/news | refused: unsupported JavaScript module script |

`--no-scripts` did not help: the module refusal comes from Lean's `inspect`, before any
script is run or not run.

## The design

**Liberal is the default** in the macOS app and on the Hub (owner decision, 2026-11-09: the
browser tries to show content and reports serious issues in the console tab). Strict is the
Settings choice (the checkbox off), `run_html.ts --strict`, and `?strict=1` on the Hub; it is
the behaviour of 8 November, except that the simple media queries below are now read in both
modes. Every test entry point is strict explicitly: `sweeps.sh`, the page GPU runs of
`test.sh` and the start check of `build-executables.sh` pass `--strict`, the Hub checks pass
`strict=1`, and `prepareHTML`, which the engine tests and the WPT runner use, is strict unless
it is given `{liberal:true}`. A saved setting from before the change, with no `liberal` field,
reads as liberal (`WebState.Settings.ofDoc`).

**Liberal mode is decided in Lean** (`labs/demos/foafnaut/WebAccept.lean`). A document request
with `liberal:true` is in liberal mode. Each refusal that can be skipped safely is a *skip
point*, `WebAccept.skip`: in strict mode it is the refusal, as before; in liberal mode it gives
the value a browser without the feature uses and a `Diagnostic` (source "System", severity,
feature, where, action, and the refusal text of strict mode).

The list of what may be skipped is `WebAccept.Skip`, and nothing else:

| skip | action in liberal mode | where |
|---|---|---|
| `mediaCondition`: a `media` attribute on a `link` or `style` that `MediaQuery` can not read | the sheet does not apply (Media Queries 4: an unknown query is false) | `WebDocument.activeSheetIn`, `fetchSheetIn` |
| `moduleScript`: `<script type="module">` | not run, as in a browser without module scripts (a `nomodule` script is classic and runs) | `classicScriptsIn` |
| `scriptsOff`: classic scripts when the host runs none (`--no-scripts`, no QuickJS guest) | not run, as with scripting off | `classicScriptsIn` (the host sends `scripting:false`) |
| `stylesheetMissing`: an external sheet the host did not fetch (HTTP error, network, the 16-sheet or 4 MiB host limit, or a host that fetches no sheets, as the Hub) | the page is drawn without it | `rulesIn`, from `resourceFailures` or a missing resource |
| `stylesheetBytes`: sheets past 2 MiB in all | the later sheets do not apply | `rulesIn` |
| `nestingDepth`: elements nested deeper than layout reads (64 levels) | the content below a depth is not drawn: the first of the DOM depths 48, 40, 32, 24, 16 at which the page lays out | `layOutDOMIn`, `pruneDeep` |
| `svgContent`: an inline `svg` that the SVG reader or layout refuses (gov.uk: the attribute `focusable`; NHS: the attribute `class`; BBC News: percentage heights) | that `svg` is not drawn; the rest of the page is | `layOutDOMIn`: one layout. Before it, an `svg` root with a percentage height is taken out; in it, a refused `svg` draws as nothing; after it, each root is read again at its box size for the diagnostic |

What stays refused in both modes, and why:

* Malformed requests and resources (duplicate resources, a resource that is not a string,
  resource and size limits of a request): a host fault, not a page feature.
* A whole SVG document (an `.svg` page) that the reader refuses: the forgiving reader
  (`SVGForgiving`) already draws what it can there, in both modes.
* `unsupported SVG stylesheet affecting HTML layout or outer SVG computed style`: dropping the
  SVG `style` would draw the SVG in other colours or sizes than its author set, with no
  sign of it in the drawing.
* SVG intrinsic size refusals, a viewport outside 1 to 4096, paint count above 1,048,576, link
  regions past 2,048 bytes, the 1 MiB page limit: past these the drawing would be cut at a
  place the page does not choose, or the engine's bounds are at stake.
* XSLT, script-command and DOM-arena refusals: the document itself would be another one.

A declaration with a value this profile can not read was already dropped in both modes, as
CSS error handling says (`CSS.applyOrKeep`); it is not a refusal and gives no diagnostic.

**The theorem.** `WebAccept.accept m run` runs a pipeline that has skip points. In liberal mode
it first runs the pipeline in strict mode and keeps that result when it is a success; only a
refusal makes it run the pipeline again in liberal mode. `WebAccept.liberal_conservative`:
for every pipeline, if strict mode accepts a document with result `a`, liberal mode gives `a`
and no diagnostics. `WebDocument.layOut_liberal_conservative` and
`inspect_liberal_conservative` instantiate it for the layout of a render and for `inspect`.
`strict_quiet` says that strict mode gives no diagnostics, `strict_refusal` that it refuses
with the message of the strict run, and `liberal_refusal` that liberal mode refuses only what
the liberal run refuses. The theorem holds by the construction of `accept`; the cost is a
second run for a page that strict mode refuses, and none for a page that it accepts.

A liberal run happens only after a refusal, so it always has a skip or a refusal: it puts a
note at the top of the page, "Partial page — see console", a link to `foafnaut:console` that
Lean draws as page content (`WebDocument.partialNote`).

## SVG sizes in em

BBC News's "invalid CSS number" was `<svg width="1em" height="1em">`: the cascade read the SVG
`width` and `height` attributes as px or a plain number only (`CSS.computed`). It now reads
`em` (the font size of the element) and `rem` (16 px) too, in both modes.

## Simple media queries

`formal/lean4/L4Factoidal/Rendering/MediaQuery.lean`, in both modes: media types `all`,
`screen`, `print` (other types match nothing), `only`, `not`, `and`; the features `width`,
`min-width`, `max-width`, `height`, `min-height`, `max-height` (also in the range form
`width >= 600px`), `orientation` and `prefers-color-scheme`; lengths in `px`, `em`, `rem`.
`or`, other features and other units are not read: a `media` attribute with them is a
skip point, and an `@media` block with them does not apply.

The viewport is that of the layout, in CSS pixels: the window width in device pixels over
the text scale (`WebDocument.mediaEnv`; at the default 200% a 1600 px window is 800 CSS px,
as a page zoom of 200% is). Pages are drawn in light colours. `CSS.parseIn` evaluates
`@media` blocks the same way; `CSS.parseFor` (no viewport) keeps the old answer for
features: false. The host fetches every sheet whose `media` it can read and that can hold on
a screen or on paper at some size.

## The console

`foafnaut:console` is a built-in page (`WebRoute.builtinPages`). The hosts keep, for each page,
the lines its scripts wrote and System entries: Lean's diagnostics (from `inspect` and from
every render; each kept once), refusals, and fetches that failed (images, icons, scripts).
The op `consolePage` (`WebConsole.lean`) writes the page as HTML from the entries, and Lean
draws it as any page. Its title counts the entries ("Console (3 System, 0 page)").

* Native: View > Console, Option-Command-J (`native_window.m`, command 40), `:console`, the
  note's link. It opens in a new tab, for the page that was shown.
* Hub: Control-Alt-J (not on a Mac, where the host browser keeps Option-Command-J), `:console`,
  the note's link.
* `foafnaut:console/N` is the console of tab N.

What the console shows of page scripts: both engines run `tools/wasmvm/quickjs/prelude.js` and
write through the one `console_log` host import into the session's `logs`; uncaught errors go
into `errors`. Every turn of a session goes to the page's console. `warn`, `error`, `info` and
`debug` carry their level at the start of the line, between two U+0001 marks, and
`WebConsole.level` reads it (`native_liberal_test.ts` checks both engines). `trace`, `group`,
`dir` and `table` write plain lines. QuickJS-NG shows levels with a guest built from this
prelude.

## Settings and the command line

* Settings: a large checkbox "Be liberal in what we accept" (`foafnaut:liberal/on` and
  `/off`) under "Pages", next to the "Page scripts" choice, in the style of the classic-UI
  checkbox, kept in the browser state
  (`WebState.Settings.liberal`, `foafnaut:liberal` in the settings document). Pages load in
  the new mode from then on.
* `run_html.ts --be-liberal-in-what-we-accept`. The foafnaut launcher passes it after `--`.

## Cost

* A page that strict mode accepts: liberal mode runs the same strict pipeline once; `accept`
  adds one match on its result. Nothing else.
* A page that strict mode refuses: the strict run stops at its first skip point (usually
  before layout: scripts and sheets are checked first), then the liberal run lays the page
  out once. Inline SVG adds one cascade before that layout and one read of each `svg` root
  after it. Too deep nesting tries up to five pruned layouts.
* Media queries are evaluated when the cascade is made, which is part of a layout. A kept
  layout (scroll, repaint, hover painted) evaluates nothing; the layout key already has the
  viewport.
* Diagnostics: Lean keeps them in the kept layout and puts them in a render answer only when
  the request asks (`diagnostics:true`), which a host does for the first frame of a liberal
  page. Hosts store them in a list per page. The console page is written and laid out only
  when it is opened.

## Measured

`real_sites_probe.ts` (the native browser's page path: prepareHTML, the native library, Noto
Sans, a 1600 by 1000 frame at 200%, page scripts off as with `--no-scripts`), live, 9 November.
"Start" is fetches, inspect, layout and the first frame; "frame" a frame of a kept layout;
"relayout" a frame at another width.

| site | before (strict, bleeding-edge app of 8 November, see above) | after, strict | after, liberal |
|---|---|---|---|
| Wikipedia FOAF | refused: media condition | refused: page scripts need a script engine (`--no-scripts`); media queries now read | renders: 1 skip (scripts off); start 11.8 s, frame 111 ms, relayout 4.8 s |
| gov.uk | refused: module script | refused: module script | renders: 3 module scripts, scripts off, 1 inline SVG (`focusable`); start 7.8 s, frame 197 ms, relayout 7.7 s |
| BBC News | refused: module script | refused: module script | renders: 62 module scripts, scripts off, 2 inline SVG skips; start 437 s (three layouts), frame 80 ms, relayout 33.6 s |

Demo pages that strict mode accepts, strict, same machine and conditions, before (a bleeding-edge build of 9 November, 01:13, commit not recorded) and after: start 135/127 ms (index), 167/185 (showcase), 135/135 (tables), 117/119
(print showcase), 182/180 (status); frame 26.9/28.2, 56.4/56.5, 31.9/31.9, 33.0/32.2,
42.4/42.8 ms. The differences are within the run-to-run spread.

The Hub loads only pages of its own site, so the real sites do not open there; the Hub check
(`hub_console_check.mjs`) uses the original fixture `fixtures/liberal/sample.html`.

### The release of 9 November (`2aa065beb`: liberal default, one-layout SVG check, layout speed-ups)

The release library, live, the same probe; times are for page scripts off:

| site | strict | liberal | skips |
|---|---|---|---|
| Wikipedia FOAF | refused: scripts off | start 629 ms, frame 61 ms, relayout 158 ms | scripts off |
| gov.uk | refused: module script | start 422 ms, frame 95 ms, relayout 122 ms | 3 module scripts, scripts off, 1 inline SVG |
| BBC News | refused: module script | start 611 ms, frame 67 ms, relayout 367 ms | 62 module scripts, scripts off, 2 inline SVG |
| w3.org | refused: media condition | start 1,111 ms, frame 88 ms, relayout 84 ms | 1 media condition, scripts off |
| NHS | refused: scripts off | start 216 ms, frame 27 ms, relayout 45 ms | scripts off, 1 inline SVG |

The release app itself, default mode with page scripts on, off screen: each page drew, and the
first frame was presented 3.1 to 4.3 s after process start (Wikipedia 3.9, gov.uk 3.1, BBC
News 4.3, w3.org 3.3, NHS 3.1), which includes engine and font load and the page's scripts.

BBC News on one saved page, bitmap face, page scripts off: 51.4 s before (three layouts, the
merged engine of `0f89690b6`), 0.58 s on this release. Most of that is the layout speed-ups,
so the two changes are not separated: on this release a layout of the same page with its SVG
and module scripts taken out by hand is 0.36 s, so three layouts would be about 1.1 s.

Pages that strict accepts, on this release, in one process: the mode that runs first takes
about twice the start of the second (a cold process), whichever it is. Liberal first: index 96,
showcase 106, tables 62, print showcase 56, status 89 ms. Strict first: 105, 97, 57, 55, 91 ms.
Frame and relayout times are equal within the spread.

What looks wrong on these pages (screen pictures from the CPU raster, page scripts off, no
chrome): the text and links are there, in one column, and much of the design is not:
* Lists keep a `*` marker and navigation stacks vertically (no flex or grid layout).
* A refused `svg` with no size of its own keeps the box it would have had, which fills the
  available width: on NHS the search button is a green block about 800 by 840 px, and on BBC
  News the masthead is an empty red band about 350 px tall. Five of the `svg` elements on NHS
  have no `width` or `height` attribute, so this is the likely cause; it was not traced further.
* Icons and logos that are inline SVG are missing, and BBC News's images are on another origin,
  so they are not fetched.
* Every one of these pages carries the "Partial page" note.

The Hub loads only pages of its own site, so these sites do not open there.

## Interactive console (issue 372, stage 1)

The console accepts one line of JavaScript (2048 characters) on desktop and Hub.
Enter evaluates it in the source page's existing script session; copy, paste,
selection and undo use the address editor. Results and errors appear above older
entries. Evaluation applies DOM changes and runs a microtask checkpoint.
It never evaluates page code in the host JavaScript engine.

The engine's `scriptSession` action `evaluate` takes `session` and `expression`
(at most 64 KiB) and returns a normal turn plus `evaluation: {text, exception}`.
Wrong or stale session IDs are rejected without replacing the live session.
A static page starts a realm on its first console submission. A scripted page
whose scripts did not start is not restarted by console input.

This first console uses indirect eval on BubblePopJS: use `var` for bindings
shared between submissions. Objects have a plain preview, without property
inspection; its preview does not invoke getters or `toString`. QuickJS keeps its
existing completion-string conversion and page-mode exception reporting: a console
exception can dispatch an error event to the page. Multiline paste is rejected explicitly.
Only one script session is held by the engine; older tabs can therefore be stale.
Command recall, live log streaming, CDP, MCP and breakpoints remain on
[issue 372](https://github.com/danbri/factoidal-core/issues/372).

Checks: `console_repl_test.ts`, `--console-sweep`, and `hub_console_check.mjs`
(keyboard input, promise jobs, exceptions, and a DOM change rendered on the source
tab, on BubblePopJS and QuickJS AOT). The console adds no listening port.
