# Liberal mode and the console tab

Owner's request for the next release (8 November 2026): a `--be-liberal-in-what-we-accept`
option on the command line and a checkbox in Settings; the browser console as another tab;
page problems logged by "System" to the console.

## What was wrong

Foafnaut refused a whole page at the first feature it does not support. On 8 November,
with the bleeding-edge app (`real_sites_probe.ts`, engine of main `0fb2e20b7`):

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
| `svgContent`: an inline `svg` that the SVG reader refuses (gov.uk: the attribute `focusable`) | that `svg` is not drawn; the rest of the page is | `layOutDOMIn`: the embedding's refusals are marked, and a marked one lays the page out again with each refused `svg` empty |

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

What the console shows of page scripts: both engines write through the one `console_log`
host import into the session's `logs`, and uncaught errors into `errors`; every turn of a
session (start, timers, clicks, pointer) goes to the page's console, for QuickJS-NG and for
BubblePopJS alike. QuickJS-NG's prelude sends `log`, `info`, `debug`, `warn`, `error` and
`trace` as one kind of line ("log"). BubblePopJS has only `console.log` today (98cc094f7):
a page that calls `console.warn` gets a TypeError, which the console shows as an error.
Levels need the guest prelude (`tools/wasmvm/quickjs/prelude.js`) and BubblePopJS's
`console` object to pass one.

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
  out once. A refused inline SVG lays the page out a second time; too deep nesting tries up
  to five pruned layouts.
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

| site | before (strict, engine of main 0fb2e20b7) | after, strict | after, liberal |
|---|---|---|---|
| Wikipedia FOAF | refused: media condition | refused: page scripts need a script engine (`--no-scripts`); media queries now read | renders: 1 skip (scripts off); start 11.8 s, frame 111 ms, relayout 4.8 s |
| gov.uk | refused: module script | refused: module script | renders: 3 module scripts, scripts off, 1 inline SVG (`focusable`); start 7.8 s, frame 197 ms, relayout 7.7 s |
| BBC News | refused: module script | refused: module script | renders: 62 module scripts, scripts off, 2 inline SVG skips (an `em` length in the SVG reader; 170 `svg` with percentage heights); start 437 s, frame 80 ms, relayout 33.6 s |

The BBC News start is three layouts of a 1 MiB page (the layout with the SVG reader's refusal
marked, the one with refused `svg` empty, which then refuses a percentage height, and the one
with no inline `svg`); one layout of it is about 14 s with the bitmap face and more with Noto
Sans. Cutting it to one layout needs a check of SVG sizes before layout: a next step. The 64
failed fetches are its images, which are on another origin (`ichef.bbci.co.uk`).

Demo pages that strict mode accepts, strict, same machine and conditions, before (engine of
main) and after: start 135/127 ms (index), 167/185 (showcase), 135/135 (tables), 117/119
(print showcase), 182/180 (status); frame 26.9/28.2, 56.4/56.5, 31.9/31.9, 33.0/32.2,
42.4/42.8 ms. The differences are within the run-to-run spread.

The Hub loads only pages of its own site, so the real sites do not open there; the Hub check
(`hub_console_check.mjs`) uses the original fixture `fixtures/liberal/sample.html`.

