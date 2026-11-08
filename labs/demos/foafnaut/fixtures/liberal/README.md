# Liberal mode fixtures

Small original pages, written for this repository, that each hold one construct that made
Foafnaut refuse a real page on 8 November 2026 (`docs/designissues/2026-11-08-liberal-mode-and-console.md`).
No text or markup of any real site is copied here. The real sites are probed live only
(`real_sites_probe.ts`).

- `media.html`: stylesheets with media conditions (`min-width`, `max-width`) that Lean now
  evaluates in both modes, and one (`hover: hover`) that it can not read.
- `module.html`: a module script next to a classic script.
- `missing-css.html`: an external stylesheet that is not there.
- `svg.html`: an inline `svg` with a width in `em` and a `focusable` attribute, which the SVG
  reader refuses.
- `sample.html`: all of the above together, for the Hub console check.
