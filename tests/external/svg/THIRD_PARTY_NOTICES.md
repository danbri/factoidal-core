# WPT SVG fixtures

The files under `upstream/` are unchanged files from
https://github.com/web-platform-tests/wpt at commit
`70dae60789ef6220d9b4e60c92c5b2107b4e2b93` (2026-10-30).
Copyright © web-platform-tests contributors. The upstream 3-Clause BSD
license is retained in [upstream/LICENSE.md](upstream/LICENSE.md).
Author notices in individual files are retained.

`source.json` records the upstream directory listings and Git blob IDs.
`manifest.json` records each vendored file's SHA-256 and byte count.
The two SVG reftest directories and their support/reference subdirectories
are retained in their original layout. Two reference drawings come from
adjacent WPT SVG categories to preserve the original `rel=match` targets.
The upstream SVG test guidance is retained in
[upstream/svg/README.md](upstream/svg/README.md).

Fonts and browser script dependencies outside these directories are not
vendored. Tests that need them remain in the inventory and results. The
runner cannot mark such a case as a rendering match. In particular, the
FreeSans URL in some fixtures is retained as text; no font with a different
license is imported. No W3C SVG 1.1 PNGs or third-party repackaged suites
are included.
