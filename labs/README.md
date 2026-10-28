# labs

Experiments that are not part of the engine or the package. A lab may be
removed or changed at any time. Nothing in `npm/`, `formal/` or `docs/web/`
imports a file from here.

| path | what it is |
| --- | --- |
| [`filetrees/`](filetrees/) | file trees to serve over WebDAV to desktop file browsers (Finder, Windows Explorer, GNOME Files, KDE Dolphin), to find what each client shows and does |

The harness that serves the trees and records what each client does is
[`tests/webdav-desktop/`](../tests/webdav-desktop/). Tracking:
https://github.com/danbri/factoidal/issues/1079 (checks with the real file
browsers).

Rules for a lab:

1. A lab holds fixtures, generators and notes. It makes no protocol, RDF or
   SPARQL decision (iron rule 7 of `CLAUDE.md`). When an experiment shows that
   the server must behave differently (for example a read-only view tree, or
   a folder whose files are SPARQL results), the change goes into Lean
   (`formal/lean4/L4Factoidal/WebDAV/`) and the lab only exercises it.
2. Text fixtures are committed. Binary, large or platform-hostile fixtures
   (images, PDFs, 60 MiB files, names that Windows or git refuse) are made by
   a generator at run time, so the repository stays text and every checkout
   can hold it.
3. A lab result that changes a decision is written into
   `docs/designissues/` and linked from `docs/worknotes-index.md`.
