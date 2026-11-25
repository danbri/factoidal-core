# 2026-11-25 Start web fonts during the initial asset wait

The host can start discovery and fetch for web fonts once it has the linked and
imported stylesheets. It now starts that work before waiting for initial page
images and the tab icon. The same ordered list of fonts is ready before a
script can read layout or the first frame is made.

An alternating Linux native browser run produced identical screenshots and
the same ordered digests for 20 BBC News fonts and two GOV.UK fonts. BBC's
fonts were ready at 11.52/10.69 seconds from document start before the change
and 7.28/7.68 seconds with overlap. Live transfer times varied across processes.
GOV.UK's font readiness went from 1.16/1.10 seconds to 0.90/0.91 seconds.

[Matched browser run](https://github.com/danbri/factoidal-builds/actions/runs/45538776030)
