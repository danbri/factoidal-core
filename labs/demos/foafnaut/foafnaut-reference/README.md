# Original FOAFNaut reference

This directory contains newly written analysis of the archived FOAFNaut,
not a copy of its application, graphics, or third-party scripts.

Source pin: [foaf/foaf 24f1fd07665cbd20af7ebafe044e025bb22a4a65](https://github.com/foaf/foaf/tree/24f1fd07665cbd20af7ebafe044e025bb22a4a65/foafnaut.org/htdocs).
The original index links both Jim's live application and the local 2003
snapshot. The [application SVG](https://github.com/foaf/foaf/blob/24f1fd07665cbd20af7ebafe044e025bb22a4a65/foafnaut.org/htdocs/2003/snap1/foafnaut.svg)
contains the JavaScript inline. No separate JavaScript download is needed.

The [presentation](https://github.com/foaf/foaf/blob/24f1fd07665cbd20af7ebafe044e025bb22a4a65/foafnaut.org/htdocs/MappingDistributedCommunities.html#L41)
credits development to **Jim Ley**, graphics to **Liz Turner**, and the
earlier FOAFcorp application to **Dean Jackson**. The repository README
warns that this is an incomplete historical mirror, not an authoritative
archive. Preserve these attributions in a recreation.

No application-wide or graphics license was found in the repository root,
site directory, application header, or presentation. The embedded SHA-1
implementation has its own Paul Johnston copyright/legal notice around
line 746; that does not establish a license for the application artwork.
The historical author websites were unavailable during this inspection.
Consequently the original SVG, screenshot, and exact path artwork are not
vendored here. A local analysis cache records unchanged files and hashes
under `depmap/cache/foafnaut-original/`, outside this source worktree.

## Visual vocabulary

The blue canvas (`#99CCEE`, line 867) carries small person figures,
not generic circular graph nodes. `Blub`, lines 93–130, builds each figure
from paths: a green torso (`#31A458`), peach arms (`#F69866`), red legs
(`#F70F34`), white head/foot controls, black outlines, and a cream name band
(`#F5F8CA`). The uppercase nickname lies across the torso. The head's plus
expands relationships; the foot's minus removes the node.

Exact upstream anchors: [person construction, line 93](https://github.com/foaf/foaf/blob/24f1fd07665cbd20af7ebafe044e025bb22a4a65/foafnaut.org/htdocs/2003/snap1/foafnaut.svg#L93),
[figure paths and label band, line 124](https://github.com/foaf/foaf/blob/24f1fd07665cbd20af7ebafe044e025bb22a4a65/foafnaut.org/htdocs/2003/snap1/foafnaut.svg#L124),
[relationships, line 133](https://github.com/foaf/foaf/blob/24f1fd07665cbd20af7ebafe044e025bb22a4a65/foafnaut.org/htdocs/2003/snap1/foafnaut.svg#L133),
and [canvas, line 867](https://github.com/foaf/foaf/blob/24f1fd07665cbd20af7ebafe044e025bb22a4a65/foafnaut.org/htdocs/2003/snap1/foafnaut.svg#L867).

`addLine`, lines 133–189, draws known relationships with width-3 pale cyan
(`#CCFFFF`) lines. One-way relationships use a `12 4` dash pattern; reverse
only uses pale yellow (`#FFFFCC`). Mutual knows relationships use solid
cyan. Co-depictions use width-1 white lines and a radius-4.2 teal midpoint
(`#33CC99`) with a white outline. A selected person has a darker blue
circle behind the figure (line 589). Panels use teal frames and cream or
yellow title bars. Branding and search controls are near the upper left.

## Layout and a bounded native starting scene

The original is **radial expansion with easing**, not a force layout.
`addDirs`, lines 631–649, places newly discovered neighbors around the
expanded person, with radius `6*n + 50`, vertical scale 1.2 and a random
angular offset. `moveBlub`, lines 653–671, advances one sixth of the
remaining displacement every 10 ms and snaps within three units.
`moveBlubTo`, lines 272–312, keeps link endpoints and co-depiction midpoint
markers attached during movement and dragging.

Layout anchors: [endpoint updates, line 272](https://github.com/foaf/foaf/blob/24f1fd07665cbd20af7ebafe044e025bb22a4a65/foafnaut.org/htdocs/2003/snap1/foafnaut.svg#L272),
[radial expansion, line 631](https://github.com/foaf/foaf/blob/24f1fd07665cbd20af7ebafe044e025bb22a4a65/foafnaut.org/htdocs/2003/snap1/foafnaut.svg#L631),
and [easing, line 653](https://github.com/foaf/foaf/blob/24f1fd07665cbd20af7ebafe044e025bb22a4a65/foafnaut.org/htdocs/2003/snap1/foafnaut.svg#L653).

A recognizable first scene can use one center person plus three neighbors
on that ellipse, at a fixed angular offset for repeatable tests. Use the
original palette and broad figure vocabulary with newly authored basic
shapes; do not import original path strings or the logo pending license
clarification. Draw relationships behind the figures, include a visible
cream name band and white plus/minus controls, and use fictional labels
A, B, C, D. Show a cyan mutual link, a cyan outgoing dashed link, and a
yellow incoming dashed link. A white co-depiction line/teal midpoint can
connect two neighbors. Draw dash segments explicitly while the restricted
SVG renderer lacks `stroke-dasharray`; label this a native reconstruction,
not successful rendering of the original SVG.

The scene's RDF data should be a newly authored, local fixture. Three
`foaf:knows` directions encode the first three relation types; a shared
depiction resource can encode the co-depiction. Use Factoidal for RDF
querying when connected, and Lean for the state/layout/shader path. Until
that integration exists, label the scene data and expansion as a fixed
fixture rather than implying a live RDF query or historical social graph.

No network calls to the historical sites or personal-data cache belong in
the demo runtime. The archived application itself uses offline
`cache-sha1/*.cz` data when `_ONLINE=false` (lines 11–19); this review did
not download the personal-data cache or the 2.4 MB scutter archive.

[person-study.svg](person-study.svg) is a newly authored, static single-person
study using only supported rectangles, circles, ellipses and lines. It keeps
the historical palette, cream band, plus/minus vocabulary and cyan dashes;
the band's A is made from rectangles, not SVG text. Its geometry is new and
does not copy the original path data. It has no event handlers or RDF input.
It is suitable for the current experimental native SVG command; compiling
it does not establish visual equivalence with the historical application.
