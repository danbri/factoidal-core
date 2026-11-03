# Desktop file browser checklist

Manual checks that the probe scripts cannot make: what the file browser
shows and what its user can do. Tracking:
https://github.com/danbri/factoidal/issues/1079 (checks with real file
browsers).

Start the lab first (`node tests/webdav-desktop/serve-labs.mjs`), connect the
file browser to the proxy origin it prints, do the checks, then press Ctrl-C
in the lab terminal. The request log (`requests.jsonl`, `summary.md`) and
`final-tree.md` record what the file browser sent while you worked.

Copy the table of your system into `results/<run>/checklist.md` and give
each row one of: `yes`, `no`, `partly: <what>`, `not tried`. Add a note when
the result differs from the "expected" column.

## macOS Finder

System: macOS version, Apple silicon or Intel. Connect: Go > Connect to
Server (Cmd-K), the proxy origin.

| # | check | expected | result |
| --- | --- | --- | --- |
| M1 | the volume mounts and Finder shows 8 folders | yes | |
| M2 | the volume is writable (a new folder can be made in `config`) | yes (server is class 2) | |
| M3 | icon view of `types`: thumbnails for image.png, chart.svg, document.pdf, page.html | yes for png, svg, pdf; html unknown | |
| M4 | Quick Look (space bar) on each file in `types`: which show content | txt, md, csv, json, html, svg, png, pdf | |
| M5 | `names`: which names show, and how (`colon:name.txt` shows as `colon/name.txt`) | | |
| M6 | `names/normalisation-pair`: one or two entries | unknown | |
| M7 | `names/case-pair`: one or two entries; open each | unknown | |
| M8 | `hidden`: dot files hidden; Cmd-Shift-. shows them | yes | |
| M9 | double-click `links/open-dashboard.webloc`: the browser opens the dashboard and it lists the mounts | yes | |
| M10 | open `links/dashboard.html` from Finder (as a file): the mount list stays empty | yes (origin null) | |
| M11 | drag `sizes/51MB.bin` to the Desktop; drag it back as `copy.bin` | yes | |
| M12 | open `config/config/example-sparql/remote_sparql.txt` in TextEdit, change it, save: the change is on the server (re-open it) | yes | |
| M13 | rename a file in Finder; move a file between two folders of one mount | yes | |
| M14 | move a file between two mounts (for example `types` to `config`) | Finder copies, then deletes; server answers MOVE across mounts with 502 | |
| M15 | add a Finder tag (colour) to a file; does it stay after unmount and mount | unknown (tags are xattrs, stored as `._` files) | |
| M16 | after the session, `final-tree.md`: which `.DS_Store` and `._*` files Finder wrote | | |
| M17 | Finder > View > Show View Options > background picture on a folder: does it stay after unmount and mount | unknown (stored in `.DS_Store`) | |

## Windows Explorer

System: Windows edition and build. Connect: This PC > Map network drive >
Folder: the proxy origin (or `\\127.0.0.1@PORT\DavWWWRoot`). The WebClient
service must run.

| # | check | expected | result |
| --- | --- | --- | --- |
| W1 | the drive maps and Explorer shows 8 folders | yes | |
| W2 | thumbnails (View > Large icons) in `types` | png yes; others unknown | |
| W3 | preview pane (Alt-P) for txt, html, pdf, png | | |
| W4 | `names`: which names show; what happens to `question?.txt`, `colon:name.txt`, `CON.txt`, `trailing-dot.` | some names cannot be shown or opened | |
| W5 | `hidden`: is `.dotfile` hidden; does `desktop.ini` change the folder icon or tooltip | dot files shown; desktop.ini unknown | |
| W6 | double-click `links/open-dashboard.url` | the browser opens the dashboard | |
| W7 | copy `sizes/51MB.bin` to the Desktop | fails with the default FileSizeLimitInBytes (50000000) | |
| W8 | edit `remote_sparql.txt` in Notepad and save | yes | |
| W9 | rename, new folder, delete to the Recycle Bin (or delete at once) | delete is permanent on a network drive | |
| W10 | `deep`: open the leaf folder (path length) | unknown | |
| W11 | after the session: which `desktop.ini` or `Thumbs.db` files Explorer wrote | | |

## GNOME Files (Nautilus)

System: distribution, GNOME version. Connect: Other Locations > Connect to
Server > `dav://127.0.0.1:PORT/`. `probe-linux.sh` covers the GLib client;
these rows are the GUI.

| # | check | expected | result |
| --- | --- | --- | --- |
| G1 | the location opens and shows 8 folders | yes | |
| G2 | thumbnails in `types` (GNOME may not make thumbnails for remote files: Settings > Files > Show thumbnails) | depends on the setting | |
| G3 | Sushi preview (space bar) | | |
| G4 | `hidden`: is `listed-in-dot-hidden.txt` hidden (`probe-linux.sh` found GLib does not apply `.hidden` over dav) | no | |
| G5 | double-click `links/open-dashboard.desktop` | opens the browser when the server sends application/x-desktop | |
| G6 | edit `remote_sparql.txt` in Text Editor and save | yes | |
| G7 | after the session: which `.Trash-*` or `.goutputstream-*` files appeared | | |

## KDE Dolphin

Connect: address bar `webdav://127.0.0.1:PORT/`.

| # | check | expected | result |
| --- | --- | --- | --- |
| K1 | the location opens and shows 8 folders | yes | |
| K2 | previews in `types` (Dolphin: Preview, and Settings > General > Previews > remote files size) | depends on the setting | |
| K3 | `hidden`: does `.directory` give the folder the blue icon | unknown | |
| K4 | double-click `links/open-dashboard.desktop` | opens the browser | |
| K5 | edit `remote_sparql.txt` in Kate and save | yes | |
| K6 | after the session: which `.directory` files Dolphin wrote | | |
