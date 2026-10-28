# Desktop file browsers over WebDAV: lab trees, a recording harness, first results

Date: 2026-10-28. Issues: https://github.com/danbri/factoidal/issues/1079
(checks with real file browsers), https://github.com/danbri/factoidal/issues/1122
(PUT with no Content-Type). Server design: `2026-10-27-webdav.md`.

Owner, 2026-10-27, verbatim (chat):

> "ok so webdav in osx, windows, linux, ... lets JAVASCRIPT (+wasm) expose a
> localhost service (http:? https:??) that the host OS exposes to users as a
> filesystem?"
>
> "Could we have this and expose stuff like recent SPARQL results, logs, and a
> config dir that had subfolders per remote external service eg.
> config/blah/remote_lws.txt and remote_sparql.txt to collect URLs from user
> that set up a service, and html or images written into these folders as
> dashboards etc.? Are there osx conventions for filenames that make finder
> present stuff in certain ways, e.g. bg images?"

Owner, 2026-10-28, verbatim (chat):

> "Can you make a gh folder eg labs for experimental serve-able filtrees and
> one for testing all these. Once we learn which work per os we can look at
> tweaking webdav eg it might synthesise a readonly views tree with tweaks slto
> use these. Or make a sparql or lws client, etc."

## Result

| path | what it is |
| --- | --- |
| `labs/README.md` | rules for labs: fixtures and notes only, no protocol decision |
| `labs/filetrees/trees.mjs` | eight trees, made in memory: `types`, `links`, `config`, `names`, `hidden`, `sizes`, `many`, `deep` |
| `labs/filetrees/static/` | the committed text fixtures of four trees |
| `tests/webdav-desktop/serve-labs.mjs` | one `local` mount per tree, `webdav-serve`, the seeder, the recording proxy on 127.0.0.1:8091 |
| `tests/webdav-desktop/record-proxy.mjs` | one JSON line per request: headers, XML bodies (4 KiB), status, sizes, time |
| `tests/webdav-desktop/probe-{macos,linux}.sh`, `probe-windows.ps1` | scripted checks per client |
| `tests/webdav-desktop/checklist.md` | GUI checks per file browser |
| `tests/webdav-desktop/selftest.mjs` | the harness without a desktop client: 14 pass, 0 fail, 1 xfail (https://github.com/danbri/factoidal/issues/1122), 0 skipped (out of 15), npm `@factoidal/core` 0.19.0 |
| `tests/webdav-desktop/results/20261028-gvfs-1.54.4/` | first run: GLib gvfs 1.54.4 through `gio` |

The trees are made in memory because some names cannot be in a git tree or
on every local file system: names that differ only by Unicode normalisation
(one file on APFS), names Windows refuses, `Icon\r`, and 51 MB files.

## What the clients are documented to do

From the chat answer of 2026-10-27, written here per rule 7 of `CLAUDE.md`.
Rows marked "to check" are what the lab is for.

* Transport. Plain `http` to 127.0.0.1 works with all four clients. `https`
  needs a certificate that each client trusts (for example from mkcert) and
  gives no protection on loopback. The risk on loopback is other local
  processes and web pages in a local browser: the listener needs a login
  (https://github.com/danbri/factoidal/issues/1108) and a `Host` header check
  against DNS rebinding.
* macOS (webdavfs, Finder): mounts read-only unless the server is class 2
  (LOCK, UNLOCK); `webdav-serve` is class 2. Writes `._*` AppleDouble files
  for extended attributes and resource forks, and `.DS_Store` for folder view
  settings (not when `DSDontWriteNetworkStores` is set).
* Windows (WebClient service): sends Basic credentials over plain http only
  when `BasicAuthLevel` is 2; refuses files above `FileSizeLimitInBytes`
  (default 50,000,000 bytes); limits a PROPFIND response to
  `FileAttributesLimitInBytes` (default 1,000,000 bytes). Microsoft lists
  WebClient as deprecated.
* GNOME Files (gvfs, `dav://`), KDE Dolphin (KIO, `webdav://`): no special
  server needs found yet.
* All clients poll. A file browser shows a change made on the server when it
  lists the folder again (on open, or when its cache ends). A file whose size
  changes between PROPFIND and GET reads short in some clients: a generated
  file (query results, a log) must have a fixed size and ETag per version.
* Every file in a mount also has an http URL. A dashboard page opened from
  that URL can call the server; opened as a file from the mounted folder, its
  requests have origin `null`. Link files give a double-click route to the
  URL: `.webloc` (macOS), `.url` (Windows), `.desktop` with `Type=Link`
  (freedesktop).

Folder presentation conventions, from most to least likely to work on a
WebDAV volume (all "to check" except the first):

1. File type by extension: thumbnails and previews (Quick Look, Explorer
   preview pane, GNOME Sushi) for png, svg, pdf, txt, csv, json, html, and
   Markdown on macOS 15 and later.
2. Hidden names: names that start with `.` on macOS and Linux; GNOME also reads
   a `.hidden` file that lists names to hide (see the gvfs result below).
3. Link files, above.
4. macOS `.DS_Store`: view style, icon positions, background colour or
   picture. Disk images use this with the picture in a hidden `.background/`
   folder; libraries that write `.DS_Store`: `ds_store` (Python, used by
   dmgbuild), `ds-store` (npm, used by appdmg). The picture reference is an
   alias to a volume; whether Finder resolves it on a WebDAV volume is not
   known.
5. macOS custom icons (`Icon\r` with a resource fork, `.VolumeIcon.icns`) and
   Finder tags and labels: extended attributes, which webdavfs stores as `._*`
   files.
6. Windows `desktop.ini` (used only when the folder has the System or
   ReadOnly attribute; over WebDAV that attribute travels in the
   Microsoft `Win32FileAttributes` property), KDE `.directory`.

## Measured 2026-10-28: gvfs 1.54.4 (GLib `gio`)

Engine: npm `@factoidal/core` 0.19.0. Client: `gio` from GLib 2.80.0 with
gvfs-backends 1.54.4, Ubuntu 24.04, in the cloud container (no FUSE, no
GUI). `probe-linux.sh`: 21 ok, 0 FAIL, 11 info (out of 32 lines). Files:
`tests/webdav-desktop/results/20261028-gvfs-1.54.4/`.

1. Mount, list, read, write, rename, mkdir, move into a folder, delete a file
   and a folder: all work. Every file of `sizes` (to 51 MB) copies byte for
   byte. `many` (1,000 files) lists in 0.38 s.
2. All 25 entries of `names` are stored and listed, including `CON.txt`,
   `colon:name.txt`, `question?.txt`, `trailing-dot.`, a 200-character name,
   the NFC/NFD pair and `Icon\r`. The server refuses no name; what each
   client does with them is for the other runs.
3. gvfs takes the type of a file from `DAV:getcontenttype`. A link file
   served as `text/plain` is not a launcher; the seeder now sends the
   shared-mime-info types (`application/x-desktop`, `application/x-mswinurl`,
   `application/x-webloc`).
4. gvfs sends PUT with no `Content-Type`. The server then stores
   `application/octet-stream`, so a file that a GNOME user saves shows as
   binary afterwards: https://github.com/danbri/factoidal/issues/1122
   (proposal: a type from the extension, decided in Lean; xfail in
   `selftest.mjs`).
5. gvfs saves a file with one PUT to the file (no temporary file and MOVE),
   tests that a name is free with PROPFIND Depth 0 (a 404), and sends a
   rename as MOVE with `Overwrite: F`. 35 of 44 PROPFINDs were Depth 0; the
   bodies ask for named properties, never `allprop`.
6. gvfs gives no `standard::is-hidden` attribute to any member over dav: dot
   files and the names in `.hidden` are not marked hidden by GLib. (GNOME Files
   may still hide dot files by name; checklist row G4.)

## Next stages (proposals; each needs an owner decision)

1. Runs on real desktops: macOS Finder (`probe-macos.sh`, then `--finder`),
   Windows Explorer (`probe-windows.ps1`), GNOME Files and Dolphin GUI rows.
   Each finding that needs a server change gets an issue and an xfail.
2. A read-only views tree, made by the server: a mount kind whose folders are
   computed (for example per-client presentation files, a `results/` folder of
   query results with a fixed size and ETag per version). The decisions (which
   files, which names, which types) are in Lean (`L4Factoidal/WebDAV/`); the
   lab trees become the fixtures for its `#guard`s.
3. Configuration folders: a PUT to `config/<service>/remote_lws.txt` or
   `remote_sparql.txt` is read by the server, and the result is written to a
   status file in the same folder. Result 5 above says what one client sends
   when it saves; the other clients' traces come from stage 1.
4. Mount kinds for other services: a SPARQL endpoint (`kind: sparql`, query
   files in, result files out) beside the LWS client mount that exists.
5. `.DS_Store` backgrounds and custom icons: only after a Finder run shows
   that Finder reads them from a WebDAV volume.

## Decisions

| Choice | Who | Notes |
| --- | --- | --- |
| Folders `labs/` (trees) and `tests/webdav-desktop/` (harness) | owner (request), implementer (names) | owner: "a gh folder eg labs ... and one for testing all these" |
| Trees made in memory; text fixtures committed, binaries generated | implementer | names and sizes that git and some file systems cannot hold |
| Each tree is a `local` mount with `storage: files` | implementer | a 51 MB file in the default snapshot storage is one JSON document |
| The proxy changes nothing; the seeder writes straight to the server | implementer | the log holds only what the desktop client sent |
| Proxy default port 8091 (the server's own default is 8090) | implementer | |
| Request bodies kept in the log: first 4 KiB of XML and text | implementer | `results/.gitignore` keeps `*.jsonl` out of git |
| Engine: `--cli`, `$FACTOIDAL_CLI`, this checkout with fetched assets, else `npx -p @factoidal/core` | implementer | the selftest skips (does not use npx) unless `--allow-npx` |
| PUT with no Content-Type: open an issue with a proposal, no server change in this landing | implementer | CLAUDE.md, "Reading owner steers", rule 4 |
