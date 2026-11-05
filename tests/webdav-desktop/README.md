# WebDAV and desktop file browsers

Find what macOS Finder, Windows Explorer, GNOME Files and KDE Dolphin do with
`factoidal webdav-serve`: which files they show and preview, which names they
take, how they save, which metadata files they write. Tracking:
https://github.com/danbri/factoidal/issues/1079 (checks with real file
browsers). The trees are in [`labs/filetrees/`](../../labs/filetrees/).
Design record: `docs/designissues/2026-10-28-desktop-webdav-labs.md`.

Current mode: read only (https://github.com/danbri/factoidal/issues/1147).
The harness starts an authenticated LWS server and fills it through HTTP as
its owner. WebDAV reaches that server through `kind: lws` mounts. The named
guest `labs` can read those mounts; every WebDAV write must return 403.
The older desktop probe scripts and saved results include successful writes;
those expectations describe the earlier server, not the current mode.

```
node tests/webdav-desktop/serve-labs.mjs            # serve every tree on http://127.0.0.1:8091/
bash tests/webdav-desktop/probe-macos.sh  http://127.0.0.1:8091/ RESULTS_DIR
bash tests/webdav-desktop/probe-linux.sh  http://127.0.0.1:8091/ RESULTS_DIR
powershell -ExecutionPolicy Bypass -File tests\webdav-desktop\probe-windows.ps1 -Origin http://127.0.0.1:8091/ -Out RESULTS_DIR
# then the GUI rows of checklist.md; Ctrl-C in the serve-labs terminal writes the summary
node tests/webdav-desktop/selftest.mjs              # the harness itself, no desktop client
```

`serve-labs.mjs` needs Node 22 or later and an engine: this checkout's
`npm/factoidal` after `tools/fetch-builds.sh`, or `--cli PATH` to another
`factoidal.mjs`, or (when neither is there) `npx -y -p @factoidal/core
factoidal`, which downloads the published package.

| file | what it does |
| --- | --- |
| `serve-labs.mjs` | starts the selected CLI as both authenticated LWS (`storage: files`) and WebDAV, seeds LWS subtrees with HTTP PUT, gives each mount `users: labs`, starts the recording proxy; on exit writes tree, request and server diagnostics |
| `record-proxy.mjs` | forwards every request unchanged and writes one JSON line per request to `requests.jsonl` (method, path, headers, XML bodies, status, sizes, time); Authorization and Cookie values are not written |
| `seed.mjs` | authenticated LWS PUT and WebDAV PROPFIND with plain HTTP; the Content-Type of each fixture |
| `summarise.mjs` | `requests.jsonl` to Markdown: clients, methods and statuses, PROPFIND depths and properties, metadata files the client wrote, failed requests, how editors saved files in `config` |
| `probe-macos.sh` | `mount_webdav`, then shell checks, Quick Look thumbnails (`qlmanage`), xattrs; `--finder` also opens the folders in Finder |
| `probe-linux.sh` | `gio` on `dav://` URIs (the GLib client of GNOME Files); in a container run it under `dbus-run-session` |
| `probe-windows.ps1` | the WebClient service and its registry limits, `net use`, file checks with PowerShell |
| `checklist.md` | the checks that need a person at the GUI, one table per file browser |
| `selftest.mjs` | starts the lab and acts as a client through the proxy; checks the harness, not a desktop client |
| `harness.test.mjs` | child startup, diagnostics, timeout and cleanup checks without an engine or sockets (`node --test`) |
| `results/` | one folder per run that is kept: `summary.md`, `final-tree.md`, `probe-*.md`, `environment.json`, a filled `checklist.md` |

Rules:

1. The harness makes no protocol decision (iron rule 7 of `CLAUDE.md`): the
   proxy changes nothing, the seeder is an ordinary client. A server change
   that a result asks for goes into `formal/lean4/L4Factoidal/WebDAV/`.
2. The servers and proxy listen on 127.0.0.1. The WebDAV lab explicitly
   serves its test fixtures to `--guest labs`; its generated LWS owner key
   stays in the temporary configuration. The trees hold no secret. This
   guest configuration is for these fixtures, not for a personal storage.
3. A result folder holds no request body of a file you care about: the log
   keeps the first 4 KiB of XML and text bodies. Check `requests.jsonl`
   before you commit it, or commit `summary.md` only (`results/.gitignore`
   leaves `*.jsonl` and `seed.json` out).

The selftest requires an engine. An explicit `--cli` is used for both
servers and never falls back to another engine. Missing engines and startup
failures fail the gate. The full size fixtures (including 49 MB and 51 MB)
remain required; a small-file pass is not a pass of the complete harness.
See [the executable investigation](../../docs/20261029-webdav-executable-gate.md)
for the 0.26.0 measurements and outstanding large-file failure.
