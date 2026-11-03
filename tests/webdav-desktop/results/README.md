# Results of desktop WebDAV runs

One folder per kept run, named `YYYYMMDD-<client>-<version>` (for example
`20261028-gvfs-1.54.4`). It holds what `serve-labs.mjs` and the probe wrote:
`summary.md`, `final-tree.md`, `environment.json`, `probe-*.md`, and a
filled copy of `../checklist.md` when the GUI rows were done.
`requests.jsonl` and `seed.json` are not committed (`.gitignore`): they are
large and can hold file content.

| run | client | probe | notes |
| --- | --- | --- | --- |
| [`20261028-gvfs-1.54.4`](20261028-gvfs-1.54.4/) | GLib gvfs 1.54.4 (`gio`), Ubuntu 24.04, in a container | `probe-linux.sh`: 21 ok, 0 FAIL, 11 info | no GUI; see the design record for findings |
