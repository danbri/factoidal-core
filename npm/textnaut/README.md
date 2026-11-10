# @foafos/textnaut

> ⚠️ **EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.**

Textnaut is a text-mode web browser on the Foafnaut engine: the engine loads a page, lays it out
and runs its scripts, and Textnaut maps the positioned text to terminal cells. It also has
screensavers. This package is a launcher plus the Textnaut program; the source is in
`labs/demos/foafnaut/textnaut/` of https://github.com/danbri/factoidal, where its own README has
the details (what is drawn, safety rule, tests).

## Install and run

Textnaut runs on [Deno](https://deno.com) 2.0 or later (tested with 2.9.4); the launcher needs
Node 18 or later and checks for Deno, with an install hint if it is missing.

    npm install -g @foafos/textnaut
    textnaut https://info.cern.ch/
    textnaut --dump --width 80 page.html
    textnaut --screensaver            # no engine, no download

The package has no runtime npm dependencies. Deno runs it with `--allow-read --allow-ffi
--allow-net --allow-env` (read page files and the engine, load a native library, fetch pages,
read the environment), no prompts.

## Try it, and see which engine ran

Each command needs [Deno](https://deno.com). `npx` runs the package with no install. Add `--timing`
to any page command: its last line says `engine native` or `engine wasm`.

| Command | Engine |
|---|---|
| `npx -y @foafos/textnaut https://info.cern.ch/` | Native if foafnaut is installed, else Wasm |
| `npx -y @foafos/textnaut --wasm https://info.cern.ch/` | Wasm |
| `FOAFNAUT_HOME=/nonexistent TEXTNAUT_CACHE=$(mktemp -d) npx -y @foafos/textnaut https://info.cern.ch/` | Wasm, downloaded as for a new user |

The package holds no engine. There is a native library for macOS on Apple silicon only, and it comes
with foafnaut. Linux uses the Wasm engine.

## Engine

The first match wins:

1. `--engine FILE`, or `TEXTNAUT_NATIVE`: a native `libweb-render` library.
2. `TEXTNAUT_WASM_DIR`: a directory with `web-render.mjs` and `web-render.wasm`.
3. The library of an installed foafnaut: `$FOAFNAUT_HOME` or `~/.foafnaut`, `current/foafnaut/libweb-render.dylib` (`.so` on Linux).
4. Otherwise the Wasm engine, fetched once on first use of a page: `foafnaut-web.tar.gz` (8.1 MB) from the pinned release `build-386f8fb43f73-foafnaut-web` of `danbri/factoidal-builds`, checked against the sha256 in `engine-pin.json`, of which only `web-render.mjs` and `web-render.wasm` (30.7 MB) are kept, in `$TEXTNAUT_CACHE`, else `$XDG_CACHE_HOME/textnaut`, else `~/.cache/textnaut`, in a directory named for the engine's commit. The files are re-checked on each run. A download that fails the check is refused and nothing is kept.

`--wasm` skips steps 1 and 3. `--screensaver` and `--help` never download. Offline with no cache,
Textnaut says so and points to the screensavers. There is no telemetry and no other network use
than the pages you ask for and that one download. The pinned engine and this version of Textnaut
are released together; a different engine is your choice with `TEXTNAUT_WASM_DIR` or `--engine`,
and the engine's scene format is checked on every page (a mismatch stops with an error).

## Keys

Arrows, `j`, `k`, Page Up, Page Down, Space, Home, End scroll. `[n]` is a link number: type the
number shown beside a link, then Enter. Tab and Shift-Tab select a link; Enter or Right follows
it. `b` or Left goes back. `?` or `h` opens a help screen with every key and option and the list
of screensavers, each startable from it. `q` or Ctrl-C quits.

## Screensavers

`textnaut --screensaver [NAME]`, a random one with no name. Tab, Space or `n`: next; `b`: the
previous one; `q` or Ctrl-C: quit; any other key quits. They are `plasma`, `tunnel`, `fire`,
`rain`, `stars`, `life`, `snakes`, `sponge` (3D Menger sponge), `sponge4d` (a 4D Menger sponge
turning in the XW and YW planes, coloured by W depth), `lissajous`, `metaballs`, `torus`, `waves`,
`maze` and `cyclic`. There are also some hidden ones. Colour works at 24-bit, 256, 16 and none,
with or without UTF-8; `--colour LEVEL` sets it.

## Licences

Our code is Apache-2.0 (LICENSE). The fetched engine contains third-party components; see NOTICE.
