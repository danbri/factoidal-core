# One executable file per platform (or one for all): Factoidal with a JS runtime, a GUI and the servers

Date: 2026-10-28. Status: study, no code. Decision needed (section
"Proposal").

Owner, 2026-10-28, verbatim (chat):

> "Also: could we make a multiplatform exe with a node/deno impl embedded plus
> factoidal codebase, doubleclocking could run a factoidal gui with option of
> launching server. Cf llamafile, grail."

"grail" is read here as GraalVM (its native-image tool makes one executable
from a Java program, and it can embed a JavaScript and a WebAssembly engine).
If another project was meant, this record needs a row for it.

## What has to go into the file

* The engine: the one fat core wasm of `@factoidal/core` (owner, 2026-10-20,
  "a single fat core"), or the native Lean build (`danbri/factoidal-builds`
  sets `linux-x86_64`, `darwin-arm64`).
* The hosts: today the servers (`serve`, `lws-serve`, `webdav-serve`,
  `authz-serve`, `xmpp-serve`) and the CLI are Node hosts in
  `npm/factoidal/`. They carry sockets, files and fetches only (iron rule 7);
  every decision is in the wasm.
* A GUI: the hub pages (`docs/web/hub/`) already run the engine in a browser.

## Options

| Option | Platforms from one build | Embeds wasm | Notes |
| --- | --- | --- | --- |
| `deno compile` | 6 targets, cross-compiled from any host: x86_64 and aarch64 for Windows, macOS, Linux (aarch64 Windows from Deno 2.9.3) | `--include` files, read at run time | `--icon` (Windows targets), `--no-terminal` (hides the Windows console); ad hoc signature on macOS by default; the package already runs on Deno |
| `bun build --compile` | 8 targets: Linux x64 and arm64 (glibc and musl), Windows x64 and arm64, macOS x64 and arm64 | `import ... with { type: "file" }`, then `WebAssembly.instantiate` | `--windows-hide-console`, `--windows-icon` (icon and metadata not when cross-compiling) |
| Node single executable application | one per platform; a blob for another platform needs `useCodeCache` and `useSnapshot` off, and the blob must match the Node binary's version | `assets` in the configuration, `sea.getAsset` | Stability 1.1 (active development); `node --build-sea` from v25.5.0; sign on macOS (`codesign --sign -`) |
| Actually Portable Executable (Cosmopolitan `cosmocc`, the llamafile method) | one file for Linux, macOS, Windows, FreeBSD, OpenBSD, NetBSD on x86_64 and aarch64 | not applicable: native code | no JavaScript runtime is built this way; the hosts would be native (Lean native build, C). llamafile is C++ built with `cosmocc`. On Windows the file must be renamed to `.exe` and be under 4 GB |
| GraalVM native-image with GraalJS and GraalWasm | one per platform, built on that platform | yes | large; adds a Java toolchain to `danbri/factoidal-builds` |

Sizes are not measured here. A Deno or Bun executable carries its runtime
(tens of MB) plus the wasm.

### The APE option in more detail

This is the one way to get one file for every operating system. It needs:

1. The Lean tree compiled with `cosmocc` (Lean emits C; the Lean runtime is C
   and C++). Not tried. Risks: the Lean runtime's thread and I/O layers
   on Cosmopolitan, the HACL\* assembly (`skills/crypto-policy`), and the
   build time in CI.
2. Native hosts: the HTTP, WebDAV, LWS servers as native loops (Lean `IO`, or
   a small C layer) in place of the Node hosts. This agrees with the
   Lean-first direction, but it is a second set of hosts to test against the
   same suites (litmus, Touchstone, `tests/webdav/`).
3. A GUI served as web pages from the same file (the llamafile server serves
   a chat page on a local port the same way).

## Double-click behaviour

* macOS: a downloaded executable has the quarantine attribute; Gatekeeper
  blocks it unless it is signed with a Developer ID and notarized. A bare
  executable opened from Finder runs in Terminal. A double-click application
  is a `.app` bundle, which is a folder, so "one file" means a `.dmg` or
  `.zip` around it.
* Windows: an unsigned `.exe` gets a SmartScreen warning on first run.
  `--no-terminal` (Deno) or `--windows-hide-console` (Bun) removes the
  console window.
* Linux: most file managers do not run an executable on double-click; a
  `.desktop` file or an AppImage is the usual route.

## GUI

Proposal: the executable starts a local web server on 127.0.0.1 with a
random port and a one-time token in the URL, and opens the default browser
at that URL (`open`, `start`, `xdg-open`). The pages are the hub pages plus a
control page: start or stop `webdav-serve` and the other servers, mount the
WebDAV server in the file browser (macOS AppleScript `mount volume` with the
http URL, Windows `net use`, Linux `gio mount`: to be checked in the lab of
`2026-10-28-desktop-webdav-labs.md`), show the request log. A native window
(a system webview through Tauri, wry or Deno's webview bindings) can come
later; it adds a per-platform build of its own.

## Proposal (decision needed)

1. Stage 1: `deno compile` of the `factoidal` CLI with the wasm included, for
   the 6 Deno targets, in `danbri/factoidal-builds`, released next to the
   other build products. Test: the existing host suites run against the
   compiled file in place of `node bin/factoidal.mjs`. Bun is the second
   choice (two more Linux targets, musl).
2. Stage 2: a `factoidal app` command: the local web GUI above.
3. Stage 3: a study of the APE route: compile the Lean native tree with
   `cosmocc`, measure size and speed against the Deno file, and list what a
   native host set needs.
4. Signing (Developer ID and notarization on macOS, Authenticode on Windows)
   needs the owner's certificates; until then the files run from a terminal
   or after the user allows them.

## Sources

* Deno compile: https://docs.deno.com/runtime/reference/cli/compile/
* Bun single-file executables: https://bun.com/docs/bundler/executables
* Node single executable applications: https://nodejs.org/download/release/v26.7.0/docs/api/single-executable-applications.html
* Cosmopolitan `cosmocc`: https://github.com/jart/cosmopolitan (README of the `cosmocc` release, platform table)
* llamafile: https://github.com/mozilla-ai/llamafile (README: Windows `.exe` rename and 4 GB limit)
