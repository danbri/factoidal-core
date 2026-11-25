# Foafnaut Linux desktop browser release, 19 November 2026

The desktop archive `foafnaut-browser-linux-x86_64.tar.gz` contains the `foafnaut` executable,
the SDL2 window library and provenance files. The executable includes Deno, the built-in
Wasm engine and fonts. The archive is 60,248,650 bytes with SHA-256
`f20df26d88fc44e166d7faa14e53c170d3022ad43fe2542d159d354d51a47a52`.
[Release and assets](https://github.com/danbri/factoidal-builds/releases/tag/build-1ba2ef92803c-foafnaut-browser-linux-x86_64) ·
[Linux launch instructions](../labs/demos/foafnaut/LINUX.md)

The release uses source commit `1ba2ef92803c30d92b7243c02d7f32ad74e32b57` and includes the
cookie persistence and navigation merge `3249012ac`. The processing-instruction attributes
merge `7311bbaa6` followed this release's source commit.
[Linux window and packaging PR](https://github.com/danbri/factoidal-core/pull/617) ·
[Processing-instruction attributes PR](https://github.com/danbri/factoidal-core/pull/619)

The Linux jobs passed, including the check that extracted the release archive to a new path
and opened its SDL2 window on Ubuntu 24.04 under X11/Xvfb with Mesa software Vulkan. The test
confirmed a link click and Back with local HTTP pages, pixels from the live HTTPS Example
Domain page, a frame after resize and clean exit on close. The browser used its Wasm worker,
presented 12 frames and reported zero dropped input events. Native Wayland, physical displays and
hardware GPU performance have yet to be tested for this release.
[Final Linux build and publish run](https://github.com/danbri/factoidal-builds/actions/runs/44439382552) ·
[Published smoke record](https://github.com/danbri/factoidal-builds/releases/download/build-1ba2ef92803c-foafnaut-browser-linux-x86_64/window-smoke.json)

The `foafnaut-linux-x86_64` release set supplies the standalone engine for Textnaut and headless tests.
The `foafnaut-browser-linux-x86_64` release set supplies the desktop browser.
[Release gate PR](https://github.com/danbri/factoidal-builds/pull/54) ·
[Linux desktop delivery issue](https://github.com/danbri/factoidal-core/issues/613)
