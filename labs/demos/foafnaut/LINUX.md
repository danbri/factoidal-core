# Foafnaut on Linux

Download the [Foafnaut desktop browser for Linux x86_64](https://github.com/danbri/factoidal-builds/releases/download/build-1ba2ef92803c-foafnaut-browser-linux-x86_64/foafnaut-browser-linux-x86_64.tar.gz). The 19 November 2026 package was built from [source commit `1ba2ef92803c30d92b7243c02d7f32ad74e32b57`](https://github.com/danbri/factoidal-core/commit/1ba2ef92803c30d92b7243c02d7f32ad74e32b57).

The package needs a desktop session, SDL2 2.0.18 or later, the Vulkan loader and a Vulkan driver. On Ubuntu 24.04 with Mesa, install `libsdl2-2.0-0`, `libvulkan1` and `mesa-vulkan-drivers`. Deno is included. On a Wayland desktop with XWayland, `SDL_VIDEODRIVER=x11 ./foafnaut` selects X11 explicitly.

Extract the complete archive, check its files and launch from the extracted directory.

```sh
tar -xzf foafnaut-browser-linux-x86_64.tar.gz
cd foafnaut-linux-x86_64
sha256sum -c SHA256SUMS
./foafnaut
./foafnaut --url https://example.org/
./foafnaut --html "/path/to/a document.html"
```

Control-L selects the address. Type a URL and press Enter. Control-T opens a tab, Control-W closes it, and Alt-Left goes back. Click links to navigate. Close the window to exit.

`./foafnaut --version` reports the engine and program revisions. The executable embeds its document engine, render plan, browser pages and fonts. If supplied, the matching `libweb-render.so` beside the executable runs the engine worker natively. The default page script engine is BubblePopJS.

The published archive passed the native window smoke test on Ubuntu 24.04 with X11/Xvfb and Mesa software Vulkan. The test checked an HTTP link click and Back, the live HTTPS Example Domain page, resize and window close, with zero dropped input events. Native Wayland, physical displays and hardware GPU performance have yet to be tested for this release. [Published smoke record](https://github.com/danbri/factoidal-builds/releases/download/build-1ba2ef92803c-foafnaut-browser-linux-x86_64/window-smoke.json)

Desktop printing, file chooser panels and the native accessibility bridge currently have macOS implementations.
