# Foafnaut on Linux

Extract the complete archive, then start the browser from the extracted directory.

```sh
./foafnaut
./foafnaut --url https://example.org/
./foafnaut --html "/path/to/a document.html"
```

The package needs a desktop session, SDL2 2.0.18 or later, and a Vulkan driver. The browser uses SDL's native window and Deno's WebGPU surface. On Ubuntu 24.04 with a Mesa driver, the runtime packages are `libsdl2-2.0-0`, `libvulkan1` and `mesa-vulkan-drivers`. On a Wayland desktop with XWayland, `SDL_VIDEODRIVER=x11 ./foafnaut` selects X11 explicitly.

Control-L selects the address. Type a URL and press Enter. Control-T opens a tab, Control-W closes it, and Alt-Left goes back. Click links to navigate. Close the window to exit.

`./foafnaut --version` reports the engine and program revisions. `sha256sum -c SHA256SUMS` checks the extracted files. The executable embeds its document engine, render plan, browser pages and fonts. If supplied, the matching `libweb-render.so` beside the executable runs the engine worker natively. The default page script engine is BubblePopJS.

The automated window check uses X11 on Xvfb with a software Vulkan driver. Native Wayland, a physical monitor and hardware GPU performance require separate tests. Desktop printing, file chooser panels and the native accessibility bridge currently have macOS implementations.
