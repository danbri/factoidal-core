# Foafnaut's Linux window

The Linux library release runs the document engine for Textnaut and WPT. The new package runs the same HTML browser entry point as the macOS app, with a Linux window and desktop input. The work is tracked in [core issue 613](https://github.com/danbri/factoidal-core/issues/613).

SDL2 supplies the display, window, committed Unicode text, pointer events, clipboard and resize notifications. The shim passes the X11 window ID and display pointer, or the Wayland surface and display pointers, to Deno 2.9.4. WebGPU presents the engine's frames to that surface. The browser reads the engine's existing Linux key table, including Control-L for the address bar and Alt-Left for history. The shell editor and page script engine receive the same editing operations as the existing desktop host. [Deno surface ABI](https://docs.deno.com/api/deno/gpu/)

CI stages the document and render-plan Wasm from its Foafnaut engine build. The packager compares the document engine's own full source commit with the host checkout and checks the render-plan source witness. A matching native Linux library, when present, runs the worker. The package records the engine input hashes, source revision and file hashes. The browser can run the bundled Wasm worker with the same renderer. [Package and launch instructions](../labs/demos/foafnaut/LINUX.md)

The release gate launches the extracted browser under Xvfb and checks colours in the mapped X11 window. XTest clicks a link, goes back, enters an HTTPS address and resizes the window. The gate also checks the live page title and ink, a presented frame at the new size, the worker backend and a clean window-manager close. It saves the screenshots and the frame trace. Xvfb with a software Vulkan driver gives no measurement of physical GPU speed or native Wayland behaviour.

At implementation time the shared Mac passed the Deno surface and input checks, and the SDL event transport returned 30,000 ordered, coalesced events plus separate resize and clipboard checks. No engine theorems changed. Before this change there was no Linux window launch to time. Linux launch time and frame counts come from the package probe once it runs.
