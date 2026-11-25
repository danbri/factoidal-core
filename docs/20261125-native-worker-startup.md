# Native worker startup without a second document engine

The desktop host loaded the WebAssembly document engine in each native worker, and used it for the synchronous link picker. The current native shim already exposes the same picker. Use it in the native backend and retain the WebAssembly fallback for libraries that lack the symbol. The main-thread browser engine continues to use WebAssembly. The native shim keeps mutable document state and remains confined to one thread.

On Ubuntu 24.04, four alternating fresh processes per arm used the same exact native library, WebAssembly bytes, font, and scripted fixture. The median worker ready time was 244 ms before and 67 ms after. Median process RSS after the first compile was 256 MiB before and 133 MiB after. The native and WebAssembly pickers returned the same target for the fixture's fractional coordinates and the same miss. The windowed gate separately checks the browser's normal link, back, live navigation, and resize behavior.

[Measurements](https://github.com/danbri/factoidal-builds/actions/runs/45531494735) · [Everyday page tracker](https://github.com/danbri/factoidal-core/issues/712)
