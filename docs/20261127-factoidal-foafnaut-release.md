# Factoidal npm and Foafnaut macOS release preparation

The npm registry served 0.38.0 from core commit `023a9ce1211b` at the start of this session. A fresh install reported a matching WebAssembly hash and release stamp. The 0.38.1 patch release includes the XMPP TLS startup checks and a newer engine.

The [build of core 51bcef8c8cb2](https://github.com/danbri/factoidal-builds/actions/runs/46012088986) passed 2,176 npm tests of 2,177. The remaining test failed the browser host-policy audit. The browser Wasm build also failed at link time. It reached the Lean runtime's libuv file metadata functions when Web Audio read its decoder files, so the Foafnaut bundle did not build.

- The decoder loader reads at most the pinned size plus one byte through a binary file handle. The existing size and SHA-256 checks still determine which decoder files the engine accepts. Pages with no decode jobs do no decoder file work.
- The built-in engine supplies the HTTP response status class for the native loader's navigation path. `statusClass_ok_iff` and `statusClass_error_page_iff` characterise the two classes used by the host. Both depend on `propext`, `Classical.choice` and `Quot.sound`. The host uses one shared default timeout across its HTTP transports. The policy audit passed with 689 sites, down from the previous cap of 690.
- Six local Deno tests passed, covering the native network transport and the page loader's routing. A standalone Lean check of the changed functions checked the two theorems and read sizes for empty, short, exact and oversized files. The full build and release checks run in CI.

## Browser Wasm size

The [candidate build](https://github.com/danbri/factoidal-builds/actions/runs/46041505276/job/140650234378) linked the renderer and measured 56,085,800 bytes raw and 6,694,464 bytes Brotli. This is 4.41% and 4.20% above the previous references. It includes the accumulated Web Audio, SVG and navigation work since those references. The size contribution of each change was not measured.

The release uses the measured candidate as the new reference for those two files. The existing raw 2% tolerance and compressed 200,000-byte allowance still apply. The native size references are unchanged. Further size work is tracked in the [engine size budget issue](https://github.com/danbri/factoidal-core/issues/551).
