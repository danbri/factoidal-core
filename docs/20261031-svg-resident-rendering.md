# Resident raw WebGPU snapshot sessions

The offscreen transport now exposes `createOffscreenSession`. It retains one
WebGPU device, shader module, pipeline, parameter buffer, texture and readback
buffer across repeated static snapshot draws. Descriptors and the complete
render/copy/submit/map/read/unmap command sequence still come from the existing
Lean render plan. Math, geometry, WGSL and resource sizes remain Lean-owned.
Resource lifetime, serial execution and disposal are host responsibilities.
The ordinary `render` helper wraps a one-frame session and closes it.

Each session uploads the initial data once. Repeated draws retain those exact
parameters; this is not an animation/update-data API. Validation references are
copied at initialization. Overlapping readbacks are refused. A failed readback
poisons the session, so it cannot continue or count a failed frame as presented.
Partial initialization cleans up acquired handles; closing is idempotent and
tries every resource even if an individual dispose throws. The counters record
host WebGPU API resource creations/submissions, not driver-internal compiler,
allocation or deallocation events.

Two new host seam tests cover reuse, one initial upload, serial readback,
disposal, setup failure, pixel corruption and null-adapter behavior. Full warm
checks pass **68 Deno tests and 12 C checks**, plus the specified typechecks.
No Lean source or native window/input code changed in this increment.

## Actual measurement

Installed Chrome 156.0.8078.76, Apple `metal-3`, fallback false, with the actual
Lean-generated eight-person SVG (1,880 primitives, 37,608 floats), explicit
800×600 output and device scale 1:

- Lean compile: about 746ms.
- GPU session setup: about 75ms, including pipeline/resource creation.
- Twenty successful resident frames, each rendered, copied, mapped, unpadded
  and checked against the Lean sample references.
- Frame/readback median 131.4ms, min 127.6ms, max 143.4ms; first 143.4ms.
- One device, shader module and pipeline, two buffers, one texture, one upload,
  twenty submissions and twenty successful frames. Session then closed.

These are host wall-clock, end-to-end round-trip measurements including GPU
work, queue/driver cost, readback and byte processing. No hardware timestamp
query was used; they are not GPU-only execution timings or CPU/GPU comparisons.
The approximate 7.6fps rate does not satisfy a 12 Hz presentation target. A cached
pipeline removes repeated setup, but the current fragment renderer still scans
every primitive for every pixel. This concrete bottleneck motivates compound
path batching of bitmap cells and conservative local bounds; it is not a reason
to weaken the visual comparison or policy checks.

Run the same measurement without installing a browser/package:

```sh
node tests/external/svg/browser_gpu.mjs --fixture INPUT.svg --repeat 20 \\
  --output /tmp/svg-resident --browser /path/to/installed/chrome \\
  --playwright /path/to/playwright-core/index.mjs \\
  --typescript /path/to/typescript/lib/typescript.js
```

`candidate.json` retains per-frame timings, API counters, actual adapter facts
and source/browser/WASM hashes. `--repeat` is bounded 1..120. The fixture mode is
explicitly local and cannot enter the pinned 38-case WPT score. The actual
report is `/private/tmp/foafnaut-default8-resident-gpu/candidate.json`.
Native Deno adapter lookup remains unavailable in this session.
