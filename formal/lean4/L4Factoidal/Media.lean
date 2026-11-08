/-
L4Factoidal.Media: audio and video for Foafnaut, decoded in the Lean WasmVM engine
(record: docs/designissues/2026-11-08-media-wasmvm.md).

- `Media.Ogg`, `Media.WebM`: the containers, read in Lean (pure, no recursion).
- `Media.Decode`: libopus, libvorbis and libvpx (VP8), compiled to WebAssembly by
  `tools/wasmvm/build-media.sh`, run in WasmVM; PCM and RGBA pictures out.
- `Media.Tests`, `Media.Bench`: `lake exe media-bench`.
-/
import L4Factoidal.Media.Ogg
import L4Factoidal.Media.WebM
import L4Factoidal.Media.Yuv
import L4Factoidal.Media.Decode
import L4Factoidal.Media.Tests
