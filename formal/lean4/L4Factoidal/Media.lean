/-
L4Factoidal.Media: audio and video for Foafnaut, decoded in the Lean WasmVM engine
(record: docs/designissues/2026-11-08-media-wasmvm.md).

- `Media.Ogg`, `Media.WebM`: the containers, read in Lean (pure, no recursion).
- `Media.Decode`: libopus, libvorbis and libvpx (VP8), compiled to WebAssembly (modules and
  build chain in `danbri/factoidal-builds`, `third_party/media-decoders`), run in WasmVM; PCM
  and RGBA pictures out.
- `Media.Modules`: the SHA-256 and interface version of each module that may be loaded.
- `Media.Tests`, `Media.Bench`: `lake exe media-bench`.
-/
import L4Factoidal.Media.Ogg
import L4Factoidal.Media.WebM
import L4Factoidal.Media.Yuv
import L4Factoidal.Media.Decode
import L4Factoidal.Media.Modules
import L4Factoidal.Media.Tests
