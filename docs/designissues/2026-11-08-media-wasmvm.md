# Audio and video in Foafnaut, decoded in WasmVM

2026-11-08. Owner: "Try to make basic audio/video work via wasm?"

## Result

- **Audio plays.** Opus and Vorbis are decoded inside Lean's WebAssembly engine
  (WasmVM) at 2.3 to 3.5 times real time on this Mac (native engine build). The
  samples are the same as a native reference decoder's to within 1 in 32768 (the
  last bit of a 16-bit sample). On macOS, `media-bench play` writes our PCM to a WAV
  file and `afplay` plays it.
- **Video decodes.** VP8 frames are decoded inside WasmVM, **bit for bit the same** as
  libvpx's native decoder (all 48 frames of both test clips). Speed: **36 frames per
  second at 160x90** and **10 to 12 frames per second at 320x180** (it depends on the
  load of the machine). The colour conversion in Lean adds little (34 and 9.6 frames
  per second with it). 160x90 decodes faster than its 24 fps; 320x180 does not yet.
- **Containers are read in Lean**: Ogg (pages, CRC, packets) and WebM/Matroska (EBML,
  tracks, clusters, blocks, all four lacing forms). Pure, no recursion, every loop
  bounded by the input size.
- **Not done yet**: the step into the Foafnaut engine (a `foafnaut:media` page, and
  `<video>`/`<audio>` in HTML pages) and the Hub. Reasons and the plan are in "Next".

No host-browser decoder is used. The host's audio output (CoreAudio, or Web Audio on
the Hub) only plays samples that Lean and WasmVM made; `afplay` in the test does the
same.

## Pieces

| Piece | Where | Licence |
|---|---|---|
| Ogg reader | `formal/lean4/L4Factoidal/Media/Ogg.lean` | ours |
| WebM/Matroska reader | `formal/lean4/L4Factoidal/Media/WebM.lean` | ours |
| I420 to RGBA (BT.601) | `formal/lean4/L4Factoidal/Media/Yuv.lean` | ours |
| Decoder driver (WasmVM, WASI host with nothing granted) | `formal/lean4/L4Factoidal/Media/Decode.lean` | ours |
| Tests and measurements | `Media/Tests.lean`, `Media/Bench.lean`: `lake exe media-bench` | ours |
| Build of the decoders | `tools/wasmvm/build-media.sh`, entry points in `tools/wasmvm/media/` | ours |
| libopus 1.5.2 | Wasm module, 126 474 bytes | BSD 3-clause |
| libvorbis 1.3.7 with libogg 1.3.5 | Wasm module, 152 244 bytes | BSD 3-clause |
| libvpx 1.15.2, VP8 decoder only | Wasm module, 98 838 bytes | BSD 3-clause |
| Test clips | `third_party/media/` (4 files, 166 KB) | CC0, made here |

All permissive. The Wasm modules are NOT in the repository: as for HarfBuzz, the owner
decides whether they are vendored or built. The script pins each release tarball by
SHA-256 and keeps sources and outputs in `~/working/media-wasm/` (76 MB).

Build flags: `-O2`, `-sSTANDALONE_WASM --no-entry`, `-mno-simd128`, no threads.
libvpx: `--target=generic-gnu`, no assembly, no run-time CPU detection, VP8 decoder
only. libvpx uses `setjmp`/`longjmp` for errors; with `-sSUPPORT_LONGJMP=wasm` they
become Wasm exceptions (legacy `try`/`catch`/`delegate`), which WasmVM runs. Imports
of the three modules: `env.emscripten_notify_memory_growth` (does nothing), and for
Vorbis also WASI `proc_exit`.

The module API is one packet in, samples or a picture out: `mw_opus_decode`,
`mw_vorbis_header`/`mw_vorbis_decode`, `mw_vp8_decode`/`mw_vp8_i420`. The containers
stay in Lean, so a container bug cannot be a memory-safety bug in C.

## Measurements

Apple M1, native build of `media-bench` (`lake exe media-bench`), other sessions'
builds running. Commands, from `formal/lean4`, with `W=~/working/media-wasm`:

    .lake/build/bin/media-bench test
    .lake/build/bin/media-bench audio $W ../../third_party/media/arpeggio.opus OUT.wav
    .lake/build/bin/media-bench video $W ../../third_party/media/testsrc-320x180.webm 48 OUT

### Audio

Real-time factor = decode time / clip length (below 1 is faster than real time).

| Clip | Codec | Length | Decode time | Instructions | Real-time factor |
|---|---|---|---|---|---|
| `arpeggio.opus` | Opus 48 kHz stereo, 24 kbit/s, Ogg | 4.00 s | 1.64 s | 190 M (115 M/s) | 0.41 (2.4x real time) |
| `arpeggio.ogg` | Vorbis 44.1 kHz stereo, Ogg | 4.00 s | 1.13 s | 120 M (106 M/s) | 0.28 (3.5x real time) |
| `testsrc-320x180.webm` | Opus 48 kHz stereo, WebM | 2.00 s | 0.88 s | 101 M (114 M/s) | 0.44 (2.3x real time) |
| `testsrc-160x90.webm` | Vorbis 44.1 kHz stereo, WebM | 2.02 s | 0.60 s | 61 M (101 M/s) | 0.30 (3.4x real time) |

Comparison with FFmpeg 9.0.1 decoding the same files to 16-bit PCM (`-c:a libopus`,
libopus 1.6.1, for Opus; FFmpeg's own Vorbis decoder): same length; largest
difference 1 (of 32768); Opus 99.97% of samples identical, SNR 111 dB; Vorbis SNR
78 dB (the two Vorbis decoders round differently). Opus pre-skip (RFC 7845 section
4.2), Ogg end trimming by the last granule position, and WebM `DiscardPadding` are
applied. Vorbis in WebM has no end trimming yet: we give 832 samples (19 ms) more
than FFmpeg at the end of `testsrc-160x90.webm`; the samples before that agree as
above.

### Video

| Clip | Decode (WasmVM) | Instructions a frame | Decode fps | With I420 copy and RGBA in Lean |
|---|---|---|---|---|
| `testsrc-160x90.webm`, 48 frames | 1.36 s | 3.7 M | 35.3 | 34.5 |
| `testsrc-320x180.webm`, 48 frames | 4.84 s | 10.9 M | 9.9 | 9.6 |

An earlier run of the 320x180 clip, with less load on the machine, decoded in 3.90 s
(12.3 fps, 133 M instructions a second).

The I420 planes of all frames are byte-identical to FFmpeg's libvpx decoding
(`cmp` of the raw files). The first RGBA picture of the Lean conversion is the same
bytes as the module's own C conversion (`mw_vp8_rgba`).

The colour conversion runs in Lean, not in the interpreter: in WasmVM it took
6.3 M instructions a 320x180 frame (36% of the time); in compiled Lean it takes
2.5 ms a 320x180 frame and 0.6 ms a 160x90 frame. The I420 copy out of WasmVM takes
0.4 ms a 320x180 frame.

### What would make 320x180 real time

12 fps is half of 24 fps. The engine runs about 130 M Wasm instructions a second in
this decoder; 320x180 at 24 fps needs about 260 M. In order of expected gain:

1. WasmVM speed round 2 ("Next" in `2026-11-07-wasmvm-engine.md`): memory 0 held in
   the loop, code as bytecode, a cheaper call. `lake exe wasmvm-bench` already reaches
   369 M/s on a plain loop.
2. More fused ops for the patterns of a video decoder (load-add-store, compare-select,
   clamp).
3. SIMD (`v128`): libvpx has SIMD forms of the inverse transform, loop filter and
   prediction; in an interpreter one SIMD op does 8 or 16 lanes of work in one
   dispatch.
4. Parallel frame decoding is not available for VP8 (frames depend on each other),
   but audio and video can decode on two cores.

In the engine on the Hub (Lean compiled to Wasm, run by V8) the `foafnaut:wasm` page
measured 1.3 to 2.9 times the native library's instruction rate, so the Hub may be
faster than these native numbers.

## Next

1. **`foafnaut:media` page** (`labs/demos/foafnaut/WebMedia.lean`, an op beside
   `wasmPage`): demux in Lean, decode in WasmVM, show the first picture as an image
   paint (`Scene.Paint.image`, as SVG `<image>` uses) and a Lean-drawn play/pause
   control; a "decoded at N fps" slideshow when slower than real time. Needs the
   decoder modules on the Hub (an owner decision: vendor 377 KB of Wasm, or build
   them in CI) and an engine build slot.
2. **`<video src>` and `<audio src controls>` in HTML**: today the HTML layout draws
   neither (`Rendering/Layout.lean` also draws `<img>` as its `alt` text). A video is
   a replaced element with the picture as image paint; this shares the image store
   that `<img>` will need.
3. **Audio output**: the native app host (`native_window.m`) has no audio sink;
   CoreAudio (an `AudioQueue` fed with our PCM) is the plan. On the Hub, Web Audio
   `AudioBuffer`s from our PCM. Both are output only.
4. **Sync**: audio clock as master; show the picture whose time is the latest at or
   before the audio position.
5. More codecs: VP9 (libvpx, BSD), AV1 (dav1d, BSD 2-clause), Theora (BSD). AV1 and
   VP9 are slower to decode than VP8.

## YouTube, and better open sources

YouTube has no plain HTML5 file to play. Its player needs much JavaScript, Media Source
Extensions, DASH manifests and signature handling, and taking media from it outside
its own player and API is against its terms of service. We do not fetch from it.

Better open sources, with direct file URLs and free licences:

- **Wikimedia Commons**: Ogg (Vorbis, Opus, Theora) and WebM (VP8, VP9, AV1, Opus,
  Vorbis), mostly CC BY, CC BY-SA or public domain; each file page states its licence.
- **Internet Archive**: direct MP4, OGV and WebM files; much public-domain material.

H.264 and AAC (MP4) are covered by patent pools, and the free decoders (FFmpeg's,
openh264) bring licence questions (LGPL, or a binary-only patent licence). Not
implemented; not proposed now.

### Hub proxy: proposed patterns (owner decision; not added)

The Hub fetches cross-origin files only through the proxy, by approved pattern. For
media from the two sites above, the patterns would be:

    ^https://upload\.wikimedia\.org/wikipedia/commons/[0-9a-f]/[0-9a-f]{2}/[^/?#]+\.(ogg|oga|ogv|opus|webm)$
    ^https://upload\.wikimedia\.org/wikipedia/commons/transcoded/[0-9a-f]/[0-9a-f]{2}/[^/?#]+\.(ogg|oga|ogv|opus|webm)/[^/?#]+\.(ogg|oga|ogv|opus|webm)$
    ^https://archive\.org/download/[A-Za-z0-9._-]+/[^?#]+\.(ogg|oga|ogv|opus|webm)$
    ^https://ia[0-9]+\.us\.archive\.org/[0-9]+/items/[A-Za-z0-9._-]+/[^?#]+\.(ogg|oga|ogv|opus|webm)$

The fourth is where `archive.org/download` redirects; the proxy must check each
redirect target against the list too. Media only (no HTML, no API), GET and HEAD
only, and a size limit (for example 50 MB). No MP4.
