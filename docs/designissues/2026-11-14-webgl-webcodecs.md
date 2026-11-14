# WebGL and WebCodecs: the object models, validation and pixel work in Lean

Date: 2026-11-14. Branch `wip/gl-codecs`. Related records: `2026-11-08-page-gpu.md` (the GPU command
path, the GLSL front end, the first WebGL slice), `2026-11-08-canvas-2d.md`, `2026-11-13-wpt-plan.md`.

## 1. Where the Web Platform Tests are

Baseline: main `19fb349c1`, Linux full run `20261114T0314Z` (83.44%), page scripts on BubblePopJS.

| Directory | Chrome subtests | Passed before |
|---|---:|---:|
| webgl | 4,279 | 124 |
| webcodecs | 3,922 | 9 |

**WebGL.** 4,198 of the 4,279 subtests are one file run twice: `idlharness.any.js` in a window and in a
worker (2,099 each). It tests the interface objects of `webgl1.idl` and `webgl2.idl` and makes no
context. The other 21 files have 81 subtests: about 51 need state, queries and error generation with no
pixels; about 19 need a framebuffer that `clear` writes and `readPixels` reads; 5 to 8 need a shaded
triangle with depth or stencil tests, then `readPixels`.

**WebCodecs** (window and worker together):

| Class | Subtests | Needs |
|---|---:|---|
| `idlharness` | 630 | the 12 interfaces; the object tests need `ImageDecoder` on a PNG and an `ImageBitmap` |
| object model, validation, `copyTo` bytes | 943 | no codec, no canvas |
| `VideoFrame` with a 2D canvas or an `ImageBitmap` | 897 | 708 of them compare `copyTo` to RGB with what `drawImage(frame)` draws, in sRGB and in Display P3 |
| WebGL upload of a frame, then `readPixels` | 53 | a sampled quad: rasterisation |
| `ImageDecoder` | 118 | PNG, JPEG and GIF are in Lean; AVIF, WebP and ICO are not |
| PCM audio "decode" | 148 | byte work (u8, s16, s24, s32, f32, A-law, mu-law) |
| real encoders and decoders | 1,131 | AV1, VP8, VP9, H.264, H.265; Opus, Vorbis, MP3, FLAC, AAC |

## 2. The rule

Decisions are Lean's; the page glue (`prelude.js`) converts arguments as Web IDL says, keeps the page's
objects and moves the bytes Lean lists; the host runs the GPU commands Lean emits. No page content goes
to a host WebGL, a host canvas or a host media stack. An engine with no codec says so: a valid
configuration is `supported: false` and `configure` closes the codec with a `NotSupportedError`.

## 3. WebGL

### 3.1 One table of the IDL (`PageGl.Table`, `PageGl.Idl`)

`tools/webgl-idl-table.py` writes `PageGl/Table.lean` from the Khronos IDL: for each interface mixin its
constants (297 for WebGL 1, 262 more for WebGL 2), attributes and operations, each operation with the
fewest arguments an overload takes and the argument types of every overload (a letter for each IDL type).
`PageGl.Idl` joins the mixins into the two interfaces (`mergeOps`: one function a name, the smallest
length, all overloads).

The page glue asks for the interface text once (web_api op 100) and builds `WebGLRenderingContext` and
`WebGL2RenderingContext` from it: constants on the interface object and its prototype, attributes,
operations with their `name` and `length`, brand checks, and argument conversion by the overload
signatures (a call that matches no overload is a `TypeError`). The state machine reads its enum values
from the same lists (`Api.isConstant`), so the page and the validator cannot disagree about a constant.

The two interfaces are made when a page first names one of them (both then become data properties of
the global object). The 15 small interfaces (`WebGLObject` and its 11 kinds, `WebGLUniformLocation`,
`WebGLActiveInfo`, `WebGLShaderPrecisionFormat`, `WebGLContextEvent`) are plain classes. All are exposed
in workers, as the IDL says.

### 3.2 The state machine and the GL error model (`PageGl.State`)

A context is an error flag and a state. `exec` checks and applies one command on the state and never
sees the flag: it answers the new state and a reply, or the GL error the command generates (the state is
then unchanged). `step` records that error only when the flag is clear; `getError` answers the flag and
clears it. So the rule "the first error wins" holds for every command by construction.

`exec` models: objects (create, delete, `is*`, the kind and the target an object was first bound to),
bindings (buffers, textures, framebuffer, renderbuffer), the stencil functions and masks of both faces,
`clearStencil`, pack and unpack alignment, vertex attribute pointers and their queries, `getParameter`
for the values it holds and the limits, and the sizes of `texImage2D`, `texImage3D` and `readPixels`
(format and type pairs of each WebGL version, level and size limits, the client buffer against
`imageBytes`). No compressed texture format is supported, so every compressed upload is `INVALID_ENUM`.
A command it does not model answers `defer`, and the drawing path of record `2026-11-08-page-gpu.md`
serves it (buffers, programs through the GLSL front end, uniforms, `drawArrays`); an error that path
finds is recorded through the same flag (`raise`). Only modelled commands cross into Lean: uniforms and
draws cost what they did.

Limits given to a page: `MAX_TEXTURE_SIZE` 2048, `MAX_3D_TEXTURE_SIZE` 256, `MAX_ARRAY_TEXTURE_LAYERS`
256, `MAX_VERTEX_ATTRIBS` 16, 65,536 live objects a context (then `OUT_OF_MEMORY`), 1,024 contexts a
session.

### 3.3 Drawing, and the GLSL ES to WGSL translator

Drawing stays on the engine's GPU command path: Lean emits WGSL and typed GPU commands, `HostCmd.safe`
is checked on every one, the host replays them. The translator (`PageGpu.Glsl`, of 2026-11-08) is a
compiler front end with one AST for GLSL ES 3.00 and 1.00, whose output goes through the same WGSL
validator and hardening as page WGSL, so the subset, cost, loop and index-clamping theorems cover WebGL
shaders with no new proof.

What it takes today: `attribute`/`in`, `varying`/`out`, loose uniforms (one uniform block laid out by
Lean), `float`, `int`, `uint`, vectors and matrices, `const` arrays, `for` with literal bounds, `if`, the
built-in functions of the WGSL subset plus `mod`, two-argument `atan` and `inversesqrt`, `gl_Position`,
`gl_FragColor` or one `out vec4`, `gl_FragCoord`. Refused, with the reason: user functions, `discard`,
`return` in `main`, `while`, samplers and textures, arrays of varyings or uniforms, and preprocessor
lines other than `#version`, `#extension` and `#ifdef GL_ES`.

What the WebGL tests and everyday pages use most, in the order to add it (each is a translator change
with the existing theorems kept, plus what is listed):

1. User functions (inlined or emitted as WGSL functions; the cost bound needs the call graph to be
   acyclic, which GLSL ES guarantees: no recursion) and `return`.
2. `sampler2D` and `texture2D`/`texture`: a WGSL texture and sampler pair for each GLSL sampler; needs
   textures in the command model with the taint label of record 2026-11-08 section 4.6.
3. `gl_PointSize` and points (a quad a point in the vertex stage), `discard`.
4. Uniform blocks (`getUniformLocation-uniform-block-member`), arrays of uniforms.
5. `#define` of constants and `#if` (a small preprocessor in Lean).
6. `precision`, `invariant`, `highp` qualifiers are already read and dropped.

Not planned: `while` with a data-dependent bound and dynamic indexing of sampler arrays (outside the
bounded subset by design).

### 3.4 Pixels: what the WPT runner can and cannot check

The runner has no GPU, and the engine has no read-back from the host (record 2026-11-08 section 1: the
page never sees composited pixels). Tests that draw and then call `readPixels` pass only when Lean itself
holds the pixels. `clear` then `readPixels` (and `copyTexImage2D` of a cleared framebuffer) can be kept
by Lean exactly: about 19 subtests, not done. A shaded triangle needs a software rasteriser in Lean that
runs the WGSL AST: 5 to 8 WebGL subtests and 53 WebCodecs ones; a design of its own, not started.

## 4. WebCodecs: frames

- `WebCodecs.Format`: the 23 pixel formats as planes (bytes of a sample position, sub-sampling factors).
- `WebCodecs.Layout`: "Parse Visible Rect", "Verify Rect Offset Alignment" and "Compute Layout and
  Allocation Size" as `copyPlan`, which answers one `Move` for each plane: the rows to copy, with their
  place in the frame's resource and in the page's buffer. The same plan serves `copyTo` (resource to the
  page) and the constructor from bytes (the page's layout to the resource). The page glue moves the rows.
- `WebCodecs.Frame`: the constructor from bytes (`ofBuffer`) and from another frame (`derive`): visible
  rectangle, display size (the scales of the source, rounded half up), rotation and flip. A rotation is
  read from the page's double exactly (sign, mantissa, exponent; integer arithmetic), so
  `Number.MAX_VALUE` has the rotation of its exact value.
- `WebCodecs.Convert`: `copyTo` to RGBA, RGBX, BGRA or BGRX: re-orderings, and Y'CbCr to R'G'B' with the
  BT.601, BT.709 and BT.2020 matrices in limited or full range, by exact integer arithmetic rounded once.
  8-bit formats. Primaries and transfer characteristics are not converted: an sRGB destination only; a
  Display P3 destination is refused (`NotSupportedError`).
- An RGBX or BGRX frame keeps 255 in its padding byte (the frame is opaque whatever the page put there).
- `WebCodecs.Orient` (op 126): a frame's rotation (clockwise quarter turns) then flip (a horizontal
  mirror), applied to its visible rectangle as packed pixels, for `drawImage(frame)` and
  `createImageBitmap(frame)`. Each output byte copies the source byte `byteSrc` names; `byteSrc_lt`
  proves that byte is inside the rectangle's bytes. The frame is drawn at its display size.
- A `VideoFrame` from a canvas, an `OffscreenCanvas`, an `ImageBitmap` or an image: the source is drawn
  on a scratch bitmap of its size in Lean's canvas and read back as RGBA (RGBX when `alpha` is
  `discard`); the timestamp is required for these sources (a `TypeError` without it).
- Canvas 2D in dedicated workers: `OffscreenCanvas` and the objects of its context are
  `[Exposed=(Window,Worker)]`; a worker's host keeps its own canvas bitmaps in Lean (`PageCanvas`), so
  the worker scope keeps those names instead of deleting them.

A `VideoFrame` made from bytes with a `visibleRect` keeps its coded size (the standard's text); one
WPT subtest (`copyTo from byte data with non-default visibleRect`) expects the coded size to shrink to
the visible size, and fails here.

## 5. WebCodecs: audio and codecs

`WebCodecs.Audio` (ops 127 to 131):

- "valid AudioDataInit" and the duration (`initCheck`): frames, channels and the sample rate above zero,
  enough bytes; the duration `⌊frames × 10⁶ / rate⌋` computed exactly on the rate's mantissa and exponent
  (the double's bytes, as for a rotation).
- "Compute Copy Element Count" (`plan`): the RangeErrors of plane index, frame offset and frame count;
  the elements copied (one channel to a planar destination, all channels to an interleaved one).
- `copy`: every conversion between the eight `AudioSampleFormat`s. Integer to integer by shifting (exact
  widening; narrowing drops the low bits); integer to `f32` by the scale `2^(bits-1)`, rounded once to
  `f32`; `f32` to integer scaled, rounded to nearest and clamped (NaN is silence); `f32` to `f32` copies
  the bits.
- The PCM decoders (`pcmDecode`): `pcm-u8`, `pcm-s16`, `pcm-s32` and `pcm-f32` output their samples as
  they are (interleaved), `pcm-s24` widened to `s32`, `ulaw` and `alaw` expanded to `s16` by G.711. A
  chunk that is not whole frames is an `EncodingError`. These are the only codecs this engine runs, so
  `Config.check` answers `supported` for an `AudioDecoder` with one of them and for nothing else.

The page glue keeps the decode queue: each `decode` is a control message that decrements the queue,
fires `dequeue`, decodes in Lean and calls `output`; `flush` resolves after the messages before it;
`reset` and `close` drop the messages not yet run and reject pending flushes.


`WebCodecs.Config.check` answers `invalid` (a `TypeError`), `unsupported` or `supported` for the four
codec kinds: the standard's validity rules (an empty codec string, a detached description, zero sizes,
members that must come in pairs) and the registrations' (Opus frame durations, complexity, packet loss,
bit rates). `WebCodecs.Codec.parse` reads the codec string as written: fixed names exactly, `vp09` with
the profile constraints of the VP binding, `avc1` and `avc3` with six hexadecimal digits. No codec is
implemented, so no configuration is supported.

### Options for real decode and encode (for the coordinator; none is started)

No verified video or audio codec in Lean, Coq or F* is known to this work. The realistic routes:

| Route | What | Size and cost | Trust |
|---|---|---|---|
| PCM in Lean | `pcm-u8/s16/s24/s32/f32`, `ulaw`, `alaw` for `AudioDecoder` | about 300 lines, 148 subtests; needs `AudioData` first | proved bounds, table-checked companding |
| FLAC decoder in Lean | lossless, integer only; the format is small (RFC 9639) | about 1,500 lines; bit-exact against the reference vectors | a real candidate for a proved decoder: no floats, MD5 of the output in the stream |
| Guest codecs in BubblePopWASM | reference decoders compiled to Wasm and run as sandboxed guests (the route of record `2026-11-08-media-wasmvm.md`): dav1d (AV1, BSD-2, about 1 MB of Wasm), libvpx (VP8/VP9, BSD-3, about 1.5 MB), libopus (BSD-3, about 300 KB), minimp3 (CC0, about 50 KB), libvorbis/stb_vorbis | decoders only at first; speed is the interpreter's: audio in real time is plausible, video is not until the VM is faster | memory-safe by the VM (the guest can only write its own memory); the codec itself unverified; output bytes are checked by `VideoFrame`/`AudioData` layouts |
| H.264, H.265 | openh264 (BSD-2, decoder and encoder, about 1 MB) as a guest; H.265 has no permissive small decoder (libde265 is LGPL) | patents are the owner's decision, not a technical one | as above |
| Encoders | libvpx, SVT-AV1/rav1e, openh264, libopus as guests | each several MB; far from real time in the VM | as above |

Order suggested by subtests a unit of work: PCM (148), then Opus/Vorbis/MP3/FLAC decode as guests (about
120), then VP8/VP9/AV1 decode as guests (about 250 and the encoder tests that decode their own output).
Encoders (about 600 subtests) last.

## 6. Theorems

Axioms: none beyond `propext`, `Classical.choice`, `Quot.sound`; no `sorry`, `native_decide`,
`unsafe`, `@[implemented_by]`, `partial def`.

**Proved**

| Theorem | Module | Statement |
|---|---|---|
| `mergeOps_nodup`, `ops_nodup` | `PageGl.Idl` | each operation name once in an interface |
| `mergeOps_le` | `PageGl.Idl` | a function's `length` is at most every overload's argument count |
| `webgl2_has_webgl1_consts` | `PageGl.Idl` | every WebGL 1 constant is a WebGL 2 constant with the same value |
| `step_keeps_error` | `PageGl.State` | no command changes a recorded error (first error wins, every command) |
| `step_records` | `PageGl.State` | a command that generates an error on a clear flag records it and leaves the state |
| `getError_clears` | `PageGl.State` | `getError` clears the flag; a second call answers `NO_ERROR` |
| `run_error` | `PageGl.State` | after any command sequence from a clear flag, the flag is the first error generated |
| `pixel_in_image` | `PageGl.State` | every pixel of an image lies inside `imageBytes` (rows padded to the alignment) |
| `checkPixels_fits` | `PageGl.State` | an accepted client buffer holds at least `imageBytes` |
| `ofName?_name`, `ofName?_sound` | `WebCodecs.Format` | pixel format names are read back exactly, and nothing else is |
| `planes_pos` | `WebCodecs.Format` | sub-sampling factors and sample sizes are positive |
| `dropAlpha_noAlpha`, `dropAlpha_planes` | `WebCodecs.Format` | the format without alpha has none; its planes are the first planes (no byte moves) |
| `copyPlan_inBounds` | `WebCodecs.Layout` | every row of every move of an accepted plan is inside the resource and inside `allocationSize`, for every format, size, rectangle and layout |
| `copyPlan_inBounds_swap`, `ofBuffer_inBounds` | `Layout`, `Frame` | the same for the constructor from bytes, against the page's buffer size |
| `parseRotation_range`, `parseRotation_mul90` | `WebCodecs.Frame` | a rotation is 0, 90, 180 or 270; multiples of 90 are kept modulo 360 |
| `addRotations_lt` | `WebCodecs.Frame` | a composed rotation is below 360 |
| `swapRB_involutive`, `swapRB_lt` | `WebCodecs.Convert` | RGBA to BGRA and back is the identity, inside the buffer |
| `nv12_i420_roundtrip`, `i420_nv12_roundtrip`, `nv12Src_lt`, `i420Src_lt` | `WebCodecs.Convert` | I420 to NV12 and back (and the reverse) is the identity, inside the frame |
| `Named.ofName?_name`, `Named.ofName?_sound` | `WebCodecs.Codec` | the 18 fixed codec names are accepted exactly |
| `vp9_profile_depth`, `vp9_profile_chroma`, `parseVp9_valid` | `WebCodecs.Codec` | an accepted VP9 string meets the profile constraints |
| `check_blank`, `check_detached` | `WebCodecs.Config` | an empty codec string or a detached description is invalid for every kind |
| `check_supported_pcm` | `WebCodecs.Config` | a configuration is supported only for an `AudioDecoder` whose codec string names a PCM codec (decoded in Lean) |
| `source_lt`, `byteSrc_lt`, `orient_size` | `WebCodecs.Orient` | every pixel and byte an oriented image copies is inside the source rectangle; the image keeps its size |
| `source_half_involutive`, `source_flip_involutive` | `WebCodecs.Orient` | a half turn twice, and a mirror twice, show every pixel where it was |
| `Format.ofName?_name` | `WebCodecs.Audio` | the eight sample format names are read back |
| `initCheck_refuses` | `WebCodecs.Audio` | an init with no frames, no channels or a rate not above zero is refused |
| `srcIndex_lt` | `WebCodecs.Audio` | every sample a copy reads lies wholly inside the data, planar or interleaved |
| `narrow_widen` | `WebCodecs.Audio` | narrowing a widened integer sample gives it back (u8 ↔ s16 ↔ s32) |
| `ulaw_range`, `alaw_range`, `ulaw_odd`, `alaw_odd` | `WebCodecs.Audio` | all 256 G.711 codes expand into 16 bits; the sign bit only negates (by `decide`) |

**Tested only** (`#guard`, from the WPT cases)

- The page glue (`prelude.js`): that it performs exactly the moves of a plan, converts arguments as Web
  IDL says and calls the state machine for every modelled command. Checked before the cloud runs by
  running the WPT files in Node against the glue and the Lean ops.
- `yuvToRgb` and `toRgb`: the colours of `videoFrame-copyTo-rgb.any.js` within 1; reads use checked
  access (`get!`), their indices are not separately proved in bounds.
- `applyMoves` against the expected bytes of `videoFrame-copyTo.any.js`.
- The format and type table of `texImage2D` (a reduced table: the pairs of WebGL 1, the types of WebGL 2).
- `avc1`/`avc3` strings; the VP9 string as text (the theorems are about its fields).

**Open**

- The codec string grammar of `av01`, `hev1` and `hvc1` is not read; `parse` is not proved to accept
  exactly a stated grammar for `vp09` and `avc1` as strings (only for the fixed names).
- No theorem that `exec` generates the error the specification names for each command (it is tested).
- Framebuffer attachments, `clear`/`readPixels` pixels held by Lean, texture contents: not modelled.
- Primaries and transfer conversion (sRGB, Display P3, BT.2020 PQ/HLG); 10 and 12-bit conversion.
- `ImageDecoder`, serialization and transfer of frames, chunks and `AudioData`: not connected yet.
- The values of float sample conversions (`ofFloat`, `toFloat`) are tested against the WPT templates,
  not proved; their reads are by checked access.
- A Display P3 destination for `copyTo` and `getImageData`: refused / not converted.
- Risk flags: none taken. The conversion arithmetic is exact integer arithmetic; no hash, no crypto.

## 7. Performance

A page that names no WebGL or WebCodecs interface pays for 16 small classes in the prelude and two
lists of names; the two context interfaces and the whole WebCodecs section are made on first use (the
section is text until then). A WebGL call that the state machine does not model goes to the drawing path
with one argument conversion; a modelled call is one `web_api` import. No timing was measured in this
work (no local engine build): the shader gallery's frame cost must be measured before and after on the
next macOS build (`shader_gallery_bench.ts`).

## 8. Measured

See the table in the night report and the coordination log; filled in when the cloud check of the
branch ends.
