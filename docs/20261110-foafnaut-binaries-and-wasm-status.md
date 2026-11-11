# Foafnaut: the binaries and the Wasm build, in answer to the five questions

Source: https://github.com/danbri/factoidal-core (branch `main`).
Build CI and releases: https://github.com/danbri/factoidal-builds

One engine, written in Lean 4, in three forms: a native command-line binary, a native shared
library inside a desktop app, and one WebAssembly module. The same Lean source and the same
C ABI in all three. Experimental code, one author with AI coding tools, no users yet.

## 0. What is built

| Artifact | Made by | What it is |
|---|---|---|
| `web-render-native` (46 MB, Linux x86_64 or macOS) | `labs/demos/foafnaut/build-web-render.sh --native` | the engine as a command: a page file in, layout and draw data out. No window, no GPU. Used for measurement and tests |
| `libweb-render.dylib` | the same script, on macOS | the engine as a shared library |
| the desktop app (macOS arm64) | `labs/demos/foafnaut/build-executables.sh` | `deno compile` of the host program, with the library, the pages and a Cocoa window library; one executable |
| `web-render.wasm` + `web-render.mjs` | `build-web-render.sh --wasm` | the engine as one Wasm module, for a browser or Deno |
| Textnaut | `labs/demos/foafnaut/textnaut/` | the same engine drawn in a text terminal |

Releases come from the builds repository, one release for each source commit and artifact set
(`foafnaut-darwin-arm64`, `foafnaut-web`); every file has a sha256 in `build-info.json`.
Linux: the Factoidal library and command-line set is released (`linux-x86_64`). The browser
engine builds on Linux as the command-line binary above; that binary and a Linux engine library
are in no release. No Linux desktop app exists (the window library is Cocoa). No Windows build.

## 1. Lake configuration and FFI boundaries

Lake file: https://github.com/danbri/factoidal-core/blob/main/formal/lean4/lakefile.lean
(Lean 4.33.1, no Mathlib). The engine's lab modules are compiled by the build script, which
calls `lean -c` and the C compiler itself, so that one script can target native and wasm32:
https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/build-web-render.sh

**Native build:** Lean to C, then `leanc -O3 -DNDEBUG`, linked with Lean's runtime.

**Wasm build:** Lean to C, then Emscripten's `emcc`, against a Lean runtime and core library
that we rebuild for wasm32 with no GMP:

```sh
emcc -O3 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions -I "$RUNTIME/wasm-include" \
     -I "$TOOLCHAIN/include" -c "$file" -o "$BUILD/obj-wasm/core/$name.o"
```

Lean does not support 32-bit Wasm upstream. Our notes on the faults and workarounds (a
`Nat` literal above 2^31 is a heap object there; the silent `leanir` failure; an abort with
`-DNDEBUG` missing): `skills/lean4-wasm-export/SKILL.md` and
`docs/designissues/2026-11-09-lean-upstream-wasm32.md`.

**C linked into the engine (84 `@[extern]` declarations in the library):**

- HACL\* (F\*-verified C, vendored unmodified) for every cryptographic primitive. The same C
  compiles to native and to Wasm. Shims:
  https://github.com/danbri/factoidal-core/tree/main/formal/lean4/ffi
- Small byte primitives (8-byte load and store), each with a Lean reference body and a
  differential test on native and wasm32.
- The C ABI of the engine itself: `web_render_shim.c` (strings and byte buffers in and out).

**Not linked:** SDL2, Raylib, Cairo, Skia, FreeType, HarfBuzz, libcurl, OpenSSL, gumbo,
html5ever, any JavaScript engine.

**Window, event loop, rasterisation:**

- Desktop app: the host is a Deno program. It loads the engine library through Deno's FFI and
  one Objective-C file of 645 lines for a Cocoa window and an input queue:
  https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/native_window.m
- Lean gives each frame as data: a scene (floats and tile words), one WGSL shader and a render
  plan. The host runs the plan on WebGPU (Deno's on the desktop, the browser's for the Wasm
  build). The host holds no layout or paint logic.
- With no GPU, a rasteriser in Lean gives RGBA bytes
  (https://github.com/danbri/factoidal-core/blob/main/labs/demos/foafnaut/SVGRaster.lean).
  `web-render-native` uses no GPU at all.
- The event loop for page scripts (timers, tasks, events) is Lean (`WebEventLoop.lean`). The
  host only forwards input and asks for frames.

**HTTPS and sockets:** none in the engine, in any build. The host fetches bytes (`fetch` of
Deno or of the browser) and passes them in. Page scripts have no network yet:
https://github.com/danbri/factoidal-core/issues/374 (open).

## 2. DOM and parser (the same in every build)

An arena, not a recursive inductive: a node is a record, the document is an array, links are
indices. https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/DOM/Arena.lean

```lean
structure Node where
  type : NodeType := .element      -- document | doctype | fragment | element | text | ...
  ns : Option String := none
  lname : String := ""
  attrs : Array Attr := #[]
  data : String := ""
  parent : Option NodeId := none
  kids : Array NodeId := #[]
  ...
structure Dom where
  nodes : Array Node := #[]
```

HTML parser: hand-written in Lean after the WHATWG algorithm, a state machine in a state monad
with fuel (`HTML/Tokenizer.lean`, `HTML/TreeBuilder.lean`, entry `parseHtml`). No combinators,
no FFI. Measured with html5lib-tests; 10 tree-construction and 6 tokenizer failures were open
at the last status note. CSS parsing, cascade and computed values are Lean
(`Rendering/Style.lean`, `ComputedValues.lean`).

## 3. Layout and text

https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/Rendering/Layout.lean

```lean
structure Box where
  source : Nat      -- the DOM node
  x : Float
  y : Float
  width : Float
  height : Float

def block (dom : Dom) (styles : Array Computed) (font : FontProfile) (embedding : Embedding) ...
def inlineLayout (font : FontProfile) (items0 : Array Inline) (x y available : Float) ...
```

`block` walks the DOM with the computed styles and gives boxes, glyph runs and scene nodes;
tables are in `TableLayout.lean`. No separate persistent box tree yet.

Fonts are read and shaped in Lean (`Rendering/Sfnt*.lean`): TrueType and CFF outlines, `cmap`,
`kern`, GSUB, GPOS, Arabic joining, mark positioning, COLR colour glyphs; bidi and line
breaking from Unicode data in Lean. The font file's bytes are an input; the binaries carry no
font library. Hinting is not run.

Measured on the native binary (Linux VM, 2026-11-09): start 0.11 s; first compile of a demo
page 40 to 105 ms; one frame of the status page on a kept layout about 280 M instructions.

## 4. JavaScript

Both builds run page scripts inside the engine. No host JavaScript engine runs a page script,
also in the Wasm build inside a browser.

- **BubblePopJS**, written in Lean
  (https://github.com/danbri/factoidal-core/tree/main/formal/lean4/L4Factoidal/JS). Also a
  standalone binary: `lake exe leanjs run FILE`. Test262, the 6,301 files of `test/language`
  in the tree: 5,633 pass, 664 fail, 4 skip. Six real-world library workloads: 6 of 6 right
  answers, about 8 times QuickJS-NG's run time (geometric mean, 2026-11-10).
- **QuickJS-NG compiled to Wasm, run inside WasmVM**, our WebAssembly engine in Lean
  (https://github.com/danbri/factoidal-core/tree/main/formal/lean4/L4Factoidal/WasmVM).
  In the Wasm build this is Wasm interpreted by Lean compiled to Wasm; it is slow, and it is
  the same code path as native. Official WebAssembly spec tests on the native binary: 61,698
  pass, 0 fail, 3,655 not run (memory64, text-format modules, rAbout 740 theorems under the browser's directories. In `formal/lean4` (the library: DOM, HTML,
CSS, layout, fonts, the JavaScript and WebAssembly engines) these are banned and checked by CI:
`sorry`, user axioms, `native_decide`, `unsafe`, `@[implemented_by]`, new `partial def`.

**The ban does not cover the engine's host modules.** `labs/demos/foafnaut/*.lean` (the
document operations, script sessions and caches that the C ABI calls) have 29 `unsafe`
definitions and 29 `@[implemented_by]` attributes, 21 of each in `WebDocument.lean`. They keep
state between calls in mutable cells that functions of a pure type read. A theorem about a
caller of one of these is about an opaque declaration, not about the compiled code. The audit
now counts them with a baseline that must not go up:
https://github.com/danbri/factoidal-core/issues/390 (open; replacement by explicit state).
Corrected 2026-11-10; the first form of this note gave the ban with no scope.. Proofs and invariants

About 740 theorems under the browser's directories. Banned and checked by CI: `sorry`, user
axioms, `native_decide`, `unsafe`, `@[implemented_by]`, new `partial def`.

- Termination: every parser and interpreter is a total function on fuel or input size.
- DOM mutation refuses a cycle (DOM §4.2.3):
  ```lean
  theorem appendChild_self (d : Dom) (n : NodeId) : d.appendChild n n = (d, .error .hierarchyRequest)
  ```
  https://github.com/danbri/factoidal-core/blob/main/formal/lean4/L4Factoidal/DOM/Theorems.lean
- Fast form equals reference form (`@[csimp]`), which matters for the binaries: the compiled
  code is the fast form. Example: `Float.ofNat` through a machine word, proved equal to core's
  definition; it took 12 to 23% off first compile in the native engine with byte-identical output.
- WasmVM steps related to the official WebAssembly 3.0 semantics (SpecTec translated to Lean)
  for part of the instruction set.
- Rendering: clipped content is inside its padding box; link regions are complete; the CPU
  rasteriser's fast form equals its reference form.
- Not proved: layout against CSS, the HTML parser against WHATWG, anything end to end.
- A theorem about the Lean source says nothing about the C compiler, Emscripten, Lean's runtime
  or the wasm32 port of that runtime. Those are trusted, and the wasm32 port is ours.

How we read theorems: https://github.com/danbri/factoidal-core/blob/main/docs/designissues/2026-11-10-theorems-as-contributions.md

## Direct answer: external C libraries for the window and the network

None in the engine. Window: Cocoa through one Objective-C file, in the desktop host. GPU:
WebGPU in the host. Network: the host's `fetch`. C inside the Lean binaries: HACL\* and a few
byte and file primitives.

## Limits of this answer

- The desktop app exists for macOS arm64 only and was not run for this note; the native
  engine binary and the JavaScript and WebAssembly binaries were built and measured on Linux.
- The Wasm build was not rebuilt for this note (this machine has no wasm32 Lean runtime); its
  facts are from the build script and the build repository's releases.
- On 2026-11-10 one page (Spinal Tap) fails on the GPU path of the Wasm build and works on
  the CPU path; the cause is not yet known.
- Counts are from a text search of the tree on 2026-11-10.
