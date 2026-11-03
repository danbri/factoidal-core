# FOAFNaut macOS build and Solving package, 2026-11-02

This record covers the local build of the small FOAFNaut WASM engines and
macOS ARM64 package from the current working tree. Generated engines,
executables and runtime caches stay under the ignored lab `.build/` directory.

## Retained SVG tree and pathLength regression

The fresh source build exposed a failing `SVGPathLengthTests.lean` assertion.
The test compared complete JSON artifacts for an SVG line with inherited dash
units inside a group and an equivalent line with explicit units at the root.
The new retained inspector `tree` correctly preserves that source group.

Native compilation of both inputs showed exactly one differing top-level
field: `tree`. The grouped document has an anonymous identity-transform group
with one line paint child; the other document has the line paint node directly.
The fields `abi`, `profile`, `binding`, `width`, `height`, `primitiveCount`,
`data`, `wgsl` and `checks` were equal. The renderer still consumes the same
complete packed data, shader and CPU reference checks in both cases.

The regression helper now parses the artifact JSON and removes only `tree`
before comparing every other field. It requires the tree field to exist and
adds exact group and leaf tree assertions for this inheritance case. The
focused source regression passed. No SVG parser or graphics semantics changed.

The first real SVG WASM link then exposed an existing broad `Std.Tactic`
import in `SVG.lean`: its generated initializer referenced
`initialize_Std_Tactic`, outside the small runtime cache closure. Removing the
unused umbrella import keeps the same `simp`/`omega` proofs from the existing
imports. This repairs the runtime import closure; no linker stub or rendering
change is intended. The standard build rechecks SVG, its Solving importers and
all source guards after this repair.

The first complete patched-runtime Deno run passed 70 tests and exposed three
stale SVG expectations. The coordinate test still refused `20%`, although the
specified percentage axis resolves it to 12.8 in a 64-pixel viewport. The two
analytic shape tests used one pixel-center sample, while the source specifies
four quarter-pixel samples. At a capsule edge, two covered quarter points give
128 gray; at the measured affine annulus edge, three give 64 gray. The tests
now derive membership independently at all four explicit sample positions,
average black-on-white coverage, and retain exact interior/exterior assertions.
All eight invalid/unsupported coordinate refusals remain. No tolerance changed.

After these assertions passed, the same affine test reached its existing
10,000-transformed-circle storage-budget case. The 400,069-character document
overflowed the WASM call stack before the expected explicit storage refusal.
A separate `--profiling-funcs` link identified repeated
`NativeSVG.DisplayNode.lowerList` frames. The declarative sibling traversal
used one frame per element.

The reference mutual definitions remain unchanged. New total node/list twins
use sibling folds and reverse accumulation, with recursive calls only for
group depth (the parser bounds that depth at 32). Six kernel-checked `csimp`
theorems preserve the exact primitive list, transform/group accumulation,
paint count and inspector node count. Paired fast node and list functions
avoid relying on `csimp` to rewrite calls within the old mutual blocks.
The lowering equalities use only `propext`, `Classical.choice` and `Quot.sound`;
the count equalities use only `propext` and `Quot.sound`.

Generated C confirms that parser counting, root lowering and JSON inspection
reach the fast twins. The fast group sibling loop advances with `goto _start`;
old calls remain only in the retained reference functions and their wrappers.
The WASM regression keeps the 10,000 transformed-circle explicit refusal and
adds admitted flat and grouped 10,000-rectangle controls, with exact 200,008-float
data and identical render payloads but distinct retained trees.

## Static Solving showcase in the native package

`build-executables.sh` generates `Solving Showcase.svg` by running
`SolvingArtifact.lean`, which requires the existing `certifyScene` result before
calling the SVG backend. The package records the generator's source hash and
the resulting SVG hash. The launcher opens an adjacent packaged SVG before
attempting source compilation. An extracted package therefore needs no Lean
installation for this static showcase.

The packaging script probes this path by copying only the launcher and SVG to
a directory with spaces, removing Lean from `PATH`, and recording the exact
filename passed to a stub `open`. Source checkouts retain scene compilation
under the pinned `formal/lean4` toolchain. This showcase uses the browser SVG
backend; its certification does not establish native WebGPU execution.

## Runtime cache provenance

The cold runtime build encountered restricted DNS in nested Git fetches. The
build instead uses the official Factoidal Builds runtime cache from commit
`94e6907c760a19008a3fe9cc1e042369bd8e1c1b`:

<https://raw.githubusercontent.com/danbri/factoidal-builds/94e6907c760a19008a3fe9cc1e042369bd8e1c1b/l4wasm-work-cache-v4.33.1.tar.gz>

Its SHA-256 is
`485feb38a59a4ffa676ec3e8581dd02b2425c4091320a42f909aac6e0c1ccec3`,
matching the official checksum file. The archive contains `Init.o`,
`object.o`, `mimalloc_static.o` and Lean 4.33.1 headers. The project build uses
the existing `--runtime-cache` option and regenerates the current project C;
no prebuilt project executable or WASM engine is installed by hand.

Matching that checksum and version did not establish the runtime patch. The
archive's clean Lean source commit is `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`,
but `object.cpp:2191` still used `lean_box_uint32(0)` for the list terminator.
Its `object.o` was dated August 24, before the required wasm32 patch. The first
fresh Deno tests failed on one-person Turtle and FOAF live initialization with
`std::bad_alloc` after requests for 3,263,201,280 and 3,263,205,376 bytes.

The standard runtime-only build applied its existing step 1b source patch and
rebuilt the runtime object. It reused 838 cached core objects and filled 26
missing timestamp modules. The object SHA-256 changed from
`57d105caa36628a1fcd4f2c77a07c04667c3561440baa31cf78120c909726075` to
`f8c0f3c611b6b0425edad7f126ed12a6d8e2704ce032e226b657e90c8783b456`.
The patched `object.cpp` SHA-256 is
`fdf172d40a32cd87aba2feb30668124dc609568718cc787f3d3f974aa62c0767`.

The runtime builder now records a versioned source-and-object hash witness
only after successful compilation. A missing or mismatched witness invalidates
only `object.o`. The lab requires the patch marker and matching hashes before
linking; missing source or a legacy cache invokes the standard runtime repair.
The package carries the witness. Thus a restored cache cannot bypass the
required patch merely because it contains the expected filenames and headers.

Emscripten also attempted to lock its system cache under Homebrew, outside the
writable worktree. The successful build command uses a local `EM_CACHE` seeded
from the installed pinned toolchain cache. Packaging uses a local `DENO_DIR`
and the official Deno 2.9.4 ARM64 `denort` runtime through `DENORT_BIN`, without
changing global toolchain configuration. The runtime ZIP's SHA-256
`81bced8c72f5a1a64d6b1d85ac96aabef5fa559712ac54d2cdfbaa80002246ec`
matches Deno's official per-asset checksum.

## Final local validation

The standard small-engine build passed all selected Lean modules, proofs,
native guards and seven real WASM links. The complete local suite passed
74 Deno tests and 12 C coordinate checks. The focused wide-tree controls passed
in actual WASM, including the explicit storage refusal and both admitted
10,000-rectangle scenes. This is the isolated lab build, not a full repository
`lake build` claim.

The standard package script compiled three real Mach-O ARM64 executables and
the Cocoa dylib into `labs/demos/foafnaut/.build/dist-20261102`. Its static SVG
launcher passed relocation with spaces and no Lean on `PATH`. A relocated copy
then passed all four compiled UI engine modes, graph/still/gallery artifact
emission, checked FOAF SVG export and compiled SVG parsing of that export
(292 primitives, 39,452 floats). The relocated dylib loaded from its adjacent
path with `mainThread=true` and granted FFI permission. Generated SVG files
also passed an independent XML well-formedness check.

Actual GPU requests were made through all three compiled rendering paths.
Each returned an unavailable adapter (exit 2); no image was written. These
CPU, loader and artifact checks do not establish native GPU rendering or
presentation. Browser GPU evidence is recorded separately by the browser
harness worker.

The build used source commit `4ca2bb7d3549036b0116f93edcf037c2f51279a7`
plus the preserved working-tree changes. The package carries exact source
hashes, tool versions and the repaired runtime witness. Full commands, logs,
dirty source hashes, engine hashes and compiled relocation evidence are under
`/tmp/factoidal-svg-20261102-*`; coordination status is
`/tmp/factoidal-svg-build-status.md`. Generated binaries and caches remain
ignored build products.

The local archive is `.build/foafnaut-darwin-arm64-20261102.tar.gz` under the
lab (89,626,296 bytes), SHA-256
`6a7062990dbbbfb23e4078874f878c6f7180ccd5d2fa8bf3eaf9c6179120bcf2`.
It was extracted again and every packaged checksum passed. Packaged source
checksums also match the current source inputs. Final SVG engine SHA-256:
`cc304ebc359a29da36657fbe462f983b3a32cfeb27a9900b016b915ccbaa03fb`.
