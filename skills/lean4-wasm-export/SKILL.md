---
name: lean4-wasm-export
description: Compile the Lean 4 port (formal/lean4, library L4Factoidal) to a single WebAssembly module that runs in the browser, Node and Deno — the toolchain route chosen and why, the exact build commands, the Lean runtime flags, the C ABI and its memory rules, how to add an export, and the traps that produce a silently-wrong or silently-aborting artifact. Use when adding or changing a wasm export, when rebuilding after a Lean change, when the wasm aborts or returns nothing, when a hub post needs the Lean engine, or when evaluating a different C-to-wasm toolchain.
---

# Lean 4 → WebAssembly

Issue: https://github.com/danbri/factoidal/issues/466
Design decision (owner-approved 2026-08-22):
`docs/designissues/2026-08-22-lean4-external-dependencies.md` §4.

## What exists

For stateful transport adapters, test the host's lifecycle independently of
the protocol engine, then replay through the rebuilt Wasm artifact. An empty
`send`/`route` answer says nothing about input consumption: export the actual
residual buffer size from Lean and require it in the host. Exercise exceptional
feed cleanup, startup failures, package subpath imports, concurrent persistence
and shutdown with outstanding IO. The 2026-10-22 XMPP integration found leaks,
incorrect buffer accounting and overlapping roster writes that the happy-path
TCP suite did not test. Evidence and limits:
[XMPP PR3 integration](../../docs/20261022-xmpp-pr3-integration.md).

| Path | Role |
|---|---|
| `formal/lean4/Wasm/Abi.lean` | JSON string-in / string-out ABI + a phase-1 JSON reader/writer shim |
| `formal/lean4/Wasm/Exports.lean` | the `@[export]` declarations (the C symbol names) of the full module |
| `formal/lean4/Wasm/CoreDispatch.lean`, `Wasm/CoreExports.lean` | the core module (`l4factoidal-core.wasm`, issue 713 stage 4): the dispatch table of the core subset and the same C symbols over it |
| `formal/lean4/Wasm/CoreDispatchTests.lean` | build-time check that the core and full tables name the same ops and answer core ops alike |
| `tools/wasm-size-profile.py` | bytes of code and data per Lean module or namespace, from the link map |
| `formal/lean4/Wasm/Main.lean` | a NATIVE driver over the same ABI (`lake exe l4wasm-cli`) |
| `formal/lean4/Wasm/l4_shim.c` | the C boundary: init, `char *` ↔ Lean string, ownership |
| `formal/lean4/Wasm/l4_stubs.c` | one stub (`initialize_libuv`) — see "the purity evidence" below |
| `formal/lean4/Wasm/build-wasm.sh` | the whole pipeline, reproducible |
| `docs/web/hub/assets/l4/l4factoidal.wasm` | the module; a build product, not committed since 2026-10-09 (in `.gitignore`; the `web` release set of `danbri/factoidal-builds` carries it) |
| `docs/web/hub/assets/l4/l4factoidal.mjs` | Emscripten's generated glue; a build product, not committed since 2026-10-09 |
| `docs/web/hub/assets/l4/l4factoidal.js` | our ES-module loader (`loadL4()`); source, committed |
| `docs/web/hub/assets/l4/l4factoidal-core.{wasm,mjs,js}` | the core module, its glue, and its loader, which step 8 generates from `l4factoidal.js`; build products |
| `tests/hub/post36_test.mjs` | the gate: cells of hub post 36 + the error paths |

Measured on the first working build (2026-08-22, macOS arm64,
Emscripten 6.0.8, Lean v4.33.1):

| Quantity | Value |
|---|---|
| `l4factoidal.wasm` | 1,432,723 bytes (1.4 MB) |
| Emscripten glue `l4factoidal.mjs` | 61,224 bytes |
| Module instantiation + Lean init, Node | ~41 ms |
| Module instantiation + Lean init, Deno | ~75 ms |
| One 2-pattern BGP over a 4-triple graph | 2.7 ms (Node), 3.7 ms (Deno) |

Gate on that build: `node --test tests/hub/post36_test.mjs
tests/hub/fn_surface_parity_test.mjs` — 10 pass, 0 fail (out of 10).

## The problem, stated exactly

Lean's compiler emits C. Linking that C needs two things the elan
toolchain ships **only as native binaries**:

1. Lean's C++ runtime (`libleanrt`), and
2. Lean's compiled core library (`libInit.a`) — every `List`, `String`
   and `Option` function your code calls.

There is no `wasm32` release asset for Lean (checked: the v4.33.1
release publishes darwin/linux/windows only). So both must be rebuilt.

## The route chosen, and the three that were not

**Chosen: regenerate the core library's C with the native `lean`, then
Emscripten for everything.**

The insight that makes this cheap: `lean -R <srcdir> -c out.c <mod>.lean`
re-emits a module's C in about **one second**, because the toolchain
ships the core library's *sources* (`<toolchain>/src/lean/Init/**`) and
every import is already a compiled `.olean`. So "rebuild the Lean
standard library" is ~630 one-second jobs — about four minutes at
`-P 8` — not a stage build. Nothing needs to *elaborate* Lean inside the
browser; it only needs to *run* already-compiled Lean.

Rejected, with reasons:

- **lean4's own CMake Emscripten build** (`emcmake cmake`,
  `-DLEAN_EMSCRIPTEN`). This is the upstream-supported route and it
  works, but it builds the Lean *compiler* (`libleancpp`, the whole C++
  frontend) and cross-builds the stdlib through it, plus libuv as an
  ExternalProject. Hours of build for a capability we do not need
  (elaboration in the browser). Its flags were still worth reading —
  `-fwasm-exceptions` and the GMP-free option came from there.
- **`leanir`, the toolchain's IR-to-C tool.** Looked ideal: the
  toolchain ships per-module `.ir` files (252 KB for
  `Init.Data.List.Basic`, so the bodies really are there) and a
  `leanir <setup.json> <out.ir> <out.c>` binary. In practice its
  `setup.json` contract could not be reconstructed: with imports absent,
  with direct imports, and with all 1,114 core modules listed, it
  emitted the same **near-empty** module (3,529 bytes, 3 exports, no
  `l_List_reverse`) and exited 0 — and some modules failed with
  `missing data file for module Init.Grind.ToInt` even though both that
  module's `.olean` and `.ir` were listed. **It fails silently**, which
  is why it is recorded here rather than left for someone to rediscover.
  Setting `isModule: true` (Init uses Lean's new module system — the
  sources begin with `module`) did not change the output.
- **WASI (`wasi-sdk` / `clang --target=wasm32-wasi`) and `zig cc`.** Not
  attempted after Emscripten linked, per the brief's instruction to take
  the route that links first and document the rest. The blocking risk to
  check first if this is revisited: Lean's runtime throws C++ exceptions
  (`runtime/exception.cpp`), and wasi-sdk's libc++ exception support is
  the historic weak point; Emscripten's `-fwasm-exceptions` is
  well-trodden. The upside WASI would buy — no JS glue at all — is
  smaller than it looks here, because the glue is 62 KB and our loader
  already hides it behind one `loadL4()`.

## Build it

```bash
export PATH="$HOME/.elan/bin:$PATH"          # every shell, every time
brew install emscripten libuv                 # libuv: HEADERS only, see below
cd /path/to/factoidal
formal/lean4/Wasm/build-wasm.sh               # work dir defaults to /tmp/l4wasm-build
```

### On Linux (measured 2026-08-26, x86_64 container, from nothing)

The script is portable; only the prerequisite install differs. This is
the whole of it:

```bash
# Lean
curl -sSfL https://elan.lean-lang.org/elan-init.sh -o /tmp/elan-init.sh
sh /tmp/elan-init.sh -y --default-toolchain leanprover/lean4:v4.33.1
export PATH="$HOME/.elan/bin:$PATH"

# Emscripten — the upstream emsdk, NOT a distro package
git clone --depth 1 https://github.com/emscripten-core/emsdk /opt/emsdk
cd /opt/emsdk && ./emsdk install latest && ./emsdk activate latest
source /opt/emsdk/emsdk_env.sh        # every shell, every time

# libuv HEADERS only (step 5 needs uv.h for declarations)
apt-get install -y libuv1-dev

bash formal/lean4/Wasm/build-wasm.sh
```

`./emsdk install latest` gave Emscripten 6.0.8 — the same version the
first working build used, so no version pinning was needed.

Measured costs, so a session can budget rather than guess:

| Step | Cost |
|---|---|
| elan + Lean v4.33.1 | ~2 min, ~2 GB |
| emsdk (clone + install latest) | ~4 min, ~1.7 GB |
| `lake build` (whole L4Factoidal, cold) | ~25 min, 704 jobs |
| `build-wasm.sh` COLD (steps 1–9) | 15 min 36 s |
| `build-wasm.sh` INCREMENTAL (steps 0, 6–9) | 8 min 11 s |

⚠️ **The "disk is the blocker" warning in
`docs/designissues/2026-08-26-cl-ikl-wasm-abi.md` is container-specific,
not a property of the build.** That note measured ~1.8 GB free against
emsdk's ~1.7 GB and planned a `git repack` around it. A container
started fresh for this work had 25 GB free and needed no reclamation at
all. Measure `df -h` in YOUR container before spending time on
repacking — the toolchains together came to about 4 GB.

**The build is byte-reproducible on a fixed toolchain.** Running
`build-wasm.sh` twice over the same source produced the identical
`l4factoidal.wasm` (sha256 `91fb323e…`, 4,348,311 bytes) — `git status`
showed the wasm unmodified after the second run. So an unexpected sha
change after a rebuild is a real input change, not link nondeterminism;
chase it rather than shrugging.

**Run it from any directory — but only since 2026-10-22.** Step 3 used
to call `lean` through the elan shim, and elan picks the toolchain from
the CURRENT directory's `lean-toolchain`. Run from the repository root
(which has none) it silently used the default toolchain (v4.35.0 on the
machine that paid for this) against v4.33.1 sources: every core module
printed `GEN-FAIL` (the real error, hidden by `2>/dev/null`, was
`incompatible header` on the first `.olean`), `core-c` held one file,
and the failure surfaced only at the link as hundreds of
`undefined symbol: l_List_appendTR___redArg` / `initialize_Init`. The
script now calls `$TOOLCHAIN/bin/lean` directly for the regeneration
and the githash. If a link ever reports an undefined core symbol again,
check `core C files:` in step 3's output before anything else.

Incremental: the script skips a core `.c`/`.o` that already exists, so a
re-run after a change to *our* Lean code only redoes steps 0, 6 and 7
(seconds). To force a clean build, delete the work directory.

Prerequisites and how much they cost:

| Thing | Size | Note |
|---|---|---|
| Emscripten | ~919 MB (`brew install emscripten`) | pulls its own node |
| lean4 source, sparse+blobless | ~3.6 MB | `src/runtime`, `src/include`, `src/util` |
| mimalloc, shallow clone at `v2.2.7` | ~6.8 MB | `src/static.c` only is compiled |
| generated core C | ~32 MB | in the work dir |
| core wasm objects | ~17 MB | in the work dir |

### Trap: `tools/ensure-test-env.sh` after a local wasm build replaces it

`tools/ensure-test-env.sh` calls `tools/fetch-builds.sh`, which installs the
newest `danbri/factoidal-builds` release into `npm/factoidal/l4-assets/` and
`docs/web/hub/assets/l4/`. Run after `build-wasm.sh`, it silently replaces the
module you just built with the release's older one, and every Node test then
runs the old engine. (2026-10-27: a new op worked, `ensure-test-env.sh` ran
to fetch test fixtures, and the next run of `lws-serve --authz` failed with
"member issuer is required" from the old wasm; the npm suite had already
passed once more against the old module. Cost: one wasm rebuild, 8 minutes.)
Rule: run `ensure-test-env.sh` BEFORE `build-wasm.sh`, and before a test run
check that `sha256sum npm/factoidal/l4-assets/l4factoidal.wasm` equals the
digest step 9 printed.

## What the build actually does

0. `lake build l4wasm` — also writes our modules' C into `.lake/build/ir/`.
1. `git clone --filter=blob:none --sparse --depth 1 --branch <tag>` of
   lean4, then
   `git sparse-checkout set src/runtime src/include src/util`
   (`src/util` because `runtime/interrupt.cpp` includes `util/io.h`).
   Only ~3.6 MB is ever downloaded. **Do not clone the full tree** — it
   is large enough to matter on a constrained machine.
2. Write the CMake-generated headers by hand:
   - `lean/config.h` — WITHOUT `LEAN_USE_GMP`, so `runtime/mpz.cpp`
     falls back to `runtime/mpn.cpp`; **this is what makes the artifact
     GMP-free**, one of the owner's selection criteria. And WITH
     `LEAN_MIMALLOC`, which is mandatory — see "the mimalloc bug".
   - `lean/mimalloc.h` — copied from the mimalloc checkout (`lean.h`
     includes it under that path).
   - `lean/version.h` — copied from the toolchain.
   - `githash.h` — `#define LEAN_GITHASH "$(lean --githash)"`.
3. Regenerate the core library's C (~631 modules, `-P 8`).
4. Compile that C to wasm objects.
5. Compile Lean's runtime `.cpp` to wasm objects (24 of the 34 files)
   plus mimalloc's `static.c`.
6. Compile our library's C (EXCEPT `Wasm/Main.c`), `l4_shim.c` (twice: once
   per module initialiser, `-DL4_INIT_MODULE`) and `l4_stubs.c`. Since
   2026-10-10 this step is incremental (an object is recompiled when its
   `.c` is newer) and parallel (`L4_WASM_JOBS`, default 4); it deleted and
   recompiled all ~650 objects one at a time before, about seven minutes.
7. `em++` link, twice: `l4factoidal.wasm` from `Wasm_Exports.o` and
   `l4factoidal-core.wasm` from `Wasm_CoreExports.o` (the two define the same
   C symbols, so each link leaves the other out), each with `--Map` and the
   size tables `$WORK/<module>.size.md` and `.size-modules.md`.

## The flags, and why each one is load-bearing

```
-O3 -DNDEBUG -DLEAN_EMSCRIPTEN -fwasm-exceptions
```

- **`-O3 -DNDEBUG`** are the flags Lake passes `leanc` natively; match
  them so the wasm build is the configuration Lean actually supports.
  They are NOT, however, the fix for the allocator abort below — see
  "the mimalloc bug", and see the misdiagnosis warning there.
- **`-fwasm-exceptions`**: Lean's runtime throws. Native wasm exception
  handling needs Chrome 95+, Firefox 131+, Safari 18.4+, Node 18+. Same
  choice lean4's CMake makes. `-fexceptions` (JS-based) is the fallback
  if an older browser must be supported; it is larger and slower.
- **NO `-pthread`**, deliberately, even though lean4's own Emscripten
  build uses it. A pthread build needs `SharedArrayBuffer`, which needs
  COOP/COEP response headers, which **GitHub Pages does not send** — so
  the hub demo would be dead on arrival. Safe here because the shim
  calls `lean_initialize_runtime_module()`, not the full
  `lean_initialize()`, so no Lean task-manager thread is ever spawned.
- **`em++`, not `emcc`, for the LINK step.** The C driver does not link
  libc++, and Lean's runtime is C++. Symptom of getting this wrong: a
  wall of undefined `std::__2::…`, `__cxa_throw`, `typeinfo for …`.
- **`-std=c++20`** for the runtime `.cpp` only: `runtime/object.cpp`
  uses `std::memory_order::relaxed` and `std::bit_cast`. C++17 fails.

Runtime files deliberately NOT compiled: `libuv.cpp`, `uv/*.cpp`,
`openssl.cpp`. `uv.h` is still needed on the include path because
`runtime/io.cpp` includes it — **declarations only**; no libuv code is
linked.

### The mimalloc bug — the one that cost the most

**`LEAN_MIMALLOC` must be defined and mimalloc must be linked.** It
looks optional (it is a CMake `option(USE_MIMALLOC ... ON)`) and the
obvious wasm instinct is to drop it. Dropping it produces a module that
passes every happy-path test and then dies.

The defect is in Lean's own non-mimalloc path, in `lean.h` and
`runtime/object.cpp`:

```c
/* lean.h — allocate: returns a pointer 8 bytes INTO the block,
   with the size stashed in the word in front. */
void * mem = malloc(sizeof(size_t) + sz);
*(size_t*)mem = sz;
return (lean_object*)((size_t*)mem + 1);

/* lean.h — lean_free_small_object: correctly backs up first. */
size_t* ptr = (size_t*)o - 1;
free_sized(ptr, *ptr + sizeof(size_t));

/* object.cpp — lean_free_object (arrays, STRINGS, closures):
   frees the UNADJUSTED pointer. */
static inline void lean_dealloc(lean_object * o, size_t sz) { free_sized(o, sz); }
```

Under mimalloc both paths agree, so no shipped Lean build ever executes
the broken one — which is why this is invisible upstream and why you
will not find it in an issue tracker.

How it presented here, and why it was nearly misdiagnosed:

| Build | Symptom |
|---|---|
| no mimalloc, no `NDEBUG` | `LEAN ASSERTION VIOLATION … i < lean_ctor_num_objs(o)` at `lean.h:779` |
| no mimalloc, `-DNDEBUG` | `RuntimeError: memory access out of bounds` |
| mimalloc | correct |

The first symptom points at `lean_ctor_get` and invites the conclusion
"assertions are on, add `-DNDEBUG`". Adding `NDEBUG` changed the message
and nothing else — **it silenced the reporter, not the bug**. Adding
`-O0` did not help either, ruling out the optimiser. What actually
located it was an `-O1 -g2 -sASSERTIONS=2` build, whose stack named the
real path:

```
bgpQuery -> lean_dec_ref_cold -> lean_del_core_other -> free_sized -> abort
```

An abort inside `free_sized` is an allocator complaint, not a logic
error; from there the `#ifdef LEAN_MIMALLOC` asymmetry is two greps
away. **Method note worth keeping: when a wasm module traps, build a
`-g2 -sASSERTIONS=2` variant and read the stack before changing any
flag.** Guessing at flags cost two full rebuild cycles here.

The bisect that made the trap tractable is also worth copying: run each
input in a FRESH module instance (a separate process), because one trap
poisons the instance and hides every later case. That is what showed
*every* decode error working and *only* the JSON-parse failures
trapping — which is what narrowed it to a string being freed.

mimalloc is cloned at the version lean4 pins (`v2.2.7`) and
`src/static.c` compiles for wasm32 with no patches:

```bash
emcc -O3 -DNDEBUG -DMI_SECURE=0 -Wno-unused-function \
     -I mimalloc/include -c mimalloc/src/static.c -o mimalloc_static.o
```

Cost of adding it: ~50 KB of wasm.

### Do not link `Wasm/Main.c`

Step 6 globs `.lake/build/ir/**/*.c`, which includes `Wasm/Main.c` — the
NATIVE CLI driver. It defines `main` and references `lean_setup_args`.
The release link dead-strips it, so the mistake is invisible at `-O3`;
the `-O1` debug link is what surfaced it as an undefined symbol. The
build script skips it explicitly.

### The purity evidence

After excluding those files, `wasm-ld` reported **exactly one** undefined
symbol: `initialize_libuv`. That is the whole of `l4_stubs.c`. The
smallness of that list is the measured evidence that the exported ABI
really is a pure computation — nothing reachable from the exports
touches Lean's IO, socket, DNS or task layers. If that list ever grows,
something impure got exported; treat a new stub as a design question,
not a build fix.

### The wall clock (NOW(), 2026-10-10)

The module reads the wall clock in one place: `Wasm/Ops/Clock.lean`, for
SPARQL `NOW()` (https://github.com/danbri/factoidal/issues/743). It uses the
toolchain's own `Std.Time.Timestamp.now`, whose C symbol
`lean_get_current_time` is in the runtime's `io.cpp` (already built in step 5,
over `std::chrono::system_clock`; Emscripten serves it from the host's clock).
The one `Std.Time` module Lean code imports is `Std.Time.DateTime.Timestamp`,
and its module initialiser chains through 26 `Std.Time` modules. Step 3 does
not regenerate `Std/Time` as a directory (most of it reaches libuv); it
generates exactly those 26, listed in `STD_TIME_MODULES` in `build-wasm.sh`.
Trap: a module missing from that list is an undefined `initialize_Std_Time_*`
symbol at the link in step 7, and a toolchain bump can change the closure
(recompute it from the `import` lines of `Std/Time/DateTime/Timestamp.lean`).

Trap: never write `import Std` (the whole package) in a module the wasm
links. Import the `Std.Data.*` module you use. `import Std` makes the
module's initialiser call `initialize_Std`, which step 3 does not generate,
and it puts `Std.Http` in scope, so the compiler reuses `Std.Http`
specialisations in OTHER modules that the native build links without
complaint. Cost, 2026-10-11: `SPARQL/OrderedPrefix.lean` (landed from
factoidal-core 906527b) had `import Std` and used nothing from it; the
native build and every native gate passed, and the wasm link failed with
five undefined symbols in `OrderedPrefix.o`, `Solid/Server/Methods.o`,
`Storage/PackStream.o` and `Wasm/Ops/Solid.o`
(https://github.com/danbri/factoidal-builds/actions/runs/38150346038).
Check before a push: `grep -rn '^import Std$' formal/lean4 --include='*.lean'`
prints nothing.
Measured cost (full / core module, `-O3` after `wasm-opt`): +82,436 and +88,885
bytes. The check after a rebuild: `queryDataset` with W3C `functions/now01.rq`
answers `true` through `l4factoidal.js` and through `npm/factoidal`.

Which C entries have the clock: `l4_call_c` (the shim routes it through
`l4_call_io`) and `l4_call_blob_io_c`. The pure `l4_call` and `l4_call_blob_c`
have none, by design; `l4_call_blob_c` stays pure because routing it through
the IO entry would also run the ops that build an out region (`packNext`,
`blobEcho`) and drop that region. The npm package calls `queryHdt` through
`callBlobIO` for this reason, and `tools/wasm-store-query-smoke.mjs` calls
`storeQuery` through it when the engine has it.

A host that must use a pure entry binds `NOW()` by passing the instant as an
optional LAST argument `now`, an `xsd:dateTime` lexical form
(https://github.com/danbri/factoidal/issues/748): `queryDataset` and
`updateDataset` fourth (after the base IRI), `queryRaw` and `storeQuery`
fourth, `queryHdt` second. An empty string, or no argument, means no instant,
and `NOW()` is then an error as before; two- and three-argument hosts do not
change. Any other text must be read by the strict XSD dateTime parser
(`L4Factoidal.SPARQL.isDateTimeLexical`); a text it does not read is an error
envelope (`"not an xsd:dateTime lexical form"`), never a silent "no instant".
The IO entries take no `now`: they read the clock. `l4wasm-cli callpure`
drives the pure `call` natively, and `l4wasm-cli callblob` the pure
`callBlob`; `Wasm/native-smoke.sh` has the cases.

## The C ABI and its memory rules

Lean side (`Wasm/Exports.lean`):

```lean
@[export l4_version]   def l4VersionExport (_ : Unit) : String
@[export l4_bgp_query] def l4BgpQueryExport (dataJson bgpJson : String) : String
```

C prototypes Lean generates:

```c
lean_object *l4_version   (lean_object *unit);
lean_object *l4_bgp_query (lean_object *data_json, lean_object *bgp_json);
```

`l4_version` takes `Unit` rather than being a nullary constant: an
exported nullary Lean definition compiles to a closed thunk that C
cannot portably call. Pass `lean_box(0)`.

The JS-facing surface is `Wasm/l4_shim.c`:

```c
int   l4_init(void);                                    /* idempotent */
char *l4_version_c(void);
char *l4_bgp_query_c(const char *data_json, const char *bgp_json);
char *l4_call_c(const char *op, const char *args_json);
char *l4_call_blob_c(const char *op, const char *args_json,
                     const uint8_t *blob, size_t blob_len);
char *l4_call_blob_io_c(const char *op, const char *args_json,
                        const uint8_t *blob, size_t blob_len,
                        uint8_t **out_ptr, size_t *out_len);
void  l4_free_result(char *p);
void  l4_free_blob(uint8_t *p);
```

### Moving BYTES, not text: `l4_call_blob_c`

The dispatch ABI carries strings, so an op whose input is block bytes cannot
use it: hexadecimal doubles the bytes over the boundary and then costs a
character walk on the way in, and base64 only fixes the first term. Measured on
one 118,769-byte IBK3 block, whole operation, native, mean of 10 runs:
hexadecimal 96 ms with a 242,416-byte args document, blob region 71 ms with a
4,893-byte args document.

`l4_call_blob_c` carries ONE contiguous byte region beside the two strings. The
host allocates it with the already-exported `_malloc`, writes the bytes into
`HEAPU8` with no encoding, and calls; the shim builds a Lean `ByteArray` with
one `lean_alloc_sarray` plus one `memcpy` and calls
`l4_call_blob : String -> String -> ByteArray -> String`
(`Wasm/Dispatch.lean`'s `callBlob`). The op's JSON argument says which bytes
belong to what, as `{"offset","len"}` windows that LEAN bounds-checks.

Two rules that are the point of the shape, not decoration:

* **Lean never receives a host pointer.** The region is copied on entry, so an
  offset past the end is an ordinary `{"ok":false}` refusal rather than a
  memory fault, a stale pointer cannot be expressed, and the host may free its
  buffer the moment the call returns. Do NOT "optimise" this into passing the
  pointer through: that trades a refusal for a fault.
* **The shim moves bytes and never interprets them.** It holds no knowledge of
  any format. A change that gives it any belongs in Lean (iron rule 11's
  spirit).

`L4Wasm.blobOpNames` lists the ops served this way (`storeQuery` today) and the
`ops` reflection reports it as `blobOps`. Every other op delegates to the pure
`call`, envelope for envelope, so a host may route everything through this
entry. The native driver has the same shape:
`lake exe l4wasm-cli callblob <op> <argsJsonFile> <blobFile>`.

Full design record, including the three Shardborough store ops that use it:
[`docs/designissues/2026-09-03-wasm-shardborough-store-ops.md`](../../docs/designissues/2026-09-03-wasm-shardborough-store-ops.md).

### Moving bytes OUT: `l4_call_blob_io_c`

`l4_call_blob_c` carries bytes in and a JSON string out. Packing a store
inside the module needs artifact bytes to come OUT with no encoding, for the
same measured reason (and base64 was refused by the owner, 2026-09-03).

`l4_call_blob_io_c` adds two out parameters. The Lean side is
`l4_call_blob_io : String -> String -> ByteArray -> IO (String x ByteArray)`
(`Wasm/Dispatch.lean`'s `callBlobIO`). The v4.33 code generator erases the IO
world token, so the generated C takes THREE `lean_object *` arguments, the
same as `l4_call_blob`, and returns an IO result object (tag 0 = ok) whose
VALUE is a `Prod`: the shim takes the value with `lean_io_result_take_value`
and reads field 0 (the Lean string) and field 1 (the ByteArray) with
`lean_ctor_get`, which borrows, so both are copied out before the pair is
released. This is checked against the generated `.lake/build/ir/Wasm/Exports.c`
— read that file, never a sketch, when adding an export with a compound
result.

Two buffers, two release entries, on purpose: the envelope goes back to
`l4_free_result`, and the byte region goes back to `l4_free_blob`. They hold
different types, and a caller that mixes them is a bug that must be visible.
On every path with no bytes — an op outside `L4Wasm.blobIoOpNames`, an error
envelope, a failed allocation — `*out_ptr` is NULL and `*out_len` is 0.

The JS binder is `callBlobIO(op, args, blobIn)` in `l4factoidal.js`, returning
`{ envelope, bytes }`. It allocates one 8-byte cell for the two 32-bit out
parameters, reads them with `getValue`, and COPIES the region out of `HEAPU8`
with `slice` before releasing it — never a subarray view, because
`ALLOW_MEMORY_GROWTH` replaces the heap buffer wholesale.

`L4Wasm.blobIoOpNames` lists the ops that build an out region; the `ops`
reflection reports it as `blobIoOps` (a host must look there, not in `ops`,
for an op that answers a region). It holds `blobEcho`, a self
test whose byte `i` is `(i * 7 + 3) mod 256` — the gate is
`tests/store-host/blob-io.mjs`, on Node and on Deno, with a 1,000,000-byte
case that catches truncation — the pack and store-serve ops, the LWS and
Solid step ops, and `datasetQuadsBin` (Dataset iteration as one region,
`L4Factoidal/RDF/QuadsBin.lean`, record
`docs/designissues/2026-10-21-dataset-iteration-region.md`: 1.8 times
faster than the JSON string it replaced, issue
https://github.com/danbri/factoidal/issues/900).

Ownership, in full:

1. Lean's convention for `@[export]`ed functions is **owned arguments**:
   the callee consumes every `lean_object *` you pass. Never `lean_dec`
   an argument you already handed over — that is a double free.
2. The returned `lean_object *` is **owned by the caller**; the shim
   copies its bytes with `strdup` and then `lean_dec`s it.
3. The `char *` returned to JavaScript is **owned by JavaScript** and
   must go back to `l4_free_result` exactly once. The loader does this in
   a `finally`, so a throwing `JSON.parse` cannot leak.
4. Returned strings are NUL-terminated UTF-8. Lean strings contain no
   interior NUL, so this is lossless.
5. Errors never cross as exceptions. A Lean-side failure comes back as
   a JSON document with an `"error"` key; the loader turns that into a
   JS `Error`. A NULL return means allocation failure only.

The module initialiser symbol is
`initialize_<package>_<Module_Path>` — here
`initialize_l4factoidal_Wasm_Exports(uint8_t builtin)`. Note it takes
only `builtin` in Lean 4.33 (no world argument), and it chains through
every import including `Init`. `lean_initialize_runtime_module` and
`lean_io_mark_end_initialization` are **not declared in `lean.h`**;
declare them yourself, as Lean's own generated `main` does.

## Loading it: browser, Node, Deno

One artifact, one loader:

```js
import { loadL4 } from './assets/l4/l4factoidal.js';
const l4 = await loadL4();
l4.version();
l4.bgpQuery(triples, bgp);   // -> SPARQL Query Results JSON
```

`call`, `callBlob` and `callBlobIO` throw an `Error` for `{"ok":false,...}`. Its
message is `l4factoidal: <error>`; since 2026-10-10 its `.envelope` property holds
the whole envelope, because some refusals carry more than `error` (a parse
failure's `line`, `column`, `offset` and `format`;
https://github.com/danbri/factoidal/issues/685). `npm/factoidal/l4-core.js`
re-encodes `.envelope` for `lib/api.js`'s `entryResult`, which is what turns a
positioned failure into a `ParseError`. A new host that needs those members reads
`err.envelope`, not the message text.

The wire entry (`l4_call_c`) goes through `callIO`, so an op that needs state
(a handle table, the document-scope counter behind `parseToDatasetJson`) is served
from `callIO`'s match and the pure `call` keeps the stateless version. Two
calls to `parseToDatasetJson` in one module instance get blank-node scopes
`d0_`, `d1_`, ...; the pure `call` leaves labels as written.

- **Browser** — the glue `fetch`es the sidecar `.wasm` from the same
  origin. No headers needed (no `SharedArrayBuffer`).
- **Node** — the glue reads it with `node:fs`.
- **Deno** — takes the Node path through `node:` compatibility. Needs
  `--allow-read` for a `file:` URL.

**The naming trap.** Emscripten 6 resolves the sidecar from the *glue
file's own basename* (`findWasmBinary()` does
`new URL("l4factoidal.wasm", import.meta.url)`), and it **ignores a
`wasmBinary` option passed to the factory**. So the glue must be named
`l4factoidal.mjs` for it to find `l4factoidal.wasm`. Rename one without
the other and every runtime fails with `ENOENT` / a failed fetch. An
earlier version of the loader read the bytes itself and passed
`wasmBinary` — that silently did nothing.

## Adding a dispatch op: where the 2026-10-10 ops live

The format, transform and reasoning ops of
https://github.com/danbri/factoidal/issues/713 stage 1 were added the
way this section says to add them: a `def` in a new `Wasm/Ops/*.lean`
file, a name in a list in `Wasm/Dispatch.lean`, an arity-checked arm in
`call`. They are `Formats.lean` (JSON-LD, RML, CSVW, XML, XPath, XSLT,
Schematron, JSON Schema, Content MathML, XForms, RIF), `Reasoning.lean`
(the two tableau ops), `QueryExtras.lean` (`queryRaw`, and `queryHdt`,
which reads the HDT file as the byte region and is therefore in
`blobOpNames`) and `ServiceReg.lean` (the SPARQL SERVICE registry,
`callIO` only). Each op needs three things in the same landing: the
`lakefile.lean` root for its module, a positive and a negative case in
`Wasm/native-smoke.sh` (which also pins the `ops` reflection, `blobOps`
included), and the JavaScript side (`npm/factoidal/l4-core.js`'s `OPS`
list and exports, `l4-core.d.ts`).

The three ops of the browser update log (`deltaLogEncode`, `deltaLogDecode`,
`deltaLogMerge`, `Wasm/Ops/DeltaLog.lean`, 2026-10-13,
https://github.com/danbri/factoidal/issues/728) are core-table ops: a name in
`Core.coreOpNames`, an arm in `Core.callArgsBy`, the names appended to the full
table's `stage2OpNames` for its reflection, and `samePure` cases in
`Wasm/CoreDispatchTests.lean`. Their JavaScript side is `lib/api.mjs` with a
host store in `lib/delta-log-hosts.mjs`. Record:
`docs/designissues/2026-10-10-npm-lean-only.md` § 11.

## The core module and the size table (2026-10-10)

`l4factoidal-core.wasm` exists because one dispatch table reaching the whole
library leaves the linker nothing to drop (10.5 MB, 2.07 MB with gzip). The
core table imports only the op modules of its subset, and the core link
drops the rest (5.68 MB, 1.07 MB with gzip). Record, with the per-namespace
table: `docs/designissues/2026-10-10-npm-lean-only.md` § 9.

Rules that keep it small:
- `Wasm/CoreDispatch.lean` must not import `Wasm/Dispatch.lean` or any op
  module of the full table. An op module that mixes core and full ops is
  split (as `Reason`/`ReasonDl`, `Validate`/`ShExValidate`,
  `QueryExtras`/`QueryHdt`); a library the core reads only for one syntax
  becomes a parameter (`ExtraReader` for JSON-LD in `Wasm/Ops/Parse.lean`).
- A new op goes either into the core table (`Core.callArgsBy` or
  `Core.callIOArgsBy`; the full table delegates to them) or into the full
  table and `Core.fullOnlyOpNames`. `Wasm/CoreDispatchTests.lean` fails the
  build when it is in neither list. That check is in the `l4wasm` library, so
  a build of one executable (`lake build l4factoidal`) does not run it: after
  adding an op, run the build of CI, `lake build L4Factoidal l4wasm
  +Harness.Qlvr +Harness.CryptoProbe` (or plain `lake build`). Paid for
  2026-10-25: PR https://github.com/danbri/factoidal-core/pull/83 added
  `sbm11Open`, `sbm11Query` and `sbm11Close` to the full table only, was
  checked with `lake build l4factoidal`, and was merged while its "Lake build
  (full Lean corpus)" check was still running; the check failed at
  `CoreDispatchTests.lean:47` and `main` was red until the next PR added the
  three names to `Core.fullOnlyOpNames`.
- After any change of imports, read `$WORK/l4factoidal-core.size.md` against
  the previous build. A namespace that appears or grows is a reference the
  core closure did not have. The size table is also how a lost `csimp`
  import was found (`skills/lean4-performance`, "A csimp replacement needs
  its import").

`tools/wasm-size-profile.py MAP --wasm FILE [--by module]` prints the table.
The bytes are those wasm-ld kept, before `wasm-opt -O3`; it prints the final
code and data sections too.

## Adding a new export

**First check whether you need one at all.** Most new functionality
should be an OP on the dispatch ABI (`Wasm/Dispatch.lean` +
`Wasm/Ops/*.lean`), not a new `@[export]` C symbol: ops ride the
generic `l4_call` / `l4_call_io` exports that already exist, so they
need no `l4_shim.c` wrapper, no `-sEXPORTED_FUNCTIONS` entry and no
loader method. Adding one is a `def` in an ops module plus two lines in
`Wasm/Dispatch.lean` (a name in `opNames`, an arity-checked arm in
`call`), and it shows up in the `ops` reflection automatically. The
four CL/IKL ops of https://github.com/danbri/factoidal/issues/623 were
added that way on 2026-08-26 and touched no C at all.

Reach for the steps below only for a genuinely new C-level entry point
— a different calling convention, not a new operation. `l4_call_blob`
(2026-09-03) is the one example so far: an op whose input is raw BYTES
rather than text needs a different convention, so it got a C entry
point; the op itself is still an ordinary dispatch arm. See "Moving
BYTES, not text" above.


1. Write the Lean function in `Wasm/Abi.lean` as a pure
   `String → … → String`. Keep the boundary at JSON strings; do not
   invent a struct-passing convention.
2. Add `@[export l4_<name>]` in `Wasm/Exports.lean`.
3. Add the `char *`-level wrapper in `l4_shim.c`, following the
   ownership rules above.
4. Add `_l4_<name>_c` to `-sEXPORTED_FUNCTIONS` in `build-wasm.sh`.
5. Add a method in `docs/web/hub/assets/l4/l4factoidal.js`.
6. Add an `async <name>(…)` wrapper to the `fn` object in
   `docs/_includes/hub.njk` **before** any hub post calls it —
   `tests/hub/fn_surface_parity_test.mjs` enforces this, because the
   node harness binds `fn` to the node package and cannot see a missing
   browser wrapper.
7. Extend `tests/hub/post36_test.mjs`, including an error path.
8. Rerun `build-wasm.sh` to test the change locally. Do not commit the
   rebuilt `.wasm` or `.mjs`: since 2026-10-09 they are gitignored (iron
   rule 9), and the `web` set of `danbri/factoidal-builds` builds them
   from the pushed core commit. Before 2026-10-09 this step said to
   commit the `.wasm`.

## Running the script from the wrong directory (2026-10-10)

`build-wasm.sh` computes its own paths from `BASH_SOURCE`, but step 3
calls `lean` with the shell's working directory, and elan picks the
toolchain from the `lean-toolchain` file of that directory. Run from the
repository root, with no `elan default` set, every one of the 838 core
modules printed `GEN-FAIL ... no default toolchain configured` (the
message is hidden: the call is `>/dev/null 2>&1`), the script did not
stop, and the build then ran on for a while before it could fail. Cost:
about ten minutes of a shared 4-CPU container. The script now changes
into `formal/lean4` itself (and makes the work directory absolute first),
so it runs from any directory. A copy of the script from before
2026-10-10 needs `cd formal/lean4 && bash Wasm/build-wasm.sh [work-dir]`,
or `elan default leanprover/lean4:v4.33.1` set once. When several agents
build at once, give each its own work directory (the argument); the
default `/tmp/l4wasm-build` is shared. Step 5 also needs `uv.h`
(`apt-get install libuv1-dev`); without it the script stops there, after
the long steps 3 and 4 have cached their output.

## Rebuilding after a Lean change

`build-wasm.sh` re-runs `lake build l4wasm` first, so a change to any
`L4Factoidal` or `Wasm` module is picked up. The core library and
runtime objects are cached in the work dir and are NOT recompiled — that
is the fast path (seconds, not minutes). Delete the work dir only when
the Lean toolchain version changes.

**A Lean toolchain bump is a wasm rebuild.** `lean-toolchain` pins both
the compiler and the core sources the wasm objects are generated from;
bumping it without re-running this script leaves an artifact built
against the old core library.

## Traps, each one paid for

- **Timing wasm under node with default flags measures Liftoff code.** A
  timed loop that wasm-opt inlined into a function entered once never runs
  as TurboFan code (V8 has no on-stack replacement for wasm). Paid for
  2026-10-12: a C kernel timed at 3.8 ms under node ran in 1.6 to 2.2 ms with
  `--no-liftoff`, and a wrong Lean-to-C ratio sent an agent to look for a
  wasm32 cause that did not exist. Check with `node --liftoff-only`; the
  record is section 7 of `docs/designissues/2026-10-12-lean-to-c-performance.md`.
  Not measured: how much a long first call into the library module loses.

- **A `Nat` literal at or above 2^31 leaks one bignum per evaluation on
  wasm32.** The compiler emits `lean_cstr_to_nat("4294967296")` at the
  use site; when that value goes straight into a borrowing comparison
  (`lean_nat_dec_lt`) nothing releases it. On 64-bit targets the literal
  is an unboxed scalar, so native measurements never show it; on the
  GMP-free wasm32 build each comparison leaves a 40-byte `mpz` on the
  heap. Paid for 2026-09-07: the packer retained 15.6 objects per quad
  (1.7 million per 110,000-row pack, surviving `packClose`), the
  all-skosdex pack died at the memory ceiling twice on Fly, and two
  agent-days went to the allocator before a heap histogram by object
  tag (`l4_heap_tags_c`) found two values only, `4294967296` and
  `4294967295`. Rule: never write such a literal inline in executable
  code; use `L4Factoidal.NatBounds.two32` (or add a sibling there),
  declared `@[reducible, noinline]` — `noinline` is what stops the
  compiler folding it back into the call site (measured), `reducible`
  keeps it transparent to proofs. Full record:
  `docs/designissues/2026-09-07-wasm-packer-memory.md` §9.

- **Linear memory that grows across calls while the live heap does not is
  the allocator, and the arena size decides it.** On wasm32 mimalloc takes
  arenas of `arena_reserve` / 4 (32 MiB by default) from emmalloc, in 4 MiB
  blocks; an object above 2 MiB is a run of whole blocks. Paid for
  2026-10-12 (https://github.com/danbri/factoidal/issues/744): the npm
  `parse()` of 48,000 triples builds strings of 4.5 MB, and six calls raised
  linear memory from 257 to 1,224 MB while `l4_heap_tags_c` reported 0.5 MB
  live after every call. Arenas of 64 and 96 MiB made it worse, 128 MiB
  made it flat (184 MB). `l4_ensure_init` in `Wasm/l4_shim.c` now sets
  `mi_option_arena_reserve` to 512 MiB (KiB units) after the module
  initialisation, so the first arena keeps the default size. To tell the
  two cases apart, read `l4_heap_tags_c` (the sum of its `bytes` is the live
  heap) after each call beside `HEAPU8.byteLength`; to test an allocator
  option without a rebuild, call `_l4_mi_option_set(option, value)` after the
  engine has loaded. Record:
  `docs/designissues/2026-10-10-lean-vs-fstar-performance.md` §11.7.

1. **`leanir` fails silently** — emits a near-empty module and exits 0.
   Do not use it. (Above.)
2. **Dropping mimalloc** aborts the module on error paths only, with a
   message that points at the wrong place. (Above — the big one.)
3. **`emcc` instead of `em++` at link time** — undefined libc++.
4. **Renaming the glue or the wasm independently** — ENOENT everywhere.
5. **Deriving the toolchain directory from the tag.** elan spells it
   `leanprover--lean4---v4.33.1` (tag and all), and `command -v lean`
   points at elan's *shim* in `~/.elan/bin`, whose grandparent is
   `~/.elan`, not the toolchain. Use `lean --print-prefix`. Getting this
   wrong resolved to `~/.elan` and the build failed 40 lines later with
   a confusing "toolchain does not ship core sources".
6. **`lean.h` needs `lean/config.h`**, which CMake generates and the
   source tree does not contain. Write it (step 2).
7. **`brew cleanup --prune=all` can break `emcc`.** It removes superseded
   kegs, and Emscripten runs on Homebrew's `node`; a stale
   `llhttp` dependency left `node` unable to start
   (`Library not loaded: libllhttp.9.3.dylib`), so `emcc --version`
   failed with a dyld error that looks nothing like a toolchain problem.
   Fix: `brew reinstall node`.
8. **`String.toList` results crash `String.ofList` on wasm32 — patch
   the runtime's list terminator** (2026-08-25). Upstream defect in
   `runtime/object.cpp`'s `string_to_list_core` (the body of
   `lean_string_data`, i.e. `String.data`/`String.toList`), present at
   v4.33.1 and still on master: it terminates the `List Char` it
   builds with `lean_box_uint32(0)`. On 64-bit that folds to the
   scalar `lean_box(0)` — the correct `List.nil` — so no shipped Lean
   build misbehaves. On wasm32 (`sizeof(void*) == 4`)
   `lean_box_uint32` HEAP-ALLOCATES a ctor object, which is not a
   scalar. Lean-COMPILED consumers read that object's pointer tag
   (0 = `List.nil`) and work anyway — `span`, `take`, `zipIdx`,
   `foldl` all pass — but `lean_string_mk` (`String.mk` /
   `String.ofList`) walks the list with `while (!lean_is_scalar(o))`,
   never meets a terminator, and runs off across the heap: measured
   here as a 3,267,424,256-byte (3 GB) `std::string` allocation →
   `std::bad_alloc`, surfacing from a `lean_obj_once` closed-constant
   initializer, wasm32 only (native x86_64 peaked at 11.6 MB RSS).
   The half-working state is the trap: every list op succeeding
   points the suspicion away from the list's own representation.
   Fix: `build-wasm.sh` step 1b patches the one line to `lean_box(0)`
   after the sparse clone (idempotent; invalidates the cached
   `object.o`). If the patch anchor ever vanishes on a toolchain bump,
   the build fails loudly — re-audit `string_to_list_core` upstream
   before deleting the step.
9. **Editing a Lean source WHILE `lake build` runs produces link
   errors that name modules which are, in fact, present.** Lake plans
   the link from the dependency graph it read at startup; an import
   added to a module mid-run is compiled but not added to that plan.
   Measured 2026-08-26: adding imports to `Wasm/Ops/CL.lean` during a
   running build failed the `l4factoidal:exe` link with
   `undefined symbol: initialize_l4factoidal_L4Factoidal_CL_Alpha` and
   nine similar, while `L4Factoidal.lean` imported `CL.Alpha` and its
   `.olean` was built. The tell is that the errors are ALL from
   `ld.lld`, with none from Lean's elaborator — a genuine missing
   module fails earlier, at elaboration, with `unknown identifier`.
   Fix: re-run `lake build` on the settled source; nothing needs
   cleaning. (This is the wasm-side face of hazard #9 in
   `workflow-gotchas-debugging`.)

10. **A wasm rebuild is not complete until all FOUR copies and the
   NATIVE binary move together.** (Until 2026-10-09 they were committed
   and a landing had to move all of them; now none is committed. A local
   rebuild must still move all four, and `build-wasm.sh` still checks
   it. The `web` and `linux-x86_64` release sets carry them for other
   checkouts.) The copies are
   `docs/web/hub/assets/l4/`, `npm/factoidal/l4-assets/`,
   `npm/factoidal-lean/` and `docs/npm/lean/`; they must be
   byte-identical (the core module has two copies, in the first two
   directories, checked the same way), because the loader stamps ONE `WASM_VERSION` (the
   wasm's own sha256 prefix) into the `?v=` cache-busting query, so a
   copy that differs is served under a hash that is not its own.
   Until 2026-08-26 step 9 synced only three: `npm/factoidal/l4-assets/`
   — the copy issue #618 made the one a plain
   `npm install @factoidal/core` resolves — was missing, so a rebuild
   left it holding the PREVIOUS wasm with everything green. Step 9 now
   syncs it and ends with a sha256 comparison across all four that
   FAILS the build on disagreement. Separately, `bin/linux-x86_64/l4factoidal`
   was committed (iron rule #9 then) and is a SECOND artifact carrying
   the same ops table: refresh it from `.lake/build/bin/l4factoidal`
   after a local wasm rebuild, or `l4factoidal ops` keeps reporting the
   old surface long after the wasm is right. Since 2026-10-09 the file
   is not committed; the `linux-x86_64` release set carries the native
   Lean CLI.

11. **`wasm-ld: warning: function signature mismatch:
   lean_io_create_tempfile / lean_io_create_tempdir` is expected.**
   Lean's generated `Init_System_IO.o` declares them with a different
   arity than the runtime's `io.o` defines. Neither is reachable from
   the exported ABI — the link still reports `initialize_libuv` as its
   only undefined symbol, which is the standing purity evidence — so
   this is noise, not a regression. What would NOT be noise is the
   undefined-symbol list growing; treat that as a design question per
   "the purity evidence" above.

   **Any OTHER signature mismatch is a trap, and the build now fails on
   it** (`link_module` in `Wasm/build-wasm.sh`). wasm-ld replaces a call
   whose signature differs from the definition with an `unreachable` stub
   and prints only a warning. 2026-10-25,
   https://github.com/danbri/factoidal/issues/1009: `ffi/l4_hostread.c`
   defined `l4_host_read_at` and `l4_host_size` with a trailing
   `lean_obj_arg world`, but the Lean 4.33 code generator ERASES the IO
   world token for `@[extern]` IO functions too (the generated
   `.lake/build/ir/Wasm/HostRead.c` declares `l4_host_size(lean_object*,
   lean_object*)`). Native arm64 and x86-64 ignore an extra argument, so
   native `l4sbm11` and native-smoke passed; in wasm `sbm11Open` trapped on
   its first host call, the 0.14.0 release shipped without SBM11 in npm
   (https://github.com/danbri/factoidal-core/pull/92), and the two
   warnings had been in the lean-wasm job log all along, read as this
   item's "noise". Rule: an IO extern's C definition takes the explicit
   arguments only, no world; check the generated declaration in
   `.lake/build/ir/<Module>.c` before writing the C.

12. **`pretty()` in a hub cell returns a DOM element in the browser and a
   plain object in the node harness.** Never read `.rows` off a
   `pretty()` result in a later cell — keep raw values in their own named
   cells and call `pretty` only in display cells. (Anti-pattern #28.)

## Gates

```bash
export PATH="$HOME/.elan/bin:$PATH"
cd formal/lean4 && lake build            # #guards + theorems + the ABI
lake exe l4wasm-cli version              # the ABI, natively
node --test tests/hub/post36_test.mjs tests/hub/fn_surface_parity_test.mjs
PLAYWRIGHT_PKG=<dir> bash tests/web-demos/hub_browser_all.sh   # browser sweep
```

The native driver (`l4wasm-cli`) exists so an ABI bug and a wasm bug are
never confused: if `lake exe l4wasm-cli bgp data.json bgp.json` and the
wasm disagree, the problem is in the build, not in the Lean.

## Scope of the current ABI (phase 1)

`l4_bgp_query` only. No SPARQL string parsing, no Turtle/N-Triples
reading, no §18.5 operators across the boundary. The JSON reader/writer
in `Wasm/Abi.lean`'s `L4Wasm.Json` namespace is a **shim marked for
deletion** once `L4Factoidal.JSON` and the N-Triples parser land from
`lean4/json` and `lean4/syntax-ntriples-nquads`; the exported C symbols
and the wire format do not change when it goes. Say this plainly
wherever the Lean engine is demonstrated — hub post 36 does.

The Lean side keeps its proof policy across this boundary: no `sorry`,
no `axiom`, no `partial`, no `native_decide`. The JSON reader recurses
on an explicit `Nat` fuel precisely so it is structurally recursive and
total without well-founded-recursion obligations.
