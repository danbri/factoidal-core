# leanjs with link-time optimisation on Linux (issue 471, step 1)

Owner decision, 2026-11-25 (CLAUDE.md, "BubblePopJS JIT: mode parameter accepted; LTO default and
tier 2 started"): make the link-time optimised build of
[PR 559](https://github.com/danbri/factoidal-core/pull/559) the default, measured before and after.
Tracking: https://github.com/danbri/factoidal-core/issues/471. The method and the macOS numbers are in
[2026-11-16-lean-memory-overhead.md](2026-11-16-lean-memory-overhead.md), section D.

## What changed

`formal/lean4/lakefile.lean`, on x86-64 Linux, unless `lake build -K leanjsLto=off`:

- The C of the `JS` library's modules (`L4Factoidal.JS.*`, the engine) is compiled with
  `-flto=thin -ffat-lto-objects`: each object holds machine code and ThinLTO bitcode.
- `leanjs` is linked with `-flto=thin -O3 -Wl,--fat-lto-objects` and the archive of the target
  `leanrt_lto` (`ffi/leanrt-lto.sh`): Lean's `runtime/object.cpp`, `runtime/alloc.cpp` and mimalloc
  v2.2.3's `static.c` as bitcode, with Lean's flags and `LEAN_USE_GMP`. The archive comes before the
  toolchain's `libleanrt.a` on the link line, so the linker takes these units and not the toolchain's.
  `lean_alloc_small`, `mi_malloc_small`, `lean_dec_ref_cold`, `lean_del_core` and `mi_free` are then
  inlined into the engine.
- Every other executable that links `JS` modules uses the machine code of the same objects, as
  before: `ld.lld` reads the bitcode section only with `--fat-lto-objects` (checked: the `leanjs`
  objects linked without the LTO arguments give a program with the same calls as Lake's plain build).

Needs on the build machine: `clang++` with libc++ headers (`libc++-dev libc++abi-dev`), `gmp.h`
(`libgmp-dev`, GMP 6.3.0 here, as the toolchain's `libgmp.a`), `git` and network for the first fetch
of the pinned sources (or `LEANRT_LTO_LEAN_SRC` naming a Lean checkout). Without them the build stops
with a message that names `-K leanjsLto=off`; it does not fall back silently. macOS and other hosts
build `leanjs` as before.

Not changed: the native engine library (`build-web-render.sh --native`). Its Linux path has no LTO
branch (`FOAFNAUT_NATIVE_LTO` is macOS only); the change and its 16 to 20 minute build were not done
in this session.

## Measurements

Machine: Linux cloud container, 4 vCPU, 15 GB, shared with two other agents' builds; Lean 4.33.1,
clang 22.1.4 (toolchain), clang 18.1.3 (runtime units). Same generated C in both builds (main
`100307076`). `perf` on this VM has no hardware counters, so instructions are from
`valgrind --tool=callgrind` (exact, single run).

Instructions, library corpus of `bubblepop_perf/realworld.py` at size N (hand-built ThinLTO program
from the same objects and flags as the Lake target; the Lake-built program has the same inlining):

| Workload | Lake build | ThinLTO | ratio |
|---|---|---|---|
| acorn (N=1) | 2,314,857,558 | 2,133,282,724 | 0.922 |
| immutable (N=1000) | 2,213,607,554 | 2,045,704,297 | 0.924 |
| lodash (N=1000) | 1,559,774,828 | 1,432,452,391 | 0.918 |
| marked (N=6) | 490,191,645 | 453,681,573 | 0.926 |
| pako (N=32) | 5,358,094,394 | 5,048,695,981 | 0.942 |
| geometric mean | | | **0.926** |

CPU time (user + system, `wait4`), size 4N and the micro set, 7 interleaved rounds (order reversed
every other round), median; the spread between runs of one program was up to 40% (other builds on
the machine), so read the direction:

| Script | Lake s | ThinLTO s | ratio |
|---|---|---|---|
| acorn-4 | 1.269 | 1.281 | 1.010 |
| immutable-4000 | 1.084 | 0.986 | 0.909 |
| lodash-4000 | 0.637 | 0.532 | 0.835 |
| marked-24 | 0.158 | 0.148 | 0.938 |
| pako-128 | 1.664 | 1.493 | 0.897 |
| geometric mean, libraries | | | 0.916 |
| fib | 0.114 | 0.109 | 0.949 |
| props | 0.263 | 0.226 | 0.858 |
| method | 0.413 | 0.328 | 0.793 |
| array | 0.342 | 0.321 | 0.938 |
| closure | 0.331 | 0.253 | 0.763 |
| alloc | 0.489 | 0.439 | 0.897 |
| json | 0.276 | 0.228 | 0.826 |
| mixed | 0.077 | 0.062 | 0.802 |

Outputs: every script printed the same bytes with both programs. Test262 subset
(`third_party/testing/test262`, all its directories, `leanjs test262 ... --list`): 5,962 pass, 338
fail, 1 skip of 6,301 with both; the verdict lists are byte-identical.

The gain is smaller than on macOS (0.842 of instructions there): Linux has no `_tlv_get_addr` call
in front of mimalloc's heap, and its shipped build already uses initial-exec thread-local access.

## Cost

- Build: the `JS` modules' C compiles about twice as long (machine code and bitcode); the `leanjs`
  link runs ThinLTO over the engine (about 1 minute on 4 vCPUs). Other executables do not change.
- `leanjs` size: 14,624,672 to about 14,942,424 bytes (+2.2%).
