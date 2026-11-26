# leanjs with link-time optimisation on Linux (issue 471, step 1)

Owner decision, 2026-11-25 (CLAUDE.md, "BubblePopJS JIT: mode parameter accepted; LTO default and
tier 2 started"): make the link-time optimised build of
[PR 559](https://github.com/danbri/factoidal-core/pull/559) the default, measured before and after.
Tracking: https://github.com/danbri/factoidal-core/issues/471. The method and the macOS numbers are in
[2026-11-16-lean-memory-overhead.md](2026-11-16-lean-memory-overhead.md), section D.

## What changed

`formal/lean4/lakefile.lean`, on x86-64 Linux, with `lake build -R -K leanjsLto=on` (see the trap
below for `-R`):

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
with a message; it does not fall back silently. macOS and other hosts
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

The program that `lake build leanjs` makes with this change (commit of this record) gives 0.924,
0.928, 0.921, 0.935 and 0.947 (geometric mean **0.931**), and the same Test262 verdict list.

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

## Landing state (2026-11-25)

Landed on `main` as opt-in (`-K leanjsLto=on`), not as the default. Reason: the `leanjs` step of
`danbri/factoidal-builds` `build.yml` installs no libc++, libc++abi or gmp headers, and the LTO
binary is 2.2 % larger, above the 2 % tolerance of `tools/binary-budget.py`. A default that
fails there would stop every Linux release. To make it the default: add those packages to that
step, raise the `leanjs` budget by hand with this record as the reason, then change
`leanjsLto` in `lakefile.lean` to `!= some "off"`. Tracking:
https://github.com/danbri/factoidal-core/issues/471.

## What the default needs (2026-11-26)

Checked against `danbri/factoidal-builds` `.github/workflows/build.yml` (read 2026-11-26, step
"Shipped binaries link no Lean compiler code; size budget", the only step that builds `leanjs`):

1. **Size budget: not a blocker on Linux.** `tools/binary-budget.json` has a `leanjs` budget only for
   `darwin-arm64`. `binary-budget.py check` reports a binary with no budget on its platform and does
   not fail (its usage text). LTO is on only for x86-64 Linux, so the +2.2% meets no budget. The
   reason given in "Landing state" above for keeping the opt-in was wrong for this half.
2. **Packages: the blocker.** That step installs nothing; the Linux job installs `libc++-dev
   libc++abi-dev` only for the native Foafnaut step (line 818 on that date), not before `leanjs`.
   `ffi/leanrt-lto.sh` also needs `gmp.h` and network for its first fetch of the pinned Lean sources.

Change requested for `danbri/factoidal-builds` (not made here: the release manager dispatches and
merges builds), in that step before `lake build leanjs`:

```yaml
          if [ "$(uname -s)-$(uname -m)" = "Linux-x86_64" ]; then
            sudo apt-get update -q
            sudo apt-get install -y -q libc++-dev libc++abi-dev libgmp-dev
          fi
```

Then, in core, after a builds run with that change is green: `leanjsLto` in
`formal/lean4/lakefile.lean` becomes `get_config? leanjsLto != some "off" && <x86-64 Linux>`, and this
record's "Landing state" is updated. Order matters: if core changes first, the Linux `leanjs` step
stops with the message of `ffi/leanrt-lto.sh`.

## Trap: `-K` without `-R` builds without LTO, with no message (2026-11-26)

In a workspace that Lake had configured before, `lake build -K leanjsLto=on leanjs` gave a `leanjs`
byte-identical to the plain build (16,751,936 bytes, no job rebuilt): Lake kept the configuration of
the earlier run. `lake build -R -K leanjsLto=on leanjs` rebuilt 199 jobs and gave the LTO program
(17,083,720 bytes). Cost: one build of about 25 minutes on the 4-vCPU VM, and a measurement that
would have compared a program with itself. Rule: give `-R` with every `-K`, and check that the
program's size changed. A default in the
lakefile (the change requested above) does not depend on `-K`.

## Measured again on main `b629c2b71` (2026-11-26)

Same Linux 4-vCPU VM, Lean 4.33.1, both programs built from the same worktree of `b629c2b71` (the
LTO one with `-R`). Size: plain 16,751,936 bytes, LTO 17,083,720 bytes (+1.98%). Every run gave the
reference answer.

Instructions (`valgrind --tool=callgrind`, size N):

| Workload | plain | LTO | ratio |
|---|---|---|---|
| acorn (N=1) | 2,320,309,403 | 2,199,721,485 | 0.948 |
| immutable (N=1000) | 2,217,261,084 | 2,114,886,174 | 0.954 |
| lodash (N=1000) | 1,549,818,980 | 1,477,441,507 | 0.953 |
| marked (N=6) | 491,894,546 | 463,279,097 | 0.942 |
| pako (N=32) | 4,059,592,302 | 3,882,221,798 | 0.956 |
| geometric mean | | | **0.951** |

CPU time (`realworld.py --runs 5`, least of 5, ms; run at 4N less the load):

| Workload | plain load | LTO load | plain run | LTO run | run ratio |
|---|---|---|---|---|---|
| acorn | 45.4 | 41.5 | 795.3 | 736.8 | 0.93 |
| immutable | 40.5 | 35.0 | 785.3 | 728.4 | 0.93 |
| lodash | 58.0 | 51.7 | 339.3 | 334.7 | 0.99 |
| marked | 29.2 | 25.5 | 87.0 | 80.2 | 0.92 |
| pako | 34.8 | 33.7 | 862.3 | 854.5 | 0.99 |

The instruction ratio (0.951) is smaller than the 0.931 of 2026-11-25 on main `100307076`; the
programs differ (PRs since then), and the cause of the difference was not measured.
