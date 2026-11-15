# CI builds: jobs, caches, cold builds and timing records

How `danbri/factoidal-builds` `build.yml` builds a core commit, what it caches, how each cache is
kept correct, and how to see where the time goes. The project is Lean first: since 2026-11-15 no
F\* build, test or release product runs automatically, and core's F\* workflows run only by hand.

## Jobs and order

| Job | Runner | Needs | What |
|---|---|---|---|
| `lean` | Linux | `resolve` | full `lake build`, smoke scripts, tail-recursion gate, Lean scoreboard |
| `lean-macos` | macOS | `resolve` | the same on macOS; its `.lake` cache feeds the macOS bundle job |
| `lean-wasm` | Linux | `lean` | `Wasm/build-wasm.sh` |
| `foafnaut-engines` | Linux | `resolve` | `build-engines.sh` and `build-web-render.sh --wasm` |
| `foafnaut-host-tests` | Linux | `foafnaut-engines` | `test.sh --skip-build` on the Wasm engines: the first test result |
| `foafnaut` | macOS | `lean-macos`, `foafnaut-engines` | `build-web-render.sh --native`, packaging, `test.sh` with the native library |
| `web-gates` | Linux | `lean`, `lean-wasm` | npm suite, OWL package checks, Touchstone LWS client lab |
| `publish` | Linux | all | releases for core `main` commits only; a release is never replaced |
| `metrics` | Linux | `publish` | the timing and cache record of the run (below) |

`lean` and `lean-macos` are separate jobs with one step list (a YAML anchor), so no Linux job
waits for a macOS runner. macOS runners are few and shared with `foafnaut-macos.yml`: waits of
10 to 85 minutes for one were measured on 2026-11-15.

## Caches

A restored cache is only a starting point: the tool that uses it decides, file by file, whether
a cached result still holds.

| Cache | Jobs | Key | Why a hit is correct | Logs show |
|---|---|---|---|---|
| `.lake` | saved by `lean`, `lean-macos`; restored by `lean-wasm`, `foafnaut-engines`, `foafnaut` | `lake-<platform>-<hash of lean-toolchain>-<hash of every .lean, lakefile.lean, ffi/**, quickjs/*.js>`; else the newest of the same toolchain | Lake rebuilds any module whose source or dependency hash changed. Lake does not track `include_str` inputs, so after a fallback restore the `WasmVM/Hosts/LeanJS*` outputs are deleted and rebuilt | `Cache restored from key:` (the full key: exact; shorter: fallback) or `Cache not found` |
| Emscripten ccache | `foafnaut-engines` | `ccache-emcc-6.0.8-Linux-<hash of lean-toolchain>-<run id>`; restores the newest of the same Emscripten and toolchain | ccache keys each object on the compiler's bytes (`CCACHE_COMPILERCHECK=content`), the command line and the preprocessed source with every header. `EM_COMPILER_WRAPPER=ccache` puts it under emcc, so `build-engines.sh` uses it too | step `ccache statistics`: `Hits: N / M` (this run's, after `ccache -z`) |
| leanc object cache | `foafnaut` (macOS bundle), `foafnaut-macos.yml` | `leanc-objects-v1-darwin-arm64-<hash of lean-toolchain>-<run id>`; restores the newest | factoidal-builds `release-tests/leanc-cache.sh` stands in front of `leanc` and keys each object on the toolchain name, the flags and the C source; Lean's generated C includes only the toolchain's `lean.h` | step summary: `C objects: N from the cache, M compiled` |
| Emscripten SDK | `foafnaut-engines`, `lean-wasm` | `emsdk-6.0.8-Linux` | a pinned tool install | `Cache restored from key: emsdk-6.0.8-Linux` |
| Lean Wasm runtime | `foafnaut-engines`, `lean-wasm` | `l4wasm-work-cache-<toolchain>.tar.gz` on the builds branch `toolchain-cache` | `build-web-render.sh` checks the runtime's witness hashes before use | `No cache for <toolchain>` when absent |

Key coverage is tested: factoidal-builds `tests/test_cache_keys.py` shows that the leanc cache
misses on a changed toolchain name, flag or source and hits on the same inputs, and that ccache
misses on a changed header.

### The cache audit

`build-web-render.sh` writes every C compile command to `.build/web-render/compile-commands.txt`.
After the build, factoidal-builds `scripts/cache-audit.sh` compiles a random sample again (12 Wasm
compiles in `foafnaut-engines`, 8 native ones in `foafnaut`) with every cache bypassed, and fails
the job if any object differs from the one the build linked. It also records the sha256 of every
object (artifacts `cache-audit-wasm`, `cache-audit-native`), so a cold and a warm build of one
commit can be compared object by object. Its log lines start with `CACHE_AUDIT`.

### A cold build

    gh workflow run build.yml --repo danbri/factoidal-builds -f core_ref=<ref> -f cold=true

No `.lake`, ccache or leanc object cache is restored (`CCACHE_DISABLE=1`), and none is saved. Use
it when a cache is suspected, and compare its `cache-audit-*` object hashes with a warm run of the
same commit. The final `.wasm` and `.dylib` do not compare byte for byte between runs: the
engine's build facts carry the build time. A cold run takes much longer: every Lean module is
built again.

## Parallel compiles

`build-web-render.sh` runs its C compiles `COMPILE_JOBS` at a time (default: the core count, at
most 4; `COMPILE_JOBS=1` gives the old serial order). Objects are linked in the old order.
`FOAFNAUT_CC_LAUNCHER=ccache` puts a launcher in front of the native compiler for local builds.

## Timing and cache records

The `metrics` job runs factoidal-builds `scripts/ci-metrics.py run` on its own run: per job the
queue wait, duration, start and end after dispatch, the longest steps, every cache restore (exact,
fallback or miss, and bytes), the compiler cache counts and the audit. It writes a table to the
run summary, an artifact `ci-metrics`, and a row per job to `runs.csv` (with `runs/<run id>.json`)
on the builds branch `ci-metrics`, as release tests record scores on `wpt-scores`. A slowdown
shows in the trend of the last runs (needs `gh` logged in):

    python3 scripts/ci-metrics.py trend --n 10 --records <checkout of branch ci-metrics>

## Measured on 2026-11-15

| | Before | After |
|---|---|---|
| F\* jobs (Linux, macOS) | 31 and 35 min every run | none |
| Dispatch to last job, warm `.lake` (run 43705361243 before, 43723628060 after F\* removal) | 142 min (57 of them waiting for a macOS runner) | 89 min |
| `lean-wasm` start | after the macOS `lean` job (+85 min in 43709145133) | after the Linux `lean` job (+13 min in 43723263913) |
| Wasm C compiles in `foafnaut-engines` (about 600 files) | 11 min, one at a time | 5 min in parallel with an empty ccache (43723263913); 20 s with a warm one, 734 of 735 hits (43726011009) |
| `foafnaut-engines` job | 42 to 58 min | 29 min (empty ccache), 25 min (warm) |

## Not done, and why

- Skipping a whole job when its inputs did not change (path filters): each job's inputs span most
  of core (Lean sources, lab files, tools, third_party), and a filter that misses one input would
  publish a stale artefact. Lake, ccache and the leanc cache already make an unchanged part cheap.
- The Wasm link (`em++ -O3` with wasm-opt, about 6 minutes, `BINARYEN_CORES=2`) and the serial
  compile of the lab modules (`lean` per module, about 5 minutes) are the largest remaining steps
  in `foafnaut-engines`. Both are possible next steps; neither is cached yet.
