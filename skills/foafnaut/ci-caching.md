# CI builds: jobs, caches, cold builds and timing records

How `danbri/factoidal-builds` `build.yml` builds a core commit, what it caches, how each cache is
checked, and how to see where the time goes. The project is Lean first: since 2026-11-15 no F\*
build, test or release product runs automatically (core's F\* workflows run only by hand).

## Jobs and order

| Job | Runner | Needs | What |
|---|---|---|---|
| `lean` | Linux | `resolve` | full `lake build`, smoke scripts, tail-recursion gate, Lean scoreboard |
| `lean-macos` | macOS | `resolve` | the same on macOS; its `.lake` cache feeds the macOS bundle job |
| `lean-wasm` | Linux | `lean` (Linux only) | `Wasm/build-wasm.sh` |
| `foafnaut-engines` | Linux | `resolve` | `build-engines.sh` and `build-web-render.sh --wasm` |
| `foafnaut-host-tests` | Linux | `foafnaut-engines` | `test.sh --skip-build` on the Wasm engines: the first test result |
| `foafnaut` | macOS | `lean-macos`, `foafnaut-engines` | `build-web-render.sh --native`, packaging, `test.sh` with the native library |
| `web-gates` | Linux | `lean`, `lean-wasm` | npm suite, OWL package checks, Touchstone LWS client lab |
| `publish` | Linux | all | releases for core `main` commits; a release is never replaced |
| `metrics` | Linux | `publish` | the run's timing and cache record, and the cache prune (below) |

`lean` and `lean-macos` are separate jobs (one step list, a YAML anchor), so no Linux job waits
for a macOS runner. macOS runners are few and shared with `foafnaut-macos.yml`: waits of 20 to 85
minutes for one were measured on 2026-11-15.

## Caches

A restored cache is only a starting point: the tool that uses it decides per file whether the
cached result still holds.

| Cache | Jobs | Key | Why a hit is correct | The log shows |
|---|---|---|---|---|
| `.lake` | `lean`, `lean-macos` save; `lean-wasm`, `foafnaut-engines`, `foafnaut` restore | `lake-<platform>-<hash of lean-toolchain>-<hash of every .lean, lakefile.lean, ffi/**, quickjs/*.js>`; else the newest of the same toolchain | Lake rebuilds a module whose source or dependency hash changed. Lake does not track `include_str` inputs, so after a fallback restore the `WasmVM/Hosts/LeanJS*` outputs are deleted and rebuilt | `Cache restored from key:` (the same key: exact hit; another: fallback) or `Cache not found` |
| Emscripten ccache | `foafnaut-engines` | `ccache-emcc-6.0.8-Linux-<hash of lean-toolchain>-<run id>`; restores the newest of the same Emscripten and toolchain | ccache keys each object on the compiler's bytes (`CCACHE_COMPILERCHECK=content`), the whole command line and the preprocessed source with every header. Wired in by `EM_COMPILER_WRAPPER=ccache` | step `ccache statistics`: `Hits: N / M` |
| leanc object cache | `foafnaut` (macOS bundle), `foafnaut-macos.yml` | `leanc-objects-v1-darwin-arm64-<hash of lean-toolchain>-<run id>`; restores the newest | builds `release-tests/leanc-cache.sh` sits in front of `leanc` and keys each object on the toolchain name, the flags and the C source; Lean's generated C includes only the toolchain's `lean.h` | `C objects: N from the cache, M compiled` |
| Emscripten SDK | `foafnaut-engines`, `lean-wasm` | `emsdk-6.0.8-Linux` | a pinned tool install | `Cache restored from key: emsdk-6.0.8-Linux` |
| Lean Wasm runtime | `foafnaut-engines`, `lean-wasm` | `l4wasm-work-cache-<toolchain>.tar.gz` on the builds branch `toolchain-cache` | `build-web-render.sh` checks the runtime's witness hashes | `No cache for <toolchain>` when absent |

Key coverage is tested: builds `tests/test_cache_keys.py` shows that the leanc cache misses on a
changed toolchain name, flags or source and hits on the same inputs, and that ccache misses on a
changed header.

GitHub keeps 10 GB of caches per repository and evicts the least recently used beyond that. Each
`.lake` is about 1 GB, so on 2026-11-15 the small compiler caches were evicted within hours. The
`metrics` job now deletes all but the newest two caches of each `.lake`, ccache and leanc family
(`scripts/ci-metrics.py prune --keep 2`). A deleted cache only makes a later restore fall back
or miss.

### The cache audit

`build-web-render.sh` writes every C compile command to `.build/web-render/compile-commands.txt`.
After the build, builds `scripts/cache-audit.sh` recompiles a random sample (12 Wasm compiles in
`foafnaut-engines`, 8 native compiles in `foafnaut`) with every cache bypassed, and fails the job
if an object differs from the one the build linked. It also records the sha256 of every object
(artifacts `cache-audit-wasm`, `cache-audit-native`), so a cold and a warm build of one commit
can be compared object by object. Its log lines start with `CACHE_AUDIT`.

### A cold build

    gh workflow run build.yml --repo danbri/factoidal-builds -f core_ref=<ref> -f cold=true

No `.lake`, ccache or leanc object cache is restored (`CCACHE_DISABLE=1`), and none is saved. Use
it when a cache is suspected, and compare its `cache-audit-*` object hashes with a warm run of
the same commit. The final `.wasm` and `.dylib` do not compare byte for byte between runs: the
engine's build facts (`WebBuild`) carry the build time.

## Parallel compiles

`build-web-render.sh` runs its C compiles `COMPILE_JOBS` at a time (default: the core count, at
most 4; `COMPILE_JOBS=1` is the old serial order); objects are linked in the old order.
`FOAFNAUT_CC_LAUNCHER=ccache` puts a launcher in front of the native compiler in local builds.

## Timing and cache records

The `metrics` job runs builds `scripts/ci-metrics.py run` on its own run: per job the queue
wait, duration, start and end after dispatch, the longest steps, every cache restore (hit,
fallback, miss, bytes), the compiler cache counts and the audit. It writes a table to the run
summary, an artifact `ci-metrics`, and a row per job to `runs.csv` (and `runs/<run id>.json`)
on the builds branch `ci-metrics`, as release tests record scores on `wpt-scores`. A trend over
the last runs (needs `gh`):

    python3 scripts/ci-metrics.py trend --n 10 --records <checkout of the branch ci-metrics>

## Measured on 2026-11-15

| What | Before | After |
|---|---|---|
| Dispatch to last job, whole run | 142 min (run 43705361243, with F\*; 57 of it waiting for a macOS runner) | 89 min without F\* (43723628060) |
| F\* jobs, every run | 31 min Linux + 35 min on a macOS runner | none |
| `lean-wasm` start | after the macOS `lean` job (up to +85 min) | after the Linux `lean` job (+13 min) |
| Wasm C compiles of `build-web-render.sh` | 11 min, serial | 5 min parallel with a cold ccache; 20 s warm (734 of 735 hits) |
| Web-render step of `foafnaut-engines` | 31.8 to 44.6 min | 20.3 min cold ccache, 17.3 min warm |
| Native C compiles on macOS | 13 min, serial | 608 of 611 objects from the leanc cache |
| Cold against warm, same core commit | | 628 of 629 Wasm objects sha256-identical; the one difference is `WebBuild.o` (build time); both audits 12 of 12 same |

## Not done, and why

- Skipping a whole job when its inputs did not change (path filters): each job's inputs span most
  of core (Lean sources, lab files, tools, third_party). A filter that misses one input would
  publish a stale product; Lake, ccache and the leanc cache already make an unchanged part cheap.
- The Wasm link (`em++ -O3`, about 6 minutes, `BINARYEN_CORES=2`) and the serial compile of the
  lab modules (`lean` per module, about 5 minutes) are the next costs on the engine path.
