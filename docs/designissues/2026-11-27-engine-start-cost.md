# Engine start: module initialization and the BubblePopJS realm decode (2026-11-27)

Issue: https://github.com/danbri/factoidal-core/issues/471 (BubblePopJS JIT; goal "performant
JIT JS improving our ux").

Result: the work that every Foafnaut engine does before the first script of its first page runs
went from 1,537 to 988 million instructions (−36%), in the program below. Two parts:

- module initialization of the engine library: 597 to 184 million;
- BubblePopJS's realm decode (`LeanJS.prepare`): 875 to 742 million.

The page numbers (start turn of a page with scripts) are in section 4.

## 1. Where it was found

A profile of `pages/spinal-tap-sparql.html` on the Linux rig (engine of `main` `e56d8bdc1`,
`perf record --call-graph dwarf`, window `load` of `tools/engine_time_split.py`): BubblePopJS was
35% of the engine's CPU time at page load. Inside it, `Snapshot.decode` was 16% and the run of the
page's scripts 18% (most of it host calls into the page objects).

## 2. Method

`Harness/RealmDecodeBench.lean` (`lake exe realm-decode-bench 1`): one process loads the engine
modules (their initialization runs) and calls `LeanJS.prepare` once. `LeanJS.prepare` is a closed
value, so Lean keeps it: a second call in the same process costs 0.3 ms. So each engine pays the
decode once, at the start turn of its first page with scripts. Counts are callgrind instructions
of the whole process (`valgrind --tool=callgrind ./realm-decode-bench 1`); wall-clock times on the
4-vCPU VM were too noisy while builds ran.

| Build | total | module initialization | decode |
|---|---|---|---|
| `main` `ae8eb4e09` | 1,536,855,065 | 596,669,487 | 875,043,142 |
| + code compiled at the first call | 1,452,623,093 | 596,665,997 | 793,776,930 |
| + wave and IDNA constants not at start | 1,151,758,237 | 298,428,051 | 791,146,246 |
| + numbers read with no copy of the state | 1,102,392,042 | 298,429,210 | 741,779,253 |
| + Web Audio test constants not at start | 987,830,402 | 183,862,183 | (same) |

## 3. The changes

1. `FunInfo.code` is a `Thunk (Option Code)`. A function's register-machine code is made at its
   first call (`fd.info.code.get` in `vmCallCode` and `callClosure`), not when the realm is
   decoded (`Snapshot.dFunCore`) or a script is resolved (`Resolve`). Most functions of the
   prelude and of a page never run. `Resolve.stats` (`leanjs compile-stats`) still compiles every
   function, with `St.counting`.
2. Lean computes a top-level constant when its module starts. Constants that are functions of
   `Unit` (`(_ : Unit := ())`) are computed at their first use; a closed term inside a function is
   computed once, when first needed (`lean_obj_once`). Changed:
   - `WebAudio.Oscillator.builtinWaveCached` (each built-in wave once; `builtinWaveCached_eq`),
     used by `OscState.new` and `Render.sineWave`; the oscillator test waves (`sineState`, `sawW`,
     `threeW`, `cosState`, `window`). They were 339 million instructions of FFT at every start.
   - The IDNA tables of `WHATWG/URL/Idna.lean`.
   - The constants of `WebAudio/Api.lean` namespace `Tests`: they rendered audio graphs at every
     start (114 million).
3. The snapshot reader: `getNat` reads a number of more than one digit with `natEnd` and `natVal`
   (no `Option` or pair), and keeps the decode state unshared (`(← get).pos`, then `modify`), so
   the state record is updated in place. `getFloat` reads the 64 bits with `readU64` (`UInt64`
   arithmetic; `readU64_eq`: the same as `readNat` modulo 2^64): before, each float went through a
   big `Nat` (`lean_nat_shiftl` and GMP). `natEnd` and `natVal` are tested against `readNat`
   (`#guard` over 0 to 4,999 and large values), not proved; `WasmVM/Tests/LeanJSRealm.lean`
   compares a whole decoded realm with the realm that running the prelude gives.

Checks: Test262 `test/language` verdict lists identical to `main` with the register machine on,
off (`BUBBLEPOP_VM=off`) and tier 1 off (`BUBBLEPOP_TIER1=off`): 5,986 pass, 314 fail, 1 skip.
The library corpus gives the same answers. `JSFuelMono` builds.

Corpus, callgrind instructions, `main` `ae8eb4e09` to this change: acorn (N=1) −1.07%, immutable
(N=1000) −0.23%, lodash (N=1000) −1.57%, marked (N=6) −14.4%, pako (N=32) +0.62%. pako makes many
calls, and each call now reads the code through the `Thunk`.

## 4. Pages

See the comment on issue 471 that links this record: start turn (`leanMs` of the
`native-html-script` record with `cause: start`) of `spinal-tap-sparql.html` and
`foaf-explorer.html`, engines of `main` and of this change, interleaved runs.

## 5. What is left

- The decode still makes one result record for each number read (the `EStateM` monad), and
  decodes every object and function of the realm. Decoding objects or function bodies at their
  first use would remove most of it; it changes the heap's object table.
- Module initialization: 184 million instructions remain, mostly Unicode and layout tables
  (`Unicode.Normalization`, `Segmentation`, `LineBreakData`, `XPath4.Unicode`, `Rendering.Layout`)
  that most pages use.
- In `copies` mode (the default) each tab has its own library copy, so each new tab pays both
  parts once.
