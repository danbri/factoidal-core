# Lean to C: what the compiler pipeline gives, what the generated C costs

Tracking: https://github.com/danbri/factoidal/issues/797. Earlier record:
[2026-10-11-qlvr-performance.md](2026-10-11-qlvr-performance.md) (the q07
kernel, the zstd decoder against libzstd). Skill section:
[`lean4-performance`, "Idioms that compile to tight C"](../../skills/lean4-performance/SKILL.md).

Owner, 2026-10-12, verbatim: "Yes work on all these optimizations at the C
level (including associated lean idioms, patterns, supporting libraries,
proofs) and anything about the lean to c pipeline that might help". Scope
change the same day, verbatim: "Do not rush into support library until we are
sure it worth trying". This record therefore covers the pipeline experiments
(item 1), the audit of the generated C (item 2), in-place fixes that keep
the output identical, and the evidence for and against a support library
(items 3 and 4 not built).

## Result

- C compiler options alone give no gain that these measurements can
  separate from noise on the kernel and the three queries; on the zstd decoder
  they give +11 to +12 % (LTO, `-march=native`, PGO). A Lean change in the
  decoder (no new library, no C) gives +26 % in the same runs.
- The generated C of the hot loops spends its work on `Nat` index arithmetic,
  boxed-index byte reads and reference-count tests, never on the algorithm.
  With `USize` indices and `ByteArray.uget`, pure Lean removes all of them:
  eight `uget` at `p + k` compile (clang -O3) to ONE 8-byte load.
- The q07 kernel (same algorithm, same input): `bytes-set` (Nat indices)
  31.4 ms; `usize` (pure Lean, `USize` indices) 11.3 ms; `usize-cstore` (the
  same, with one inline-C 8-byte store in place of eight `uset`) 5.8 ms; C
  `-O2` 4.3 to 8.8 ms in the same rounds. Per round, `usize` is 1.5 to 2.5
  times C (median 1.96) and `usize-cstore` 0.8 to 1.3 times C (median 1.16).
- Evidence on the support library (end of this record): the load side needs no
  C primitive, only an idiom and its bound lemmas; the store side needs one
  primitive, which halves the kernel time.

## Method and machine

- Machine: linux x86_64, 4 vCPU Intel Xeon at 2.10 GHz, Lean 4.33.1 (bundled
  clang 22.1.4, lld), system clang 18.1.3 for the PGO builds, gcc 13.3.0 for
  the C kernel (`-O2`). Three agent sessions shared the machine: the 1-minute
  load average was 2.0 to 5.3 during the runs, never below 1.5. Every
  comparison is therefore interleaved: each round runs every binary once in
  the same order, and the table gives the median over 5 rounds and, in
  brackets, the median over rounds of the ratio to the baseline of the same
  round. Absolute times are 1.5 to 2 times the 2026-10-11 record (which ran
  at a lower load); only ratios within a table are comparable.
- `tools/qlvr/bench/pipeline.sh OUT VARIANT` rebuilds `l4qlvr` from the C that
  Lake generated (`.lake/build/ir`) and the Lake link response file, with
  other compiler options; nothing under `.lake` changes. The `o3` variant
  reproduces the Lake binary byte size exactly (7,644,840 bytes).
- `tools/qlvr/bench/compare.py ROUNDS INDEXDIR KERNELFILE NAME=BIN...` runs
  the interleaved rounds: `l4qlvr kernel FILE 10` (every Lean kernel
  implementation, median of 10), `l4qlvr zstd-diff` (Lean decoder MB/s, with
  the 1,860-frame differential), and `l4qlvr query --repeat 10` for q07, q10,
  q16 (median warm execution).
- `tools/qlvr/bench/c-audit.py FILE.c NAME` counts, in the body of a generated
  C function, the call sites of each runtime category (`Nat` operations,
  reference counts, boxing, allocation, boxed-index array reads, unboxed
  reads, `push`, calls). A loop compiled to `goto _start` runs its body once
  per iteration, so the counts are per iteration over both branches.
- Assembly: `leanc -O3 -DNDEBUG -S` of a small file with the same
  definitions.

## 1. Pipeline experiments

Variants (all from the same generated C; the engine code of `main`):

| Variant | What changes |
| --- | --- |
| o3 | bundled clang, the Lake options (`-O3 -DNDEBUG`); the baseline |
| o2 | bundled clang, `-O2` |
| native | bundled clang, `-O3 -march=native` (this host only; not usable for release binaries) |
| lto | bundled clang, `-O3 -flto=thin`, linked by lld with `-flto=thin` |
| o3-c18 | system clang 18, `-O3` (baseline for the PGO variant) |
| pgo-c18 | system clang 18, `-O3 -fprofile-instr-use`, trained on the kernel, zstd-diff and q07/q10/q16 |
| lean-fix | bundled clang, `-O3`: the Lean change of section 3 (not a pipeline option; for comparison) |

5 rounds, load 2.41, 3.48, 5.26, 3.19, 2.37 (`compare.py`):

| Measure | o3 | lean-fix | o2 | native | lto | o3-c18 | pgo-c18 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| kernel production ms | 16.4 | 14.8 (0.90) | 17.2 (1.06) | 16.9 (1.00) | 15.8 (0.92) | 16.8 (1.00) | 17.0 (1.04) |
| kernel bytes-set ms | 31.4 | 31.8 (0.98) | 30.0 (0.98) | 32.1 (0.99) | 33.2 (1.07) | 32.9 (1.03) | 41.6 (1.30) |
| kernel usize ms | 11.3 | 11.6 (1.11) | 11.5 (1.14) | 11.8 (1.03) | 11.5 (1.10) | 12.1 (1.16) | 13.2 (1.31) |
| kernel usize-cstore ms | 5.8 | 5.3 (0.79) | 5.0 (0.79) | 5.9 (0.93) | 5.8 (0.98) | 6.5 (1.10) | 6.5 (1.12) |
| zstd MB/s (higher is better) | 148 | 182 (1.26) | 149 (1.01) | 154 (1.11) | 170 (1.12) | 148 (0.92) | 162 (1.11) |
| q07 warm ms | 138.0 | 124.4 (0.88) | 134.6 (0.94) | 137.0 (0.96) | 133.8 (0.98) | 140.7 (0.97) | 143.6 (0.95) |
| q10 warm ms | 40.6 | 37.3 (0.88) | 49.0 (1.21) | 41.4 (0.97) | 38.4 (0.92) | 45.7 (1.09) | 43.0 (1.01) |
| q16 warm ms | 170.6 | 178.3 (1.00) | 183.6 (1.03) | 174.0 (1.00) | 158.8 (0.92) | 203.5 (1.18) | 176.2 (1.03) |

(The kernel rows of `lean-fix` measure the same kernel code as `o3`: they
show the noise, about ±10 to 20 % per ratio at these loads.)

What the pipeline cannot reach:

- LTO and PGO act on the generated C only. The Lean runtime (`libleanrt.a`,
  `libInit.a`) is machine code in the toolchain, so `lean_byte_array_push`,
  `lean_byte_array_copy_slice`, `lean_nat_big_*` and the allocator stay
  out-of-line calls. `lean_byte_array_push` alone is 14 % of the zstd decoder's
  self time after section 3. LTO over the runtime needs the runtime rebuilt as
  bitcode from the Lean source (the wasm build already rebuilds it for
  wasm32); not tried.
- The bundled clang has no profile runtime (`libclang_rt.profile`), so PGO
  needs another compiler (here clang 18 with `libclang-rt-18-dev`) and a
  second baseline; the instrumented binary must be linked with
  `-Wl,-u,__llvm_profile_runtime`, or it writes no profile.
- `-march=native` gives a binary for this CPU only.

Lean compiler options in this toolchain (`Lean/Compiler/LCNF/ConfigOptions.lean`,
`Lean/Compiler/Options.lean`): `compiler.small` (inline threshold, default
1), `compiler.maxRecInline`, `compiler.maxRecInlineIfReduce`,
`compiler.extract_closed`, `compiler.maxRecSpecialize`, `compiler.reuse`,
`compiler.ignoreBorrowAnnotation`; attributes `@[inline]`, `@[specialize]`,
`@[noinline]`, `@[always_inline]`, `@[extern c inline "..."]`. Measured here:
`@[specialize]` on loops that take the store function as an argument (the
kernel `usize` loops): the specialised copies contain no closure call
(`lean_apply_*` absent, `c-audit.py`). The `compiler.*` options were not
measured: none of them changes the costs that the audit finds (`Nat` index
arithmetic, boxed-index reads, out-of-line `push`), which come from the types
in the source.

## 2. Audit of the generated C

Counts are call sites in the body of one loop iteration (both branches),
from `c-audit.py` on `.lake/build/ir`:

| Loop | nat | rc | box | alloc | boxed-index read | unboxed read | push |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| kernel `filterAS` (bytes-set: `Nat` index, `ld64`, `set64`) | 69 | 39 | 0 | 1 | 24 | 0 | 0 |
| kernel `filterAU`, `usize` (`USize` index, `ldU`, `setU`), first version (`set1` tested `i.toNat < a.size`) | 16 | 8 | 1 | 1 | 0 | 24 | 0 |
| kernel `filterAU`, `usize` (`set1` tests `i < a.usize`) | 0 | 0 | 1 | 1 | 0 | 24 | 0 |
| kernel `filterAU`, `usize-cstore` | 0 | 0 | 1 | 2 | 0 | 24 | 0 |
| kernel `runEnd` / `runEndU` | 21 / 0 | 11 / 0 | 0 / 0 | 0 / 0 | 8 / 0 | 0 / 8 | 0 |
| kernel `sumLoop` / `sumLoopU` | 35 / 0 | 20 / 0 | 0 / 0 | 0 / 0 | 16 / 0 | 0 / 16 | 0 |
| zstd `seqLoop`, before / after | 152 / 62 | 155 / 105 | 0 / 0 | 3 / 3 | 70 / 22 | 0 / 48 | 0 / 0 |
| zstd `pushCopy` (per byte) / `pushCopyU` | 6 / 0 | 5 / 0 | 0 / 0 | 0 / 0 | 1 / 0 | 0 / 1 | 1 / 1 |
| zstd `hufStreamLoop` (not changed) | 61 | 41 | 0 | 1 | 18 | 0 | 1 |
| Bgp `mergeJoin` main loop (`for` in `Id.run`, not changed) | 44 | 48 | 4 | 16 | 18 | 0 | 0 |

The one `alloc` and `box` left in the `USize` loops build the result pair
at the loop exit, not per row.

### What each cost is, in the C

A `Nat` byte position. `ld64 c p` in `filterAS` (bytes-set) compiles, per
byte, to:

```c
v___x_1002_ = lean_unsigned_to_nat(1u);
v___x_1003_ = lean_nat_add(v_p_873_, v___x_1002_);   /* scalar test, add, overflow test, box */
v___x_1004_ = lean_byte_array_fget(v_c0_829_, v___x_1003_); /* unbox the index */
lean_dec(v___x_1003_);                               /* scalar test */
v___x_1005_ = lean_uint8_to_uint64(v___x_1004_);
```

eight times per Id, plus `lean_nat_mul` for `8 * i`, a boxed
`lean_byte_array_size` and `lean_nat_dec_le` for the bounds test.

A `USize` position with `uget` (`ldU` in `Harness/QlvrKernel.lean`, the
same shape as `Codec.Zstd.word64U`):

```c
v___x_13_ = lean_usize_add(v_p_2_, v___x_12_);
v___x_14_ = lean_byte_array_uget(v_d_1_, v___x_13_);
```

and clang -O3 merges the eight reads and shifts into one load:

```asm
l_ldU:
	xorl	%eax, %eax
	cmpq	$-9, %rsi          # p + 8 does not wrap
	ja	.LBB0_3
	leaq	8(%rsi), %rcx
	cmpq	8(%rdi), %rcx      # p + 8 <= size
	ja	.LBB0_3
	movq	24(%rdi,%rsi), %rax
.LBB0_3:
	retq
```

`word64U` (zstd, `UInt64` position, one test in `UInt64`) compiles to the
same fast path: six instructions and one `movq`.

Stores. Eight `ByteArray.uset` (pure Lean `setU`) cannot be merged: each
`uset` tests `lean_is_exclusive` and may copy, and clang cannot prove that a
byte store does not change the reference count it reads next (a `uint8_t`
store may alias any object). The function compiles to 389 instructions. The
inline-C store `setC` (harness only) compiles to:

```asm
	movq	%rsi, %rcx
	subq	$-8, %rcx          # p + 8 does not wrap
	jae	.LBB7_5
	cmpq	8(%rax), %rcx      # p + 8 <= size
	ja	.LBB7_5
	cmpl	$1, (%rax)         # exclusive
	je	.LBB7_4
	callq	lean_copy_byte_array@PLT
.LBB7_4:
	movq	%rdx, 24(%rax,%rsi)
```

A big-number constant. The first version of `copyShort` tested
`s + k < USize.size`. On a 64-bit host `USize.size` is 2^64, which is not
a small `Nat`: every match then called `lean_nat_big_lt`, and `__gmpz_add`
appeared in the profile (0.8 % and 0.5 %). The bound is now `copyBound`
(2^30, small on 32-bit and 64-bit hosts) with `copyBound_le : copyBound ≤
USize.size`.

A `for` loop with several `let mut` variables in `Id.run` (Bgp
`mergeJoin`). The state is a nested `MProd`; each iteration takes it apart
(three `lean_is_exclusive` tests, `lean_ctor_get`, reuse of the cell or
`lean_alloc_ctor` when it is shared) and builds it again. Each inner
`for x in [i:ie]` allocates its `Std.Range`. The `Nat` row indices and the
`word64` reads at `Nat` positions add the costs of the first excerpt.

A tuple result from an inner loop. `crossLeftU` calls `crossRightU` once
per left row of a run; the `(ByteArray × ByteArray × USize)` result costs two
`lean_alloc_ctor` and one `lean_box_usize` per call, and seven
reference-count operations to take it apart.

## 3. Changes made, outputs identical

- `L4Factoidal/Codec/Zstd.lean`:
  - `word64U d q` (`UInt64` position, one `UInt64` test, eight `uget`) with
    `word64U_eq : word64U d q = word64 d q.toNat` for every `d` and `q`;
    `bitsAtU` reads through it, `bitsAtU_eq` restates the previous
    definition.
  - `pushCopyU` (`USize` counters, `uget` read) with `pushCopyU_eq`
    (equal to `pushCopy` when the counts fit in `USize`), and `copyShort`
    (one test against `copyBound` per match, then `pushCopyU`, else
    `pushCopy`) with `copyShort_eq : copyShort s k out = pushCopy s k 0 out`
    for every argument. `seqLoop` calls `copyShort`; by the two theorems its
    value is unchanged.
  - Measured: zstd-diff 1,860 pass, 0 fail (out of 1,860); 182 against 148
    MB/s (ratio 1.26 over 5 interleaved rounds). q07 warm 0.88, q10 0.88,
    q16 1.00 (inside the noise).
- `Harness/QlvrKernel.lean`: the kernel implementations `usize` and
  `usize-cstore` with `ldU`, `setU`, `setC` and the `USize` loop lemmas
  (`usize_succ_toNat`, `usize_pred_toNat`, `ldU_bound`, `usize_lt_size`).
  `setC` is an `@[extern c inline]` 8-byte store whose Lean body is `setU`;
  it exists only in this harness, to measure what a store primitive gives,
  and the checksum comparison of `l4qlvr kernel` and `tests/qlvr/kernel.sh`
  is its differential test. Harness units are not in the wasm module
  (`Wasm/build-wasm.sh` skips `Harness_*`).
- New theorems use only `propext`, `Classical.choice` and `Quot.sound`
  (`#print axioms`, section "Gates").

Not changed, with the measured cost that remains (zstd self time after the
change, `perf record` of `zstd-diff`): `seqLoop` 37 % (thirteen table reads
per sequence through `Array Nat` with a boxed index and `lean_uint64_of_nat`;
`Fse` tables as `ByteArray`/`UInt16` columns would remove them),
`lean_byte_array_push` 14 % (out of line; writing into the output reserved
from the frame size with `uset` would remove it, but the frame checks use
`out.size`), `hufStreamLoop` 6 % (`Nat` bit positions, as `seqLoop` before),
`copy_slice` 6 %. Bgp `mergeJoin` and `gather` keep `Nat` indices and the
`for` state (13 % of q07 in the 2026-10-11 profile).

## 4. QLever for the same join

Not measured again: the QLever server runs in Docker and the Docker daemon
was not running on this machine; starting it was not permitted in this
session. The 2026-10-11 record measured QLever's `computeResult` for q07 at
19 to 27 ms (cache cleared), and the C kernel of the join at 2.05 to 2.38 ms
at a lower load. The kernel is the scan-filter and merge join of q07 only;
QLever's q07 time includes its block decompression (libzstd) and the other
two patterns. In q07, the Lean decoder is 52 of 75 ms (2026-10-11), so the
join kernel speedups in this record act on about one sixth of the Lean q07
time.

## 5. The case for and against a support library

What the missing unboxed column access costs, per iteration, in the kernel
(section 2): `filterAS` has 69 `Nat` operations, 39 reference-count tests and
24 boxed-index reads per iteration; with `USize` indices and `uget`, none. Per
8-byte store, pure Lean leaves eight exclusivity tests and eight bounds tests
that clang cannot merge.

Measured, kernel only, same rounds (5 interleaved rounds of the `o3` binary
against the C kernel; load 1.9 to 2.3):

| Kernel | Median ms | Times C (median of per-round ratios) |
| --- | ---: | ---: |
| bytes-set (`Nat` indices) | 32.8 | 6.3 |
| floats (`FloatArray`, one slot per Id) | 9.6 | 1.7 |
| usize (pure Lean, `USize` + `uget` / `uset`) | 11.1 | 2.0 |
| usize-cstore (`usize` + one inline-C 8-byte store) | 5.9 | 1.2 |
| C `-O2` | 5.1 | 1 |

Against what the pipeline options give: no measurable change on the kernel
(section 1), +11 to +12 % on the zstd decoder.

For a library:

- The bound lemmas are the cost of the pure-Lean idiom: `ldU_bound` and
  `word64U_toNat` each took several attempts (USize wrap-around, `2 ^
  numBits` on 32-bit and 64-bit hosts, `ByteArray.usize` as `size %
  2 ^ numBits`). A library states them once.
- A store primitive halves the kernel time (11.1 to 5.9 ms) and brings it
  within about 1.2 times C. This needs `@[extern c inline]` (a trusted C
  expression with a Lean reference body and a differential test), which is
  not in the library today.

Against:

- The loads need no C and no library type: the idiom (`USize` index, one
  `USize` test, eight `uget`) already compiles to one load, and
  `word64U` is in `Codec.Zstd` with its theorem. SBM11 can call it.
- In q07 the join is about 13 % of the warm time and the zstd decoder 70
  to 80 %. A faster column library changes the kernel, not the query, until
  the decoder's `push`, table reads and bit reader are changed.
- Builders that grow geometrically, slices and merge helpers had no
  measurement that asked for them: the kernel writes into buffers of known
  size.

Proposal for the owner's decision: a small module with `ldU`/`word64U`, the
bound lemmas, one 8-byte store (inline C, Lean reference body, differential
test, wasm-checked) and a `USize` loop lemma set; no builders or merge
helpers until a measurement asks for them. Wasm: the new `Codec/Zstd.c`
compiles with `emcc` and the build's flags (`/tmp/l4wasm-build` include
paths); a full wasm build was not run.

## What did not work or was not done

- PGO with the bundled clang: no profile runtime. With clang 18 the first
  instrumented build wrote no profile until the link pulled in
  `__llvm_profile_runtime`.
- `copyShort` with a test against `USize.size`: a big-number comparison per
  match (section 2). Repaired before measurement.
- `set1` with `i.toNat < a.size`: 16 `Nat` operations and 8 reference-count
  tests per kernel iteration. Repaired (`i < a.usize`).
- Not tried: LTO over a bitcode build of the Lean runtime; `compiler.small`
  and the other `compiler.*` options; the `Fse` table and output-buffer
  changes of section 3; QLever timings (section 4).

## Gates

Run on this change (worktree of `main` at dba20147), 2026-10-12:

- `lake build` (whole library and executables): 1,528 jobs, 0 errors.
- `python3 tools/lean-tail-recursion-audit.py --gate`: exit 0 (no new
  allow-list line).
- `tests/qlvr/run.sh`: 39 pass, 0 fail (out of 39); in it, queries 21 pass,
  0 fail, 0 refused (out of 21) and zstd-diff 1,860 pass, 0 fail (out of
  1,860 frames).
- `tests/qlvr/kernel.sh`: all eight Lean implementations and the C reference
  give the same checksum.
- `formal/lean4/Wasm/native-smoke.sh`: 350 pass, 0 fail, 0 xfail (out of 350).
- `tests/known-defects/run.sh`: 13 XFAIL, 0 XPASS, 0 probe errors (out of 13).
- `tests/stack/run.sh --canary`: 57 pass, 0 fail (out of 57).
- `#print axioms`: `word64U_eq`, `bitsAtU_eq`, `ldU_bound`, `usize_lt_size`,
  `usize_succ_toNat`, `usize_pred_toNat`: `propext`, `Quot.sound`;
  `pushCopyU_eq`, `copyShort_eq`: `propext`, `Classical.choice`,
  `Quot.sound`; `copyBound_le`: none.
- Wasm: `emcc` with the flags of `Wasm/build-wasm.sh` compiles the new
  `L4Factoidal/Codec/Zstd.c`; the full wasm build was not run.

## Commands

```
cd formal/lean4 && lake build l4qlvr
tools/qlvr/bench/pipeline.sh /home/user/qlvr-work/perf/pipeline o3      # and o2 native lto o3-c18 pgo-c18
python3 -I tools/qlvr/bench/compare.py 5 /home/user/qlvr-work/instance KERNELFILE o3=.../o3/l4qlvr lto=.../lto/l4qlvr ...
python3 tools/qlvr/bench/c-audit.py formal/lean4/.lake/build/ir/L4Factoidal/Codec/Zstd.c Zstd_seqLoop
formal/lean4/.lake/build/bin/l4qlvr kernel-dump /home/user/qlvr-work/instance KERNELFILE
```
