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
- Evidence on the support library (section 5): the load side needs no
  C primitive, only an idiom and its bound lemmas; the store side needs one
  primitive, which halves the kernel time.
- Owner, 2026-10-12: "library yes". Section 6: `L4Factoidal/Prim/Bytes.lean`
  (`ldU64LE`, the `stU64LE` primitive with its Lean reference, the lemmas),
  one C source for native and wasm32, and a differential test that runs on
  both (14,605 pass, 0 fail (out of 14,605) on each). Kernel with the
  primitive: 1.1 to 1.3 times C natively, 2.9 to 3.4 times C in wasm32.
- Section 7 replaces the two ratios above. Both came from errors in the C
  measurement: natively the C kernel paid about 1,100 page faults per run
  (glibc returned its 2 MB buffers to the kernel at each `free`), and under
  node both kernels ran as V8 baseline (Liftoff) code. With the two errors
  removed, the Lean kernel with the primitive is 3.5 to 4.7 times C natively
  and 3.8 to 4.9 times C in wasm32. No cause is specific to wasm32. Of the
  gap, about half is the five 2 MB buffer copies the harness makes before it
  writes; the rest is about 4 times more instructions per row than C.
- Section 8 (owner, "Yes A B"): an append primitive `pushU64LE` removes the
  copies, a fused merge loop removes the tuple per run of equal keys (proved
  equal to the old loop), and a proved bounds test before the merge loop
  removes the bounds test per load. Native: 4.0 to 4.4 times C before, 1.8
  to 1.9 times C after (3.0 ms); wasm32: 4.1 to 4.4 before, 2.3 after;
  instructions per run 32.1 to 21.6 million (C 7.8). Not applied to the
  production `Qlvr.Side.put64`: no gain on the queries, and an inline-C
  primitive cannot run under `#guard`.

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
  `usize-cstore` with `ldU`, `setU`, `setC` (replaced by the library of section 6) and the `USize` loop lemmas
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

## 6. The support library (owner decision, 2026-10-12)

Owner, 2026-10-12, verbatim, on the proposal of section 5: "library yes".
And, the same day: "But should it be actual native C or a wasm build of that
C, or is our normal path to wasm equivalent wrt perf? Our tool must be
portable crossplatform and provably doing same things everywhere."

Answer, by construction: there is one C source. The C of a primitive is the
string in its `@[extern c inline "..."]` attribute; the Lean compiler pastes
it into each call site of the generated `.c` file (seen in
`.lake/build/ir/Harness/PrimBytesTest.c` and `Harness/QlvrKernel.c`). The
native build compiles that file with clang, the wasm build
(`Wasm/build-wasm.sh`, and `tools/lean-wasm-exe.sh` for a single
executable) compiles the same file with emcc. So the normal wasm path IS a
wasm build of that C; there is no second implementation.

### What landed

`L4Factoidal/Prim/Bytes.lean`:

- `ldU64LE d p` (pure Lean): one `USize` test, eight `uget`. Bytes past the
  end read 0. clang -O3: two compares and one `movq`; emcc -O3: one
  `i64.load`. `Codec.Zstd.word64U` now reads through it (`word64U_eq` kept,
  `word64Slow_eq_spec` added); `Harness/QlvrKernel.lean` uses it in place of
  its own `ldU`.
- `stU64LE b p x`: `@[extern c inline]` 8-byte little-endian store. Lean body:
  `stU64LERef b p x`, a separate executable definition (eight `uset`; out of
  bounds or `p + 8` wrapping, `b` unchanged). The kernel's `usize-cstore`
  variant calls `stU64LE` and `usize` calls `stU64LERef`; the harness-only
  `setC` and `setU` are deleted.
- The `USize` loop lemmas moved from the kernel harness:
  `usize_succ_toNat`, `usize_pred_toNat`, `usize_lt_size`, and the window
  lemmas `usize_add_small`, `window_of_test`, `window_lt`, `test_of_window`.

The C expression:

```c
({ lean_object* _l4a = #1; size_t _l4p = #2; uint64_t _l4x = #3;
   if (_l4p + 8 <= lean_sarray_size(_l4a) && _l4p < _l4p + 8) {
     if (!lean_is_exclusive(_l4a)) _l4a = lean_copy_byte_array(_l4a);
     uint8_t* _l4q = lean_sarray_cptr(_l4a) + _l4p;
     _l4q[0] = (uint8_t)_l4x; _l4q[1] = (uint8_t)(_l4x >> 8); /* ... */
     _l4q[7] = (uint8_t)(_l4x >> 56); }
   _l4a; })
```

Compiled (`leanc -O3 -S`, x86-64): two compares, one exclusivity compare,
`movq %rdx, 24(%rax,%rsi)`. Compiled (`emcc -O3 -S`, wasm32): the same tests
in `i32`, one `i64.store 16`. The `setC` of section 3 used `memcpy` and a
`__BYTE_ORDER__` test; this one writes byte `k` as `x >> 8k`, so the byte order
is in the source and the code is correct on a big-endian host (clang there
emits a byte swap and a store, or eight stores).

### What is proved, over the Lean definitions

All in `L4Factoidal.Prim.Bytes`; `#print axioms`: only `propext`,
`Classical.choice`, `Quot.sound`.

- `ldU64LE_eq`: `ldU64LE d p = ldU64LESpec d p.toNat` for every `d`, `p`.
- `size_stU64LE`: the size is preserved.
- `getOr0_stU64LE`: every byte of the result, as a function of `b`, `p`, `x`;
  `getOr0_stU64LE_other` and `getElem_stU64LE_other`: bytes outside
  `[p, p+8)` unchanged; `getOr0_stU64LE_at`: byte `p + k` is byte `k` of `x`;
  `stU64LE_oob`: out of bounds (or wrap), the array is unchanged.
- `ldU64LE_stU64LE`: read after write, `ldU64LE (stU64LE b p x) p = x` when
  `p.toNat + 8 ≤ b.size < USize.size`.
- `u64_of_bytes`: the eight little-endian bytes of `x` reassemble to `x`.
- No theorem assumes `System.Platform.numBits = 64`; where the width matters
  the proof splits on `System.Platform.numBits_eq` (32 or 64). No executable
  code tests against `USize.size`.

### What is trusted, and how it is checked

Trusted: that the C expression computes `stU64LERef`. The four facts it
rests on (byte order, `size_t` and `USize` of equal width so the wrap test
agrees, `lean_sarray_size` equals `ByteArray.usize` for every array that can
be allocated, the copy on a shared array) are in the module header.

Checked by `tests/prim/run.sh`, which runs `l4prim-test`
(`Harness/PrimBytesTest.lean`) natively and, built by
`tools/lean-wasm-exe.sh` from the same generated C, as wasm32 under node.
It compares `stU64LE` and `stU64LERef` byte for byte on 30 array sizes ×
22 positions (0, 1, size-9, size-8, size-7, size-1, size, size+1, six
random, and 2^w-1, 2^w-7, 2^w-8, 2^w-9 where `p + 8` wraps) × 5 values
(0, 2^64-1, 0x0102030405060708, two random), each with an exclusive and a
shared array (the shared original must stay unchanged), plus read after
write and `ldU64LE` against `ldU64LESpec`:

- native (numBits 64): 14,605 pass, 0 fail (out of 14,605);
- wasm32 under node 22 (numBits 32, emcc 6.0.12): 14,605 pass, 0 fail
  (out of 14,605).

The test sees a defect: with the byte order of byte 0 changed and the copy
on a shared array removed, it reported 3,085 fail (out of 14,605).

### Numbers: the q07 kernel, native and wasm32

`tools/qlvr/bench/kernel-targets.py 5 10 KERNELFILE ...`: 5 interleaved
rounds; per round each program runs each implementation 10 times; median
over rounds of the per-round median, and median over rounds of the ratio to
the C kernel (`tools/qlvr/bench/kernel.c`, `-O2`) of the same target. Native:
`l4qlvr-kernel` (Lake build) and gcc 13.3. Wasm32: the same Lean C and the
same `kernel.c`, built with emcc 6.0.12 (`-O3` for Lean, as
`Wasm/build-wasm.sh`; `-O2` for the C), run by node 22. Same input
(`l4qlvr kernel-dump`, 31,250 and 269,625 rows; 13,369 output rows); all
implementations on both targets give checksum 5325009063194286364.

Run 1, 1-minute load 0.74, 0.78, 0.80, 0.81, 0.91:

| Implementation | native ms | native × C | wasm32 ms | wasm32 × C |
| --- | ---: | ---: | ---: | ---: |
| bytes-set (`Nat` indices) | 32.3 | 5.87 | 68.5 | 20.47 |
| usize (`ldU64LE`, `stU64LERef`) | 12.3 | 2.30 | 15.6 | 4.36 |
| usize-cstore (`ldU64LE`, `stU64LE`) | 6.4 | 1.26 | 12.6 | 2.91 |
| C `-O2` | 5.3 | 1 | 3.8 | 1 |

Run 2 (after the gates), load 1.64, 1.54, 1.49, 1.45, 1.42:

| Implementation | native ms | native × C | wasm32 ms | wasm32 × C |
| --- | ---: | ---: | ---: | ---: |
| bytes-set | 32.8 | 6.23 | 66.0 | 16.78 |
| usize | 12.0 | 2.09 | 15.2 | 4.77 |
| usize-cstore | 6.4 | 1.08 | 11.8 | 3.35 |
| C `-O2` | 6.5 | 1 | 4.0 | 1 |

What the numbers say, and what they do not:

- Natively the store primitive halves the kernel time, to 1.1 to 1.3 times C,
  as in section 5.
- In wasm32 the primitive gives 15.2-15.6 to 11.8-12.6 ms (about -20 %), and
  the Lean kernel stays 2.9 to 3.4 times the C kernel compiled by the same
  emcc. The loop of `filterAU` in the wasm object has three `i64.load` and one
  `i64.store` (merged, as natively); the cause of the remaining gap in wasm32
  was not found in this work. Candidates not measured: the allocation and
  copy of the scratch arrays through the Lean runtime (mimalloc in wasm32)
  against `malloc` in the C kernel, and the per-call result tuples
  (section 2).
- The C kernel is faster under node than natively (3.8 to 4.0 against 5.3 to
  6.5 ms); not analysed. (Analysed in section 7: both numbers, and the two
  tables above, are wrong for the C kernel, for two different reasons.)
- On wasm32 the slow path of `ldU64LE` converts `p` to `Nat`
  (`lean_big_usize_to_nat` for `p ≥ 2^31`); it runs only for a read that is not
  inside the array.

### Gates for this change

Worktree of `main` at e0c998b8, 2026-10-12:

- `lake build`: 1,546 jobs, 0 errors.
- `python3 tools/lean-tail-recursion-audit.py --gate`: exit 0 (no new
  allow-list line; the first version of the kernel timing loop sorted with
  `Array.qsort`, which the gate refused; it now uses `Qlvr.mergeSortBy`).
- `tests/prim/run.sh`: native 14,605 pass, 0 fail (out of 14,605); wasm32
  14,605 pass, 0 fail (out of 14,605).
- `tests/qlvr/run.sh`: 39 pass, 0 fail (out of 39); in it zstd-diff 1,860
  pass, 0 fail (out of 1,860 frames), 177 MB/s (not an interleaved
  comparison with the previous decoder).
- `tests/qlvr/kernel.sh`: all eight Lean implementations and the C reference
  give the same checksum.
- `tests/sbm11/run.sh`: 123 pass, 0 fail (out of 123).
- `formal/lean4/Wasm/native-smoke.sh`: 350 pass, 0 fail, 0 xfail (out of 350).
- `tests/known-defects/run.sh`: 13 XFAIL, 0 XPASS, 0 probe errors (out of 13).
- `tests/stack/run.sh --canary`: 57 pass, 0 fail (out of 57).
- `Wasm/build-wasm.sh` (a copy of the work directory, `L4_WASM_NO_INSTALL=1`,
  emcc 6.0.12): both modules link, with `L4Factoidal/Prim/Bytes.c` and the
  changed `Codec/Zstd.c` among the library objects; nothing installed.
- No `sorry`, `native_decide`, user `axiom` or `import Std` in the new or
  changed files.

## 7. Why wasm32 looked slower: two measurement errors, then the real gap

Question (issue 797): why is the Lean kernel (`usize-cstore`) 2.9 to 3.4
times the C kernel in wasm32 under node, but 1.1 to 1.3 times C natively? And
why is the C kernel faster under node (3.8 to 4.0 ms) than natively (5.3 to
6.5 ms)?

Answer: both ratios of section 6 are wrong, for the C side. The native C
kernel paid page faults that the Lean kernel did not pay (H1), and under node
both kernels ran as V8 baseline code (H2). With both errors removed, the Lean
kernel is 3.5 to 4.7 times C on both targets. No cause specific to wasm32 was
found (H3, H4). The gap that stays is the same on both targets (H5).

Method: one hypothesis at a time; each one is a change and an interleaved
A/B run (each round runs every variant once, in the same order; median over
rounds; the 1-minute load before each round is given). Other agents used the
machine: the load was 0.7 to 10.2. Instruction counts (valgrind
`callgrind`, native only) do not change with load; they support the timing
where the load was high. Scripts: `tools/qlvr/bench/kernel-targets.py` and
ad hoc copies of `tools/lean-wasm-exe.sh` with other flags. Input:
`l4qlvr kernel-dump` of q07 (31,250 A rows, 269,625 B rows, 13,369 output
rows). Every variant gave checksum 5325009063194286364.

### H1. The native C kernel pays page faults (confirmed)

The C kernel allocates five buffers per run, four of them 2.16 MB. glibc
serves an allocation above its mmap threshold with `mmap` and returns it to
the kernel at `free`, so every run touches new pages. The Lean runtime
allocates through mimalloc, which keeps freed memory.

Change: glibc tunables `glibc.malloc.mmap_threshold=33554432` and
`glibc.malloc.trim_threshold=1073741824` (no code change).

| Measure | default | tuned |
| --- | ---: | ---: |
| C kernel, minor page faults per process (100 runs) | 114,102 | 4,789 |
| Lean kernel, minor page faults per process (80 runs) | 8,906 | 6,330 |
| C `c-O2` median ms, 7 rounds, load 2.16 to 2.94 | 4.53 | 1.41 (ratio 0.28) |
| Lean `usize-cstore` median ms, same rounds | 6.91 | 6.57 |

Verdict: confirmed. About 1,100 page faults per C run took 3.1 of 4.5 ms.
The Lean kernel does not change. `tools/qlvr/bench/kernel.c` now sets the
two thresholds with `mallopt` when it is built against glibc.

### H2. Under node, both kernels run as Liftoff code (confirmed)

V8 compiles wasm first with Liftoff (baseline) and compiles hot functions
again with TurboFan. TurboFan code is used from the NEXT call of a function;
V8 has no on-stack replacement for wasm. wasm-opt (`emcc -O2`/`-O3` at link)
inlines `run` into `main` in the C kernel (the `.wat` has `main` and no
`run`, also with `__attribute__((noinline))`), and inlines the Lean kernels
into `runKernel` (in a `node --cpu-prof` profile, 37,474 of the samples are
self time of `runKernel`). Both functions are entered once.
`node --trace-wasm-compilation-times` shows TurboFan code for `main` that is
never called again.

Change: node flags. 5 rounds, load 0.74 to 3.90:

| Kernel | default | `--liftoff-only` | `--no-liftoff` (TurboFan only) |
| --- | ---: | ---: | ---: |
| C `c-O2` ms | 4.13 | 4.44 (0.99) | 2.16 (0.56) |
| Lean `usize` ms | 17.23 | 18.91 | 13.96 |
| Lean `usize-cstore` ms | 11.93 | 11.66 | 8.83 |

Verdict: confirmed. node's default equals `--liftoff-only` for both kernels.
Liftoff costs the C kernel more (1.9 times) than the Lean kernel (1.35 times),
so the section 6 ratio in wasm32 was too LOW, not too high. A C build with
`run` marked `noinline` did not change this (3.21 against 3.40 ms, 7 rounds,
load 1.33 to 1.36), because wasm-opt inlines it all the same.
`kernel-targets.py` now runs node with `--no-liftoff` (`KERNEL_NODE_FLAGS`
sets other flags). The same effect can apply to a long first call into the
library module (`Wasm/build-wasm.sh`); that was not measured.

### H3. emcc options (rejected)

What the build already uses: `-O3 -DNDEBUG`, `-sASSERTIONS=0`, no
`SAFE_HEAP`, no stack checks, mimalloc, and bulk memory (the kernel module
has 113 `memory.copy` and 32 `memory.fill`). Changed: the flags of the 14
Lean modules of the kernel program (runtime objects unchanged), TurboFan
only, 9 rounds, load 7.36 to 10.14:

| Lean module flags | `usize-cstore` ms | ratio to `-O3` |
| --- | ---: | ---: |
| `-O3` (as `Wasm/build-wasm.sh`) | 9.40 | 1.00 |
| `-O2` | 11.96 | 0.98 |
| `-O3 -msimd128` | 9.14 | 0.92 |
| `-O3 -flto` (Lean modules only) | 9.17 | 1.01 |

A first run of the same four (7 rounds, load 7.0 to 8.6) gave 1.12, 0.93,
0.95. The C kernel at `-O3` was 1.37 times its `-O2` time. Verdict: no flag
gives a gain that is larger than the noise and repeats. `Wasm/build-wasm.sh`
is not changed.

### H4. 32-bit `USize` boxes `UInt64` values (rejected)

In the generated C (`.lake/build/ir/Harness/QlvrKernel.c`, the same file
for both targets), the specialised hot functions of `usize-cstore` take
`uint64_t` and `size_t` arguments unboxed and contain no `lean_box_uint64`
(`c-audit.py`: `filterBU` box 1, `crossLeftU` box 2, all for the result
tuples, `lean_box_usize`). The loads are `i64.load` in wasm32 (section 6).
Verdict: rejected for this kernel.

### H5. The gap that stays, on both targets

Instruction counts, native, `callgrind`, per run: C `run` 7.8 million;
Lean `usize-cstore` 32.1 million (4.1 times). Lean, by function:

| Function (inclusive) | million instructions per run | Notes |
| --- | ---: | --- |
| `filterBU` | 11.0 | 39 instructions per B row in its own code (all 269,625 rows match); 0.5 of the 11.0 is one `lean_copy_byte_array` (below) |
| `mergeLoopU`, own code | 9.0 | two `ldU64LE` with bounds tests and a fuel counter per step |
| `crossLeftU`, `crossRightU`, and the tuples they return | 9.6 | 13,369 calls per run; each result is a 3-tuple: 3 allocations (`mi_malloc_small`) and 3 frees (`lean_dec_ref_cold`, `mi_free`) |
| `filterAU`, `runEndU`, `sumLoopU` | 1.7 | |
| `scratch` | 0.7 | the buffer copies (below) |
| total (`runUsizeCStore`) | 32.1 | |

Each Lean output buffer starts as a copy of an input column
(`scratch x.b1 (8 * x.nB)`, so that `stU64LE` overwrites). That is five copies
per run, four of 2.16 MB (the compiler shares the two identical `scratch`
calls; the first store then copies the shared array). A copy is few
instructions (`rep movsb`, `memory.copy`) but 10.8 MB of memory traffic.
Change: `c-O2-copies` in `kernel.c`, the C kernel plus the same five copies.
7 rounds, load 8.57 to 10.18:

| | native ms | wasm32 ms (TurboFan) |
| --- | ---: | ---: |
| C `c-O2` | 2.20 | 2.22 |
| C `c-O2-copies` | 4.63 (1.90) | 4.97 (2.24) |
| Lean `usize-cstore` | 7.01 | 9.54 |

Verdict: the copies are about half of the gap on both targets. After them,
Lean is 1.5 times `c-O2-copies` natively and 1.9 times in wasm32.

Final run, `kernel-targets.py 7 10` with both fixes, load 7.78 to 9.63:

| Implementation | native ms | native × C | wasm32 ms | wasm32 × C |
| --- | ---: | ---: | ---: | ---: |
| bytes-set | 32.4 | 14.85 | 46.4 | 17.96 |
| usize | 12.1 | 5.67 | 14.0 | 5.54 |
| usize-cstore | 6.7 | 3.45 | 9.2 | 3.83 |
| C `-O2` | 2.2 | 1 | 2.5 | 1 |
| C `-O2` with the five copies | 3.8 | 2.05 | 4.7 | 1.54 |

### What is still not explained

- In the same rounds the wasm32 ratio is 1.1 to 1.3 times the native ratio
  (3.83 against 3.45 above; 1.9 against 1.5 after the copies). At load 8 to
  10 this is not separated from noise. Not measured: the mimalloc small
  allocation path in wasm32 (40,107 allocations per run, for the tuples of
  `crossLeftU`).

### Next steps (not done; each needs the owner's decision or its own issue)

- Remove the copies: an output buffer that is not a copy of an input. Pure
  Lean has no uninitialised `ByteArray`; a builder primitive (append 8 bytes
  to a `ByteArray` with reserved capacity, `@[extern c inline]` with a Lean
  reference body and a differential test, as `stU64LE`) would remove them.
  Measured value: about half of the gap (H5).
- Remove the tuple allocation per `crossLeftU` call (a Lean change with an
  equality theorem against the present definition).
- The bounds and exclusivity tests per row in `filterBU` (39 against about 10
  instructions per row).

### Gates for this change

No Lean source and no build script changed (`kernel.c`,
`kernel-targets.py`, this record, two skills). Worktree of `main` at
dfcc267a, 2026-10-12: `lake build` 1,546 jobs, 0 errors;
`python3 tools/lean-tail-recursion-audit.py --gate` exit 0;
`tests/prim/run.sh` native 14,605 pass, 0 fail (out of 14,605), wasm32
14,605 pass, 0 fail (out of 14,605); `tests/qlvr/run.sh` 39 pass, 0 fail
(out of 39); `tests/qlvr/kernel.sh`: all implementations, with
`c-O2-copies`, give the same checksum; `Wasm/build-wasm.sh`
(`L4_WASM_NO_INSTALL=1`, a copy of the work directory): both modules link.

## 8. No buffer copies, no tuple per run, no bounds test per load

Owner, 2026-10-12, verbatim: "Yes A B", to two steps of section 7: (A) a
builder primitive that appends 8 bytes, so that the kernel makes no buffer
copies; (B) no tuple allocation per `crossLeftU` call, with a proof that the
new function equals the old, and a look at the bounds test per step of
`mergeLoopU`, removed only with a proof.

### Where the copies and the tuples came from

Generated C of `runUsizeCStore` (`.lake/build/ir/Harness/QlvrKernel.c`):
three calls of `scratch` (`ByteArray.extract`, so
`lean_byte_array_copy_slice`: one copy of `a2`, 250 KB, and one each of `b1`
and `b2`, 2.16 MB), then `lean_inc_ref` of the two `b` buffers, because the
compiler made the two equal `scratch x.b1 (8 * x.nB)` (and the two of
`x.b2`) one object each, given both to `filterBU` and to `mergeLoopU`. The
first `stU64LE` into each shared buffer copies it (`lean_copy_byte_array`):
two more copies of 2.16 MB. Callgrind (native) shows the tuples: under
`mergeLoopU`, 13,369 calls of `crossLeftU` and 40,107 calls of
`lean_dec_ref_cold` per run.

### What changed

`L4Factoidal/Prim/Bytes.lean`:

- `pushU64LE b x`: `@[extern c inline]`, append the eight little-endian bytes
  of `x`. Its Lean body is `pushU64LERef b x`, a separate non-extern
  definition (eight `ByteArray.push`). The C: when `b` is exclusive and has at
  least 8 bytes of spare capacity (`lean_sarray_capacity - lean_sarray_size
  >= 8`, which cannot wrap), eight byte stores `(uint8_t)(x >> 8k)` and
  `m_size += 8`; otherwise eight calls of `lean_byte_array_push`, the runtime
  function that `ByteArray.push` compiles to (it copies a shared array and
  grows the capacity with `lean_sarray_ensure_capacity`). No `realloc`, no
  other runtime function: `lean_is_exclusive`, `lean_sarray_capacity`,
  `lean_sarray_size`, `lean_sarray_cptr` and `lean_to_sarray` are the inline
  functions of `lean.h`.
- `ldU64LEIn d p h`: `ldU64LE` with no bounds test (eight `uget`), for
  `h : p.toNat + 8 ≤ d.usize.toNat`. `le_div8_toNat` and `idx8_window` give
  `h` for row `i < n` of a column after ONE test `n ≤ d.usize / 8` in `USize`.

`Harness/QlvrKernel.lean`, four new variants (all old variants unchanged):

| Variant | Output buffers | Merge loop |
| --- | --- | --- |
| `usize-cstore` (section 6) | `scratch` copies, `stU64LE` | `mergeLoopU` + `crossLeftU` |
| `usize-cstore-flat` | the same | `mergeFlatU` (step B) |
| `usize-cpush` | `emptyWithCapacity`, `pushU64LE` (step A) | `mergeLoopU` + `crossLeftU` |
| `usize-cpush-flat` | the same | `mergeFlatU` |
| `usize-cpush-in` | the same | `mergeFlatIn`: one test, then `mergeFlatP` (no bounds test per load) |

`mergeFlatU` makes the cross product a state of the merge loop: when
`ci < ie` it emits left row `ci` with right rows `cj` to `je`, then returns to
the merge. Every call is a self tail call, so the C is one loop; it allocates
only the result tuple, once. In the push variants each output buffer is
`ByteArray.emptyWithCapacity (8 * n + tag)` with a different `tag`: with equal
expressions the compiler shared them again (four references to one empty
array), and an unused tag parameter did not help (the compiler removed it,
`newBuf___redArg`).

A push variant is correct for every input: a buffer that is too small grows.
The `stU64LE` variants drop rows that do not fit their buffers (here the
output has at most `nB` rows, so none is dropped).

### What is proved

`#print axioms`: `propext`, `Quot.sound`, and for `ldU64LESpec_pushU64LE`
and `ldU64LE_pushU64LE` also `Classical.choice`. No `sorry`,
`native_decide`, user axiom, `import Std` or raised heartbeats.

- Over the reference of `pushU64LE` (`Prim.Bytes`): `data_pushU64LE` (the
  bytes are `b.data ++ u64Bytes x`), `size_pushU64LE` (size + 8),
  `getOr0_pushU64LE_old` (old bytes unchanged), `getOr0_pushU64LE_new` (byte
  `b.size + k` is byte `k` of `x`), `getOr0_pushU64LE_past`,
  `ldU64LESpec_pushU64LE` (`ldU64LESpec` at the old size is `x`, no
  hypothesis) and `ldU64LE_pushU64LE` (the same through `ldU64LE` at a
  `USize` position equal to the old size).
- `ldU64LE_eq_in`: `ldU64LE d p = ldU64LEIn d p h`; `test_of_usize_window`,
  `le_div8_toNat`, `idx8_window`. Each holds for `numBits` 32 and 64.
- Step B (`QlvrKernel`): `mergeFlatU_spec` (in any state, `mergeFlatU` equals
  the rest of `crossRightU` for row `ci`, then `crossLeftU` from `ci + 1`,
  then `mergeLoopU`; by `fun_induction`), `mergeFlatU_eq` (from the start
  state, `mergeFlatU = mergeLoopU`, the old definition, which stays as the
  reference), for every store function `st`.
- Bounds: `runEndU_le` (`runEndU` does not pass `n`), `mergeFlatP_eq`
  (`mergeFlatP = mergeFlatU` under the column hypotheses and the invariant
  `je ≤ nb`), `mergeFlatIn_eq` (`mergeFlatIn = mergeLoopU` from the start
  state, whether its one test passes or not).

Not proved: that `runUsizeCPush` equals `runUsizeCStore` (different buffers;
the checksum comparison of `tests/qlvr/kernel.sh` checks it on q07).
`@[csimp]` was not used for step B: `mergeFlatU` is a separate function with
more arguments, and the variants call it directly.

### What is trusted, and how it is checked

Trusted: the C of `pushU64LE` computes `pushU64LERef`. The facts it rests
on: byte `k` is written as `x >> 8k` (byte order in the source); the fast-path
test `capacity - size >= 8` (no wrap, since size ≤ capacity); the size field
update; that `lean_byte_array_push` is the compiled `ByteArray.push` (it is
the `@[extern]` of `ByteArray.push` in Lean 4.33).

`tests/prim/run.sh` (`Harness/PrimBytesTest.lean`) now also compares
`pushU64LE` with `pushU64LERef`: every listed array size (0 to 1000 and 20
random) with capacity equal to the size, 1, 7, 8, 9 and 16 bytes above it, 0
and half the size (growth); five values; exclusive and shared (the shared
original must not change); size + 8 and read back with `ldU64LE`; and chains
of 120 appends from an empty array of capacity 0, 1, 7, 8, 9, 13, 64 and 800
with one intermediate array kept live (shared):

- native (numBits 64): 21,581 pass, 0 fail (out of 21,581);
- wasm32 under node 22 (numBits 32, emcc 6.0.12): 21,581 pass, 0 fail (out
  of 21,581).

Mutation check (native, each change alone, then restored):

| Change to the C of `pushU64LE` | Result |
| --- | --- |
| byte 0 written as `x >> 8` | 1,645 fail (out of 21,581) |
| no exclusivity test | 1,146 fail (out of 21,581) |
| `m_size += 7` | 2,562 fail (out of 21,581) |
| capacity test `>= 1` in place of `>= 8` | segmentation fault (exit 139) |

### Numbers

Instruction counts, native, valgrind callgrind 3.22, `l4qlvr-kernel` built by
Lake, million instructions per kernel run (inclusive, 4 runs divided by 4).
They do not change with load. The C kernel `run` (section 7): 7.8.

| Variant | total | merge loop | `filterBU` | other |
| --- | ---: | ---: | ---: | ---: |
| `usize-cstore` | 32.1 | 19.3 | 11.0 | 1.8 |
| `usize-cstore-flat` | 27.9 | 15.1 | 11.0 | 1.8 |
| `usize-cpush` | 32.9 | 19.5 | 12.4 | 1.0 |
| `usize-cpush-flat` | 29.7 | 16.3 | 12.4 | 1.0 |
| `usize-cpush-in` | 21.6 | 8.2 | 12.4 | 1.0 |

- Step B removes 4.2 million instructions per run and all 40,107 frees in the
  merge loop (`lean_dec_ref_cold` under `mergeFlatU`: 0 calls).
- Step A adds 0.8 million instructions (the append tests the capacity and
  writes the size field; `filterBU` 11.0 to 12.4) and removes the copies,
  which are few instructions (`rep movsb`) and 10.8 MB of memory traffic per
  run: the gain is in time, not in instructions.
- The proved bounds removes 8.1 million instructions from the merge loop.
  The slow paths of `ldU64LE` (a call of `ldU64LESpec` and a `lean_dec`) left
  the loop. In the disassembly before the change, the loop (17 arguments)
  kept most of its state in stack slots; the instruction count of the
  change is measured, its split into tests and spills is not.

Time, `tools/qlvr/bench/kernel-targets.py 9 10`: interleaved, 9 rounds, 10
runs per implementation per round, median over rounds; native gcc 13.3 `-O2`
C with the glibc thresholds of section 7; wasm32 emcc 6.0.12, node 22
`--no-liftoff`. Other agents used the machine.

Run 1, 1-minute load 2.13 to 2.25:

| Implementation | native ms | native × C | wasm32 ms | wasm32 × C |
| --- | ---: | ---: | ---: | ---: |
| `usize-cstore` | 6.8 | 4.39 | 8.7 | 4.08 |
| `usize-cstore-flat` | 5.3 | 3.41 | 8.0 | 3.58 |
| `usize-cpush` | 5.0 | 2.94 | 6.9 | 3.45 |
| `usize-cpush-flat` | 3.9 | 2.40 | 5.3 | 2.52 |
| `usize-cpush-in` | 3.0 | 1.88 | 5.0 | 2.29 |
| C `-O2` | 1.6 | 1 | 2.2 | 1 |
| C `-O2` with the five copies | 3.9 | 2.38 | 4.7 | 2.11 |

Run 2 (after the gates), load 3.04 to 5.13:

| Implementation | native ms | native × C | wasm32 ms | wasm32 × C |
| --- | ---: | ---: | ---: | ---: |
| `usize-cstore` | 6.6 | 4.04 | 10.1 | 4.42 |
| `usize-cstore-flat` | 5.4 | 3.17 | 8.2 | 3.85 |
| `usize-cpush` | 4.7 | 2.92 | 6.9 | 3.16 |
| `usize-cpush-flat` | 4.1 | 2.48 | 5.9 | 2.57 |
| `usize-cpush-in` | 3.0 | 1.83 | 5.4 | 2.34 |
| C `-O2` | 1.6 | 1 | 2.4 | 1 |
| C `-O2` with the five copies | 3.7 | 2.54 | 4.8 | 1.90 |

Noise: between the two runs, the implementations that did not change moved
by 1 to 12 % (native `lean-native` 13.2 and 14.8 ms, wasm32 `lean-usize` 14.3
and 15.6 ms). A difference smaller than that is not claimed.

All implementations on both targets give checksum 5325009063194286364.

What the numbers say:

- Natively the three steps together take the kernel from 4.0 to 4.4 times C
  to 1.8 to 1.9 times C (6.6 to 6.8 ms to 3.0 ms), in both runs. Each step
  alone (step B: `cstore` to `cstore-flat`; step A: `cstore` to `cpush`; the
  proved bounds: `cpush-flat` to `cpush-in`) is 18 % or more, larger than
  the noise, in both runs.
- In wasm32: 4.1 to 4.4 times C to 2.3 times C (8.7 to 10.1 ms to 5.0 to
  5.4 ms). Step A is larger than the noise in both runs (21 and 32 %).
  Step B on top of step A is too (6.9 to 5.3 and 5.9 ms); step B alone is in
  run 2 (10.1 to 8.2 ms), not in run 1 (8.7 to 8.0 ms). The proved bounds
  gives 5.3 to 5.0 and 5.9 to 5.4 ms (6 to 8 %), not separated from the
  noise. Why it gives less in wasm32 than natively was not analysed.
- The instruction counts agree with the native times for steps B and the
  proved bounds. For step A they do not move (the copies are memory traffic);
  the C kernel with the same five copies (`c-O2-copies`) costs 2.1 to 2.3
  ms more than `c-O2` natively, close to the 1.8 to 1.9 ms that step A
  saves.

### Production paths

- `Qlvr.Side.put64` (append 8 bytes, used by the joins of `Qlvr.Bgp`, by
  `Qlvr.Query` and by `Storage/Sbm11/IdQuery`) is the same eight
  `ByteArray.push` as `pushU64LERef`, so `@[csimp] put64 = pushU64LE` is
  `rfl`. Measured with `tools/qlvr/bench/compare.py 7` (before and after
  binaries, load 5.1 to 7.6): q07 warm 112.1 against 125.5 ms (median ratio
  1.02), q10 1.00, q16 0.97, zstd 1.05; the kernel variants that do not call
  `put64` moved by 0.92 to 1.13 (the noise). Only `lean-current` (the old
  scan with `selectRows`) gained (0.77). No query gain is larger than the
  noise, so the change is NOT applied. It also breaks the build: an
  `@[extern c inline]` primitive has no symbol that the interpreter can call,
  so the `#guard`s of `Qlvr/Side.lean` and `Qlvr/MergeTheorems.lean`, which
  evaluate code that reaches `put64`, fail ("Could not find native
  implementation of external declaration"). They were disabled only for the
  measurement build.
- `Storage/Sbm11/FrameWords.put64` is the same eight pushes. Not changed (the
  SBM11 files belong to other work in progress); the `#guard` limit above
  applies there too.
- `Codec/Zstd`: the decoder writes literal and match bytes, not 8-byte
  values; steps A and B do not apply. Not measured.

### Gates for this change

Worktree of `main` at 26ee727f, 2026-10-12:

- `lake build` (whole library and executables): 1,546 jobs, 0 errors.
- `python3 tools/lean-tail-recursion-audit.py --gate`: exit 0 (no new
  allow-list line; the new loops are self tail calls).
- `tests/prim/run.sh`: native 21,581 pass, 0 fail (out of 21,581); wasm32
  21,581 pass, 0 fail (out of 21,581).
- `tests/qlvr/run.sh`: 39 pass, 0 fail (out of 39); queries 21 pass, 0 fail,
  0 refused (out of 21); zstd-diff 1,860 pass, 0 fail (out of 1,860 frames).
- `tests/qlvr/kernel.sh`: all twelve Lean implementations and the three C
  ones give the same checksum.
- `tests/sbm11/run.sh`: 123 pass, 0 fail (out of 123).
- `formal/lean4/Wasm/native-smoke.sh`: 350 pass, 0 fail, 0 xfail (out of 350).
- `tests/known-defects/run.sh`: 13 XFAIL, 0 XPASS, 0 probe errors (out of 13).
- `tests/stack/run.sh --canary`: 57 pass, 0 fail (out of 57).
- `Wasm/build-wasm.sh` (`L4_WASM_NO_INSTALL=1`, a copy of the work
  directory, emcc 6.0.12): both modules link, with the changed
  `L4Factoidal/Prim/Bytes.c` among the library objects; nothing installed.
- `#print axioms` on the 18 new theorems: `propext`, `Quot.sound`, and
  `Classical.choice` for two (listed above). No `sorry`, `native_decide`,
  user `axiom`, `import Std`, `partial`, `unsafe` or raised heartbeats in the
  diff.
- The production files (`Qlvr/Side.lean`, `Qlvr/MergeTheorems.lean`) are
  unchanged; the `@[csimp]` measurement build was reverted.

### Still open

- `filterBU` was the largest part: 12.4 of 21.6 million instructions, 46
  per B row (C about 10). Section 9 repairs it (7.8 million, 29 per row).
- The ratio in wasm32 stays above the native one (2.3 against 1.9 times C).
- Code that a `#guard` evaluates cannot call an `@[extern c inline]`
  primitive. A primitive for a production path needs its checks as compiled
  tests, or a form the interpreter can run.

## 9. The scan filter: loads proved in bounds, loads as one primitive (2026-10-22)

Issue: https://github.com/danbri/factoidal/issues/797; OKR batch 3 KR 1.3
(https://github.com/danbri/factoidal/issues/875). Target: Lean kernel at most
2 times the C kernel in callgrind instructions (a goal; owner, 2026-10-12:
"some lean overhead may be unavoidable").

### What was found

In `filterBU` (all 269,625 B rows match) the key compare was one `cmp` with a
memory operand, but each pushed column value was loaded as eight `movzbl`,
shifted, or-ed, and stored as separate pieces. The cause is the shape of
`pushU64LE`: its fast path stores the value, its slow path calls
`lean_byte_array_push` once for each byte of the same value. The value is
therefore used both whole and in pieces on two paths, and clang did not merge
its eight byte loads into one 8-byte load (it merged the loads of the key
compare, which has one use). Removing the bounds tests alone made it worse:
27.7 million instructions per run against 21.6, because the bounds tests had
been hiding nothing and the byte loads stayed.

### What changed

- `Prim.Bytes.ldU64LEIn` is now an `@[extern c inline]` primitive: an 8-byte
  `__builtin_memcpy` from the array data (a byte swap on a big-endian host).
  The Lean reference body is `ldU64LEInRef` (the old pure body); `ldU64LEIn`
  equals it by `rfl` (`ldU64LEIn_eq_ref`); `ldU64LE_eq_in` is unchanged in
  statement. The differential test `Harness/PrimBytesTest.lean` compares
  `ldU64LEIn` with `ldU64LEInRef` and with `ldU64LESpec` at every in-bounds
  position of every case.
- The fast path of `pushU64LE` stores with an 8-byte `__builtin_memcpy`
  (byte stores on a big-endian host) and its slow path first copies the value
  to an 8-byte local, then pushes the local's bytes. Same meaning
  (`pushU64LERef`); the existing push differential cases cover both paths.
- `Harness/QlvrKernel.lean`: `filterBP` and `filterAP` (loads `ldU64LEIn`
  with the proofs `8 * n <= c.usize`), callers `filterBIn` and `filterAIn`
  (one `USize` test before the loop, else the tested loop), theorems
  `filterBP_eq`, `filterAP_eq`, `filterBIn_eq`, `filterAIn_eq` (equal to
  `filterBU` and `filterAU`; `#print axioms`: `propext`, `Quot.sound`). New
  kernel variant `usize-cpush-filt` (`usize-cpush-in` with both callers).

### Numbers

Callgrind 3.22, native, `l4qlvr-kernel` built by Lake, million instructions
per kernel run (2 runs, inclusive). C `run`: 7.8 (section 7).

| Variant | total | merge loop | `filterBU`/`filterBP` | filterA | ratio to C |
| --- | ---: | ---: | ---: | ---: | ---: |
| `usize-cpush-in` (before) | 21.6 | 8.2 | 12.4 | 0.4 | 2.77 |
| `usize-cpush-filt` (after) | 16.5 | 8.1 | 7.8 | 0.4 | 2.11 |

`filterBP`: 29 instructions per B row (46 before; C about 10). Wall time,
native, 20 runs, load average 3.4 to 4.1 (not comparable with section 7):
`usize-cpush-in` 1.6 ms, `usize-cpush-filt` 1.4 to 1.5 ms, C 0.84 to 0.91 ms
(median).

### Remaining cost: 2.11 times C, above the target 2

Per matching row, `filterBP` runs: loop test and increment 4, key compare 2,
and for each of the two output columns one 8-byte load, the exclusivity test
(`rc == 1`), the capacity test (load size and capacity, subtract, compare), the
store, and the size-field update: about 11 each. C writes one store and one
pointer increment for each column.

- The exclusivity test and the capacity test of each push are required by the
  semantics of `ByteArray` in Lean (a value that a second reference may share
  is copied before a write; a full buffer grows). They cannot be hoisted out
  of the loop by a Lean proof, because exclusivity is a run-time property.
  Cost: about 16 of the 29 instructions per row.
- The merge loop (8.1 million) is unchanged by this change. Its remaining
  tests are the loop tests, the push tests of its two output columns, and the
  `runEndU` calls (107,000, 2.9 million).
- A path under 2.0 needs one of: a push that tests exclusivity and capacity
  once for a block of rows (a new primitive `reserve n` with a Lean
  reference, and a proof that the loop writes at most `n` rows); or writing
  both columns from one scan with one exclusivity test for each. Not done;
  not opened as an issue because 2.11 is within the "some Lean overhead may be
  unavoidable" statement; the owner may open one.

### Gates for this change

`lake build` (whole library, 1,868 jobs, 0 errors); `tests/qlvr/run.sh`: 39
pass, 0 fail (out of 39); `tests/qlvr/kernel.sh`: all implementations agree;
`tests/prim/run.sh`: native 24,896 pass, 0 fail (out of 24,896), wasm32 24,896
pass, 0 fail (out of 24,896); `tools/lean-tail-recursion-audit.py --gate`,
`tools/lean-unbuilt-modules.py --gate`, `tools/lean-registry-audit.py --gate`,
`tools/lean-csimp-reach.py --gate`: exit 0. No `sorry`, `axiom`,
`native_decide`, `partial` or raised heartbeats in the diff.

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
# section 7
tools/lean-wasm-exe.sh Harness.QlvrKernelBench OUT/l4qlvr-kernel.js
cc -O2 -o OUT/kernel-c tools/qlvr/bench/kernel.c
emcc -O2 tools/qlvr/bench/kernel.c -o OUT/kernel-c.js -sALLOW_MEMORY_GROWTH=1 -sENVIRONMENT=node -sNODERAWFS=1 -sEXIT_RUNTIME=1
python3 -I tools/qlvr/bench/kernel-targets.py 7 10 KERNELFILE native-lean=formal/lean4/.lake/build/bin/l4qlvr-kernel native-c=OUT/kernel-c wasm32-lean=OUT/l4qlvr-kernel.js wasm32-c=OUT/kernel-c.js
node --liftoff-only OUT/kernel-c.js KERNELFILE 10      # against --no-liftoff and no flag
valgrind --tool=callgrind formal/lean4/.lake/build/bin/l4qlvr-kernel KERNELFILE 2; callgrind_annotate --inclusive=yes --tree=calling callgrind.out.*
```
