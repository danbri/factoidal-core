# RV32 Lean runtime constructor alignment audit

Tracking: [factoidal-core #745](https://github.com/danbri/factoidal-core/issues/745).

## Finding and bounded repair

The pinned non-mimalloc allocator has matching allocation/free pointer
arithmetic. It also places small objects four bytes after the allocation
base on RV32. A constructor's UInt64 or Float field can therefore have
four-byte alignment while its C type requires eight. The four constructor
UInt64/double accessors dereference casts to eight-byte-aligned types.
The new generator replaces only those four accesses with `memcpy`,
retaining the object layout, assertions and native byte order. It adds
`<string.h>` and changes no allocator or other accessor.

This is source inspection plus compiler/sanitizer testing. It is not a
proof of the Lean runtime, an executed RV32 allocator test or a zkVM
receipt. The separate real-runtime integration must use the generated
header consistently and execute its own checks.

## Exact source pin

| Item | Value |
| --- | --- |
| Upstream commit | `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` |
| Header | `src/include/lean/lean.h` |
| Pristine SHA-256 | `02af0040283143b264e3a44b06b348b6973ae6037fa8f550701c83dd7a062ace` |
| Generated SHA-256, patch version 1 | `ce5ed3683fd9958e7dc1bbb91fd205f33d32ccebb79304a3b0c7b1ecbffd0231` |
| RV32 compiler | RISC Zero `riscv32-unknown-elf-g++`, GCC 13.2.0 |
| Target flags | `-march=rv32im -mabi=ilp32 -std=c++17 -O2 -DNDEBUG` |
| Runtime configuration | `LEAN_MIMALLOC`, `LEAN_USE_GMP`, `LEAN_MULTI_THREAD` absent |

The [pinned header](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/include/lean/lean.h)
is the source of the line anchors below. The generator refuses a different
whole-file hash, missing/duplicate anchors, an already patched input, and
input/output/manifest aliases, including existing symlinks and hardlinks.
It writes a separate generated copy atomically. Its JSON audit records
the pin, input/output hashes, five edit names and source lines, and hashes
of each replacement fragment. The pristine checkout is not modified.

## Allocation and deallocation audit

| Path | Allocation | Deallocation | Source anchors and finding |
| --- | --- | --- | --- |
| Small constructors, thunks, external objects | `malloc(sizeof(size_t) + sz)`, store size prefix, return one `size_t` after allocation base | Subtract one `size_t`, then `free_sized` on that original base | `lean.h:482–498`, `544–554`; matching pointer arithmetic |
| Arrays, scalar arrays, strings, closures | `lean_alloc_object`: direct `malloc(sz)`, no prefix | `lean_dealloc`: direct `free_sized(o, sz)` | `runtime/object.cpp:262–277`, `354–373`; matching pointer arithmetic |
| MPZ, with GMP disabled | `lean_alloc_small_object(sizeof(mpz_object))` | Destroy MPZ, then `lean_free_small_object` | `runtime/object.cpp:276`, `1362–1366`; the RV32 target reports MPZ object alignment 4 |
| `free_sized` compatibility implementation | No allocation change | The upstream weak implementation calls ordinary `free(ptr)` | `runtime/object.cpp:65–67`; genuine upstream implementation |

The source is [pinned `runtime/object.cpp`](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/runtime/object.cpp).
The old comment in `formal/lean4/Wasm/build-wasm.sh` saying that the
non-mimalloc allocator returns prefixed string allocations to an
unadjusted free does not describe this pinned implementation. No
mimalloc stand-in, fake allocator or panic/heartbeat replacement is
introduced by this change.

## Actual RV32 layout and relevant accessor audit

`tools/zkvm/rv32_layout_probe.cpp` includes the real upstream `lean.h` and
`runtime/object.h`. It checks the following properties using target C++
`static_assert`; both the pristine and generated header compiled.

| Property | Target result |
| --- | ---: |
| Pointer and `size_t` size | 4 bytes |
| UInt16 alignment | 2 bytes |
| UInt32 and Float32 alignment | 4 bytes |
| UInt64 and Float alignment | 8 bytes |
| `lean_object` size / alignment | 8 / 4 bytes |
| Constructor `m_objs` offset / constructor alignment | 8 / 4 bytes |
| Scalar-array `m_data` offset | 16 bytes |
| Non-GMP `mpz_object` size / alignment | 20 / 4 bytes |
| `std::max_align_t` alignment | 16 bytes |

For an allocation base aligned to eight, the four-byte small-object
prefix puts the object at 4 modulo 8. Its zero-object scalar payload
starts another eight bytes later, still 4 modulo 8. Thus boxed UInt64
and Float already reach the defect without any unusual caller offset.
Changing only the prefix would not establish alignment for every offset
permitted by the header API: an odd number of four-byte object fields
also changes the scalar start unless the caller adds separate padding.

| Accessor family | Relevant source anchors | Alignment analysis / action |
| --- | --- | --- |
| Constructor UInt64 get / set | `lean.h:836`, `871` | Requires eight-byte typed access to byte-offset storage; replaced with `memcpy` |
| Constructor Float get / set | `lean.h:841`, `876` | Same issue for `double`; replaced with `memcpy` |
| `lean_box_uint64` / `lean_unbox_uint64` | `lean.h:2976–2984` | Use those constructor accessors at offset zero; covered by the repair |
| `lean_box_float` / `lean_unbox_float` | `lean.h:2996–3004` | Use those constructor accessors at offset zero; covered by the repair |
| Name/Expr UInt64 fields | `lean.h:3102`, `3286` | Delegate to the repaired UInt64 accessor; no separate typed load |
| Constructor `usize`, UInt8/16/32, Float32 | `lean.h:816–834`, `846–869`, `881` | RV32 type alignment is at most four; the small prefix itself does not violate it. Existing caller offset/layout preconditions remain. These functions are unchanged. |
| FloatArray payload | `lean.h:1128`, `1238–1267` | Direct allocation, then a 16-byte data offset and eight-byte elements. It does not share the small-prefix defect under the allocator's alignment contract. Unchanged. |
| UInt64/Float once-cell values | `lean.h:3411`, `3438` | Access caller-provided typed storage, not constructor byte-offset fields. The typed-storage alignment requirement remains. Unchanged. |

This table audits the relevant header access paths for the observed
small-prefix defect. It does not establish all offset/layout preconditions
for every caller or rule out every alignment problem in the runtime.

## Reproduced failure and repair tests

The host test compiles the actual header as both C and C++ at `-O2` with
`-fsanitize=undefined -fno-sanitize-recover=undefined`. It uses ordinary
libc memory for synthetic constructor storage, keeping the constructor
itself correctly aligned. Only the scalar field is placed at offset
four. Volatile function pointers call the genuine header accessors so
the compiler cannot remove an access by substituting bytes that the
test just wrote.

| Test | Result on 2026-11-22 |
| --- | --- |
| Transformation scope, deterministic hash, pristine-input preservation | Pass |
| Refusal of upstream drift, patched input, in-place output, symlink/hardlink aliases, manifest aliases | Pass; eight contract tests total |
| Pristine C accessor tests | Four expected UBSan failures at the exact source accesses: lines 838, 843, 873, 878 |
| Pristine C++ accessor tests | Same four expected UBSan failures |
| Generated C accessor tests | Four isolated modes plus combined mode pass; no UBSan diagnostic |
| Generated C++ accessor tests | Same five modes pass; no UBSan diagnostic |
| Value preservation | Nine UInt64/binary64 bit patterns, including signed zero, subnormal, infinities and quiet NaNs; adjacent sentinel bytes unchanged |
| Pristine RV32 compilation | Layout assertions and actual accessor compilation pass |
| Generated RV32 compilation | Same assertions and compilation pass |
| Pristine header hash after all tests | Unchanged |

The first probe let GCC remove a known-value load, so a successful run
did not exercise that upstream accessor. The final probe prevents that
optimisation and requires both a misalignment diagnostic and the exact
expected source line for every upstream mode. A passing baseline would
now fail the test runner instead of being counted as success.

The native synthetic probe deliberately does not call the Lean allocator
or `lean_free_object`: its memory lacks the Lean size prefix. The RV32
probe additionally exports `zk_audit_box_payload_alignment`, which can
be linked against the real runtime to inspect a genuine allocation
before any typed scalar access. That helper was compiled, not executed,
in this audit.

## Measured code-generation cost

The RV32 compiler emits safe byte copies and a small stack slot for the
generated `memcpy` accesses. The isolated offset-zero accessor wrappers
have the following assembly instruction counts, including return:

| Wrapper | Pristine header | Generated header |
| --- | ---: | ---: |
| UInt64 get | 3 | 21 |
| UInt64 set | 3 | 20 |
| Float get | 3 | 21 |
| Float set | 3 | 20 |

These are static instruction counts from the actual target assembly,
not cycle measurements, guest timings or a performance ratio for the
ASK pipeline. No claim of zero performance cost is made. The generated
header is an explicit RV32 build input; ordinary native/Wasm builds
which do not use it are unchanged.

## Build integration and reproduction

Generate the separate header before compiling any runtime or generated
Lean C translation unit:

```sh
python3 tools/zkvm/patch_lean_rv32_header.py \
  --input "$LEAN_SRC/src/include/lean/lean.h" \
  --output "$RV32_BUILD/include/lean/lean.h" \
  --manifest "$RV32_BUILD/lean-header-audit.json"
```

Put `-I "$RV32_BUILD/include"` before `-I "$LEAN_SRC/src/include"` for
every C and C++ translation unit. Keep the generated config and its
no-mimalloc/no-GMP/single-thread configuration in that build include
directory. The build must stop if the generator fails. Do not reuse
objects compiled against the original header.

Run the committed tests with a pristine checkout, generated config and
the real RV32 compiler:

```sh
python3 tools/zkvm/test_patch_lean_rv32_header.py \
  --lean-src "$LEAN_SRC" \
  --config-include "$RV32_BUILD/include" \
  --output-dir "$AUDIT_DIR" \
  --rv32-cxx "$RV32_CXX"
```

The output directory contains a JSON report with compiler versions,
exact commands and config/header hashes, each expected UBSan diagnostic,
the generated-header audit, and both target assembly files. These are
regenerable build artefacts and are not committed. Full runtime execution,
failure handling and proof verification remain separate integration gates.
