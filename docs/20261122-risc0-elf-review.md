# Restricted RISC Zero guest: binary gate and runtime review

Tracking: <https://github.com/danbri/factoidal-core/issues/745>.

## Concrete runtime findings

The pinned Lean runtime defines `LEAN_THREAD_PTR` and `LEAN_THREAD_VALUE`
using GCC `__thread` independently of `LEAN_MULTI_THREAD`. The initial RV32
archive therefore contained TLS even though the backend selected Lean's
single-thread configuration. Inspection of its actual `runtime_alloc.o`
showed `lean_inc_heartbeat` loading and storing through `tp`, with
`R_RISCV_TPREL_*` relocations and a TLS `g_heartbeat` symbol. The RISC Zero
3.1.0 guest entry initialises `gp` and `sp`, but does not initialise C TLS.
Every small Lean allocation increments this heartbeat, so this was a runtime
blocker, rather than an unused optional feature.

The integration branch addresses this with a narrowly guarded patch of the
four `LEAN_THREAD_*` storage macros to ordinary storage for the single,
non-preemptive hart. Its generated-source manifest records the pinned
header before and after the patch. The gate below checks the resulting
binary as an independent obligation; a source patch alone is insufficient.

Review also found that `lean_get_stderr` returns a raw `FS.Stream` through
`BaseIO`, so returning an `IO.Result.error` would have the wrong object
layout. The restricted port aborts on this unsupported operation and on
unexpected task-worker stack setup. `lean_st_mk_ref` retains the exact
upstream allocation/header/ownership operations. The standard
`Init.Data.Random` initializer needs eight real SDK-provided advice bytes
once; those bytes are unrelated to the supplied private salt and carry no
entropy or authority guarantee. Admitted ASK execution has no RNG access.

The bridge checks initializer errors before calling the checked computation.
Lean errors have empty output; only statuses 0 and 1 with 128 journal bytes
can reach the Rust commit. Runtime panic exits are enabled before module
initialization. These are source/codeflow review conclusions, not a new
formal proof about C or Rust.

## ELF and archive gate

`zkvm/risc0/verify-elf.py` checks the actual bytes of the guest executable and
optionally every ELF member of its runtime archive. The accepted binary
profile is ELF32, little endian, RISC-V, static `ET_EXEC`, with zero ABI
flags and a word-aligned entry in executable file bytes. The optional
archive contains ordinary `ET_REL` objects; thin archives and malformed or
unrecognised members are refused.

The gate checks ELF program, section, symbol and relocation tables directly.
It refuses dynamic/interpreter headers, dynamic symbol/section tables, TLS
program headers, TLS section flags, TLS symbol types and RISC-V TLS
relocations. Section-name checks also catch `.tdata` and `.tbss`. The
explicitly selected GNU `readelf` independently examines an immutable
temporary snapshot, with warnings and errors treated as failures. Its
relocation-name check supplements the numeric TLS relocation checks.
The tool's path, version and SHA-256 are recorded; callers can require its
exact hash with `--readelf-sha256`.

Example, with paths supplied by the build:

```sh
python3 zkvm/risc0/verify-elf.py \
  --readelf /absolute/pinned/toolchain/bin/riscv32-unknown-elf-readelf \
  --elf /absolute/build/factoidal-ask-guest \
  --runtime-archive /absolute/build/libfactoidal_ask.a \
  --report /absolute/evidence/elf-check.json
```

This checks the binary format and the stated restrictions. It does not
prove the machine code's behaviour, validate the complete instruction set,
or replace source/build provenance and actual guest/native journal parity.

## Validation

The Python suite has 13 passing tests, including real selected-readelf
integration. Its controls cover architecture and ABI mismatches, truncated
tables, invalid entry points, dynamic/interpreter headers, TLS whose section
name looks ordinary, TLS symbols without a TLS section, all 18 recognised
TLS relocation numbers, normal relocations, GNU long archive names,
malformed/thin/duplicate archives, a wrong tool hash and non-ELF members.
The tiny valid ELF fixtures are generated in temporary directories and are
structural controls; they are not claimed to execute the ASK computation.

Before the integration rebuild replaced the original archive, its actual
3,172-byte `runtime_alloc.o` was extracted outside the repository. The gate
refused that object in an archive with 26 reported TLS findings, including
its section, symbol and real `TPREL` relocations. No binary fixture is
committed. Acceptance of the final production guest remains a separate
integration check once the guest links.

The full original 76,383,514-byte runtime archive was also checked: all
896 object members were inspected and the gate refused it with 187 TLS
findings. Its SHA-256 was
`384c44a277df6a6b5ba07a503e6a5fd463e78036746aee583d80362b524c2a9f`.

## Receipt decoding review

The initial offline verifier's 512 MiB bincode limit did not bound nesting
of `CompositeReceipt.assumption_receipts`. A 1,040,092-byte input with
20,000 nested composite assumptions caused a stack-overflow abort before
proof verification. It produced no successful verification or journal;
this was an availability defect. A depth-zero control returned the normal
invalid-receipt error.

The SDK's `SegmentReceipt` and its `ReceiptClaim` are not recursively
nested: claim assumptions are a list of values containing two digests.
The agreed integration fix is to preflight the fixed bincode envelope and
refuse any nonempty composite assumption-receipt list before recursive SDK
decoding. The ASK guest itself uses no receipt assumptions. Proof
verification must continue to use the SDK after decoding; the preflight
does not implement cryptography. That change and its regression controls
are owned by the integration branch.

## Ordinary memory fences on the restricted target

The first complete guest linked and passed the ELF/TLS gate but execution
trapped on instruction `0x0ff0000f`, the ordinary full `fence iorw,iorw`.
Mapping the disassembled instruction addresses to the actual linker map
found 9,901 such fences: 73 in `runtime_object.o` and 9,828 in the generated
Lean modules. None came from linked Rust or toolchain-library code. The
principal source is `lean_once_cell_t.state`: its `_Atomic(int)` storage
and the implicit sequentially consistent reads in the `lean_*_once`
fast paths make GCC emit fences. Task-object atomic accesses account for
the remaining runtime sites.

`lower-fences.py` supplies a deliberately narrow build transformation:

1. GCC compiles each source to its original assembly with `-S` and the
   existing RV32IM/ILP32 flags.
2. `lower_assembly(source_bytes)` replaces only standalone ordinary `fence`
   or `fence iorw,iorw` instruction lines with `nop`. It returns the lowered
   bytes and a JSON-serialisable audit containing source-line locations,
   counts, before/after words and before/after assembly hashes.
3. The same GCC toolchain assembles the lowered file with RV32IM/ILP32.
   Original assembly, lowered assembly and audit are retained as build
   evidence. In this noncompressed instruction profile both instructions
   occupy four bytes.

The target has one non-preemptive hart, no concurrent memory users, no
signal handlers and no memory-mapped devices exposed by the computation.
An ordinary hardware ordering fence therefore adds no observable action
to the sequential execution. Performing this transformation after GCC
code generation retains the compiler's ordering decisions. It does not
relax C/C++ atomic semantics before optimisation. This is an explicit
restricted-runtime port assumption, not a new Lean theorem.

FENCE.I, other fence forms, inline-label/compound fence lines and unknown
operands are refused. Directives, data and comments are preserved, including
strings or `.word` data that happen to contain fence-like text. There is no
binary search-and-replace and no modification to the installed toolchain.

The complete pinned `libstdc++.a` contains three fence/atomic opcodes in
`debug.o`; that object was absent from the linked guest. The pinned `libc.a`
and `libgcc.a` contain none. Future changes can alter what gets linked, so
`verify-instructions.py` checks the final ELF with an explicitly selected
GNU `objdump`. It scans actual 32-bit instruction words in executable
sections and refuses the MISC-MEM opcode (all fences, including FENCE.I)
and AMO opcode (all atomic instructions, including LR/SC). It is a companion
to the ELF/TLS gate, not a complete instruction-set validator.

Validation: ten lowering/scanner tests pass, including an actual
assembler/linker control proving that both fence replacements preserve
instruction addresses and become four-byte NOPs. Fence-valued `.rodata`
remains unchanged and is not treated as executable code. Actual GCC `-S`
output for the full pinned `runtime/object.cpp` and generated
`Init.Data.OfScientific` was accepted, with 125 and 76 sites respectively
(including sites later discarded by the linker). The final instruction
gate inspected 1,173,263 instruction words in the original guest and
correctly refused all 9,901 fences. That original ELF had SHA-256
`a1c84aa44150fd4693f4ff5863297835b9b72d14a28a1f789ef7f01ce74858ae`.
The rebuilt production guest still requires a clean final scan and an
actual execution/parity check.
