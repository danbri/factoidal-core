# Native HACL* source provenance

This directory restores the Ed25519/SHA-2 dependency used by Factoidal's
Lean native executables. It contains three extracted C translation
units, their 26-header include closure, and the upstream Apache license.
The C and headers retain their upstream license notices unchanged.

## Source

- Upstream: [cryspen/hacl-packages](https://github.com/cryspen/hacl-packages).
- Upstream revision recorded by the source repository:
  `05c3d8fb321ed65e3db3a6a8b853019e86fb40a2` (2024-09-30).
- Restored from Factoidal source Git revision
  `e505f643297922f195e940eb432d4f3ddf2c2a63` on 2026-10-10.
- The restored paths are unchanged between source checkout
  `0c331255b3a0fec0306b5459a944749364db891f` and that fetched remote
  revision. The source checkout is not modified by this restoration.
- Source provenance record: `third_party/hacl/PROVENANCE.md` at the
  source Git revision. This restoration does not rerun HACL*'s upstream
  F*/Low* verification or independently fetch the upstream distribution.

The restored translation units are `src/Hacl_Ed25519.c`,
`src/Hacl_Curve25519_51.c`, and `src/Hacl_Hash_SHA2.c`. They supply
Ed25519, SHA-256, and the SHA-512 used internally by Ed25519.
Unrelated source-repository primitives and WebAssembly artifacts are
not restored in this native increment.

## Integrity and integration

`SHA256SUMS` records every restored source/header/license file. From
this directory, check the restored bytes with:

```text
shasum -a 256 -c SHA256SUMS
```

`formal/lean4/lakefile.lean` builds these three C files unchanged and
links them with `formal/lean4/ffi/hacl_ed25519.c` into `libl4hacl.a`.
The shim performs length checks, Lean byte-array marshalling, and
big-endian chaining-state conversion; hashing and signing remain HACL*
calls. Native runtime evidence comes from `l4native-crypto-smoke`,
which compares whole and streamed SHA-256 with the pure Lean function
and runs RFC 8032 Ed25519 vectors plus refusal checks.

The pure Lean SHA-256 remains the specification. Native declarations
are opaque and introduce no equality theorem or new logical axiom.
Differential checks establish agreement only on their exercised
inputs. Messages above HACL*'s u32 byte-length limit are refused by the
whole-message binding; such a refusal is an empty byte array, never a
32-byte digest. Browser and WebAssembly compatibility are separate
validation obligations and are not established by a native smoke run.

Do not edit the extracted C or headers. Update their pinned source
and integrity record together when adopting a different upstream
revision.
