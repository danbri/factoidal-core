/-
Wasm.MediumHost — the host side of the storage-medium interface
(`L4Factoidal/Storage/Medium.lean`, https://github.com/danbri/factoidal/issues/1010
KR1) for the wasm module and the native dispatch driver.

  mediumReadHost root name off len : IO ByteArray
  mediumSizeHost root name         : IO UInt64     (`UInt64.max`: absent)

`root` is the store identifier the host gave to `sbm11Open`; `name` is an
object name that Lean built (`Medium.objectName` of a manifest file name, which
`Manifest.safeFileName` admitted, or `CURRENT` and its target). The host maps
the pair to bytes and decides nothing else.

Realisation: `ffi/l4_medium.c`. Under Emscripten it is two `EM_JS` thunks onto
`globalThis.__factoidalMediumRead(root, name, off, len)` (a `Uint8Array`, or
`null`) and `globalThis.__factoidalMediumSize(root, name)` (a byte count, or
`-1` when absent), which the JavaScript host installs
(`npm/factoidal/lib/sbm11-hosts.mjs`: Node `fs` positioned reads). On every
other target the C side reads the file `root/name` with POSIX `open`, `fstat`
and `pread`, so `lake exe l4wasm-cli callseq` runs the same ops natively.

The same shape as `Wasm/ExtHost.lean` (the §17.6 call-out) and
`Harness/PosixRangeIO.lean` (positioned reads): an `opaque` declaration
realised by C. No `unsafe`, no `@[implemented_by]`, no user `axiom`.

What these reads return is the named IO assumption `MediumReadsWritten`
(stage `sbm11Medium`, `L4Factoidal/Dataflow/Instances.lean`).
-/
import L4Factoidal.Storage.Medium

namespace L4Wasm

/-- Bytes `[off, off + len)` of object `name` of store `root`, or the empty
array when the host has no such bytes (an absent object, a short object, a
host error). -/
@[extern "l4_medium_read"]
opaque mediumReadHost (root : @& String) (name : @& String) (off len : UInt64) : IO ByteArray

/-- The length of object `name` of store `root`; `UInt64.max` when it is
absent. -/
@[extern "l4_medium_size"]
opaque mediumSizeHost (root : @& String) (name : @& String) : IO UInt64

open L4Factoidal.Storage.Medium (Medium)

/-- The medium of store `root` through the host functions: read only (the
writes of issue 1010 KR2 and KR3 refuse). A read that returns fewer bytes
than asked is an error that names the object. -/
def hostMedium (root : String) : Medium IO :=
  L4Factoidal.Storage.Medium.readOnly
    (fun name off len => do
      if len == 0 then return .ok ByteArray.empty
      if off ≥ 2 ^ 63 || len ≥ 2 ^ 63 then return .error s!"{name}: range out of bounds"
      let b ← mediumReadHost root name off.toUInt64 len.toUInt64
      if b.size == len then return .ok b
      return .error s!"{name}: the host returned {b.size} of {len} bytes at {off}")
    (fun name => do
      let n ← mediumSizeHost root name
      return .ok (if n == UInt64.ofNat (2 ^ 64 - 1) then none else some n.toNat))

end L4Wasm
