/-
Wasm.HostRead — the positioned reads of a store whose bytes a host supplies
(https://github.com/danbri/factoidal/issues/1009 KR1).

  hostReadAt source file off len : IO ByteArray   -- `len` bytes, else an IO error
  hostSize source file : IO UInt64                -- `UInt64.max`: no such file

Realisation: `ffi/l4_hostread.c`. Under Emscripten each is an `EM_JS` thunk
onto `globalThis.__factoidalReadAt` and `globalThis.__factoidalFileSize`,
which the JavaScript host installs (`npm/factoidal/lib/sbm11.mjs`). On every
other target `source` is a directory and a read is one `pread` of
`source/file`, so the native `l4factoidal` runs the same ops over the same
files.

This is the shape of `Wasm/ExtHost.lean` and `Harness/PosixRangeIO.lean`: an
`opaque` declaration realised by C. No `unsafe`, no `@[implemented_by]`, no
user `axiom`. It lives in `Wasm/` because a host call-out is an ambient
effect; the library session (`Storage/Sbm11/HostSession.lean`) takes its
reads as a `Host` value and names no extern.
-/
import L4Factoidal.Storage.Sbm11.HostSession

namespace L4Wasm

@[extern "l4_host_read_at"]
opaque hostReadAt (source file : @& String) (off len : UInt64) : IO ByteArray

@[extern "l4_host_size"]
opaque hostSize (source file : @& String) : IO UInt64

/-- The host of the generation that `source` names: a read-only storage
    medium (`Storage/Medium.lean`, issue 1010 KR1); `writeObject` and
    `switchPointer` refuse. -/
def hostOf (source : String) : L4Factoidal.Storage.Sbm11.HostSession.Host :=
  L4Factoidal.Storage.Medium.readOnlyIO
    (fun file off len => hostReadAt source file off.toUInt64 len.toUInt64)
    (fun file => do
      let n ← hostSize source file
      return if n == UInt64.ofNat (2 ^ 64 - 1) then none else some n.toNat)

end L4Wasm
