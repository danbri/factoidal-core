/-
Harness/QlvrKernelBench — `l4qlvr-kernel FILE [ITERS]`: the q07 kernel
timing loop of `l4qlvr kernel` alone (Harness/QlvrKernel.lean), as an
executable whose import closure has no FFI, so that tools/lean-wasm-exe.sh
can build it for wasm32 and node can run it on the same input file
(https://github.com/danbri/factoidal/issues/797).
-/
import Harness.QlvrKernel

/-- The file read in 1 MiB chunks through a handle. `IO.FS.readBinFile` asks
    the runtime for the file size first (`lean_io_metadata`), which calls
    libuv, and libuv is not in the wasm32 runtime build. -/
def readAll (file : String) : IO ByteArray := do
  let h ← IO.FS.Handle.mk file .read
  let mut out := ByteArray.empty
  repeat
    let chunk ← h.read (1024 * 1024)
    if chunk.isEmpty then break
    out := out ++ chunk
  return out

def main (args : List String) : IO UInt32 :=
  match args with
  | [file] => do QlvrKernel.runKernel (← readAll file) 50
  | [file, n] => do QlvrKernel.runKernel (← readAll file) (n.toNat?.getD 50)
  | _ => do IO.eprintln "usage: l4qlvr-kernel FILE [ITERS]"; return 2
