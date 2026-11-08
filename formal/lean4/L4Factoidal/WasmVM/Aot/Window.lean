/-
L4Factoidal.WasmVM.Aot.Window: a view of a guest memory that lives outside Lean
(record: docs/designissues/2026-11-08-wasmvm-aot.md, "Host calls").

When the host's WebAssembly engine runs a translated guest, the guest's memory is that
engine's memory, not a Lean value. A host function of Lean (`Wasi.call`,
`Hosts.Dom.serve`) still reads and writes it through `StoreOf.readMem` and
`StoreOf.writeMemS`, generic in the `LinearMemory` backend. A `Window` is such a backend:
the memory's size, the byte ranges the host copied in before the call (`segs`), and the
writes the function made (`writes`), which the host copies back after it. A byte that is
neither in a segment nor written reads as zero; the host sends every range a function
reads (`Hosts.Page.readsOf`), so a host function never reads one.
-/
import L4Factoidal.WasmVM.Exec.Memory

namespace L4Factoidal.WasmVM.Aot

structure Window where
  size : Nat
  segs : Array (Nat × ByteArray) := #[]
  writes : Array (Nat × ByteArray) := #[]
  deriving Inhabited

namespace Window

/-- The byte at `i`: the last write that holds it, else a segment that holds it, else 0. -/
def byteAt (w : Window) (i : Nat) : UInt8 :=
  let hit := fun (acc : Option UInt8) (p : Nat × ByteArray) =>
    match acc with
    | some b => some b
    | none => if p.1 ≤ i && i < p.1 + p.2.size then some (p.2.get! (i - p.1)) else none
  match w.writes.foldr (fun p acc => hit acc p) none with
  | some b => b
  | none => (w.segs.foldl hit none).getD 0

def readBytes (w : Window) (off n : Nat) : ByteArray :=
  -- One segment holds the whole range and nothing was written: one copy.
  match w.writes.isEmpty, w.segs.find? (fun p => p.1 ≤ off && off + n ≤ p.1 + p.2.size) with
  | true, some (s, b) => b.extract (off - s) (off - s + n)
  | _, _ => Id.run do
    let mut out := ByteArray.emptyWithCapacity n
    for k in [0:n] do out := out.push (w.byteAt (off + k))
    return out

def load (w : Window) (ea n : Nat) : UInt64 := Id.run do
  let mut v : UInt64 := 0
  for k in [0:n] do v := v ||| ((w.byteAt (ea + k)).toUInt64 <<< (8 * k).toUInt64)
  return v

def le (v : UInt64) (n : Nat) : ByteArray := Id.run do
  let mut out := ByteArray.emptyWithCapacity n
  for k in [0:n] do out := out.push (v >>> (8 * k).toUInt64).toUInt8
  return out

def write (w : Window) (d : Nat) (b : ByteArray) : Window := { w with writes := w.writes.push (d, b) }

end Window

instance : LinearMemory Window where
  empty := { size := 0 }
  size w := w.size
  create n _ := { size := n }
  grow w n := { w with size := w.size + n }
  load8 w ea _ := w.load ea 1
  load16 w ea _ := w.load ea 2
  load32 w ea _ := w.load ea 4
  load64 w ea _ := w.load ea 8
  store8 w ea v _ := w.write ea (Window.le v 1)
  store16 w ea v _ := w.write ea (Window.le v 2)
  store32 w ea v _ := w.write ea (Window.le v 4)
  store64 w ea v _ := w.write ea (Window.le v 8)
  copyWithin w s d n := w.write d (w.readBytes s n)
  copyInto src s dst d n := dst.write d (src.readBytes s n)
  fill w d b n := w.write d (ByteArray.mk (Array.replicate n b))
  writeBytes w d b s n := w.write d (b.extract s (s + n))
  readBytes w off n := w.readBytes off n

end L4Factoidal.WasmVM.Aot
