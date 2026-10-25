/-
L4Factoidal.Storage.Medium — the storage-medium interface of persistent
stores (https://github.com/danbri/factoidal/issues/1010, KR1).

A medium holds named IMMUTABLE objects (the files of a generation, its
manifest) and one small mutable object per store, the current pointer
(`CURRENT` on disk). A store reads and writes through four host operations
and nothing else:

1. `readAt name off len`: bytes `[off, off + len)` of the object `name`,
   exactly `len` bytes, else an error;
2. `size name`: the length of the object `name`, `none` when it is absent;
3. `writeObject name bytes`: write a new immutable object (issue 1010 KR2 and
   KR3). Declared here; every host refuses it today;
4. `switchPointer name expected new`: replace the pointer `name` by `new` only
   when it still holds `expected` (`none`: absent), and answer whether it did
   (issue 1010 KR3: on LWS a conditional PUT with `If-Match`). Declared here;
   every host refuses it today.

The host decides no format, no name and no digest (iron rule 7): every object
name is built in Lean, and every byte the host returns is decoded and checked
in Lean (`Sbm11/HostSession.lean` checks each read against the manifest).

Hosts today, all read only (`readOnly`): the native and Node `fs` positioned
reads and any JavaScript reader (`Wasm/HostRead.lean`), among them the LWS
reader of `npm/factoidal/lib/sbm11-lws.mjs` (HTTP `Range` GETs of LWS
resources, issue 1010 KR3 read part).

## The named assumption

`IO` is opaque to Lean, so what a host returns is not proved. What a store
relies on is the named IO assumption `ReadsWritten` of
`Dataflow/Instances.lean` (stage `sbm11Disk`): the bytes read are the bytes
the packer wrote. `ServesObjects md objs` is that assumption stated for one
medium and its objects; it is not a second assumption. `ofObjects`, the pure
model of a medium, satisfies it by proof (`ofObjects_serves`); for every
host medium it is `ReadsWritten`, assumed.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/

namespace L4Factoidal.Storage.Medium

/-- **The host operations of a storage medium** over a monad `m` in which an
operation can fail (`IO` for a host, `Except String` for the model). Object
names are relative paths that Lean builds; a host maps them to its own
namespace (a directory, an OPFS directory, a URL prefix). -/
structure Medium (m : Type → Type) where
  /-- Bytes `[off, off + len)` of the immutable object `name`: exactly `len`
      bytes, else an error. -/
  readAt : (name : String) → (off len : Nat) → m ByteArray
  /-- The length of the object `name`, `none` when it is absent. -/
  size : (name : String) → m (Option Nat)
  /-- Write the immutable object `name` (issue 1010 KR2, KR3). -/
  writeObject : (name : String) → ByteArray → m Unit
  /-- Replace the pointer `name` by `new` when it holds `expected` (`none`:
      absent); `true` when it did, `false` when another writer switched it
      first (issue 1010 KR3). -/
  switchPointer : (name : String) → (expected : Option String) → (new : String) → m Bool

/-- The refusal of a write operation by a read-only medium. -/
def readOnlyRefusal (op name : String) : String :=
  s!"{op} {name}: this storage medium is read only (writes are https://github.com/danbri/factoidal/issues/1010 KR2 and KR3)"

/-- A read-only medium: the two read operations of a host; both writes
answer `fail` with `readOnlyRefusal`. -/
def readOnly {m : Type → Type} (fail : {α : Type} → String → m α)
    (readAt : String → Nat → Nat → m ByteArray) (size : String → m (Option Nat)) : Medium m where
  readAt := readAt
  size := size
  writeObject := fun name _ => fail (readOnlyRefusal "writeObject" name)
  switchPointer := fun name _ _ => fail (readOnlyRefusal "switchPointer" name)

/-- A read-only medium in `IO`: a failure is `IO.userError`. -/
def readOnlyIO (readAt : String → Nat → Nat → IO ByteArray) (size : String → IO (Option Nat)) :
    Medium IO :=
  readOnly (fun msg => throw (IO.userError msg)) readAt size

/-- The object `file` of the directory `dir` (`""`: the root). -/
def objectName (dir file : String) : String :=
  if dir.isEmpty then file else dir ++ "/" ++ file

/-- The medium of the subdirectory `dir`: every name is prefixed with
`dir/`, for all four operations. -/
def Medium.under {m : Type → Type} (md : Medium m) (dir : String) : Medium m where
  readAt := fun f off len => md.readAt (objectName dir f) off len
  size := fun f => md.size (objectName dir f)
  writeObject := fun f b => md.writeObject (objectName dir f) b
  switchPointer := fun f e n => md.switchPointer (objectName dir f) e n

/-- The medium in `IO` of a medium in `Except String`: a model, run where a
host is expected. -/
def Medium.toIO (md : Medium (Except String)) : Medium IO where
  readAt := fun f off len => IO.ofExcept (md.readAt f off len)
  size := fun f => IO.ofExcept (md.size f)
  writeObject := fun f b => IO.ofExcept (md.writeObject f b)
  switchPointer := fun f e n => IO.ofExcept (md.switchPointer f e n)

/-- **`ReadsWritten` for one medium**: for every object `name` with bytes
`b` in `objs`, `size name` answers `some b.size` and every read inside `b`
answers the extract of `b`. For a host medium this is the named IO
assumption `ReadsWritten` (`Dataflow/Instances.lean`), not proved. -/
def ServesObjects {m : Type → Type} [Pure m] (md : Medium m) (objs : List (String × ByteArray)) : Prop :=
  ∀ name b, objs.lookup name = some b →
    md.size name = pure (some b.size) ∧
    ∀ off len, off + len ≤ b.size → md.readAt name off len = pure (b.extract off (off + len))

/-- **The pure model of a medium**: the objects are a list of names and
bytes (the first entry of a name wins); `readAt` cuts a range and refuses a
range past the end; both writes refuse. -/
def ofObjects (objs : List (String × ByteArray)) : Medium (Except String) :=
  readOnly (fun msg => .error msg)
    (fun name off len =>
      match objs.lookup name with
      | none => .error s!"{name}: no such object"
      | some b =>
        if off + len ≤ b.size then .ok (b.extract off (off + len))
        else .error s!"{name}: a read of {len} bytes at {off} is past the end ({b.size} bytes)")
    (fun name => .ok ((objs.lookup name).map (·.size)))

/-- The model satisfies `ServesObjects`, by proof. -/
theorem ofObjects_serves (objs : List (String × ByteArray)) : ServesObjects (ofObjects objs) objs := by
  intro name b h
  refine ⟨?_, ?_⟩
  · simp [ofObjects, readOnly, h]; rfl
  · intro off len hr
    simp [ofObjects, readOnly, h, hr]; rfl

/-- A read-only medium refuses `writeObject`, whatever the name and bytes. -/
theorem readOnly_writeObject {m : Type → Type} (fail : {α : Type} → String → m α)
    (r : String → Nat → Nat → m ByteArray) (s : String → m (Option Nat)) (name : String) (b : ByteArray) :
    (readOnly @fail r s).writeObject name b = fail (readOnlyRefusal "writeObject" name) := rfl

/-- A read-only medium refuses `switchPointer`. -/
theorem readOnly_switchPointer {m : Type → Type} (fail : {α : Type} → String → m α)
    (r : String → Nat → Nat → m ByteArray) (s : String → m (Option Nat)) (name : String)
    (e : Option String) (n : String) :
    (readOnly @fail r s).switchPointer name e n = fail (readOnlyRefusal "switchPointer" name) := rfl

/-- `under` reads the prefixed object. -/
theorem under_readAt {m : Type → Type} (md : Medium m) (dir f : String) (off len : Nat) :
    (md.under dir).readAt f off len = md.readAt (objectName dir f) off len := rfl

/-! ## Tests over the model -/

private def demo : List (String × ByteArray) :=
  [("a", "hello".toUTF8), ("CURRENT", "g1".toUTF8), ("g1/manifest.sbm11", "MANI".toUTF8)]

#guard ((ofObjects demo).readAt "a" 1 3).toOption.map (·.toList) == some "ell".toUTF8.toList
#guard ((ofObjects demo).readAt "a" 0 5).toOption.map (·.toList) == some "hello".toUTF8.toList
#guard ((ofObjects demo).readAt "a" 3 3) matches .error _
#guard ((ofObjects demo).readAt "b" 0 0) matches .error _
#guard ((ofObjects demo).size "a").toOption == some (some 5)
#guard ((ofObjects demo).size "b").toOption == some none
#guard (((ofObjects demo).under "g1").size "manifest.sbm11").toOption == some (some 4)
#guard (((ofObjects demo).under "g1").readAt "manifest.sbm11" 0 4).toOption.map (·.toList) ==
  some "MANI".toUTF8.toList
#guard ((ofObjects demo).writeObject "c" ByteArray.empty) matches .error _
#guard ((ofObjects demo).switchPointer "CURRENT" (some "g1") "g2") matches .error _
private def errorOf {α : Type} : Except String α → Option String
  | .error e => some e
  | .ok _ => none

#guard errorOf (((ofObjects demo).under "g1").writeObject "x" ByteArray.empty) ==
  some (readOnlyRefusal "writeObject" "g1/x")
#guard objectName "" "manifest.sbm11" == "manifest.sbm11"
#guard objectName "g1" "manifest.sbm11" == "g1/manifest.sbm11"

end L4Factoidal.Storage.Medium
