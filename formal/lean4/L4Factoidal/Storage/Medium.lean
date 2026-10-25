/-
L4Factoidal.Storage.Medium — the storage-medium interface of persistent
stores (https://github.com/danbri/factoidal/issues/1010, KR1).

A medium holds named IMMUTABLE objects (the files of a generation, its
manifest, its delta log) and one small mutable object per store, the current
pointer (`CURRENT` on disk). A store reads and writes through three host
operations and nothing else:

1. `readAt name off len`: bytes `[off, off + len)` of object `name`;
2. `writeObject name bytes`: write a new immutable object (issue 1010 KR2 and
   KR3; declared here, served by no host yet);
3. `switchPointer name expected new`: replace the pointer `name` by `new` only
   when it still holds `expected` (`none`: absent), and say whether it did
   (issue 1010 KR3; declared here, served by no host yet).

`size name` answers the length of an object, or `none` when it is absent. The
host decides no format, no name and no digest (iron rule 7): every object name
is built in Lean, and every byte the host returns is decoded and checked in
Lean.

Hosts (`docs/designissues/2026-10-24-sbm11-in-npm.md` section 3): native and
Node `fs` positioned reads, OPFS `FileSystemSyncAccessHandle.read({ at })`,
HTTP `Range` requests (read only), LWS resources (issue 1010 KR3). In this
landing the wasm module reaches its host through `Wasm/MediumHost.lean`
(`ffi/l4_medium.c`), and the Node host is `npm/factoidal/lib/sbm11-hosts.mjs`.

## The named assumption

`IO` is opaque to Lean, so what a host returns is not proved. The behaviour a
store relies on is the named IO assumption `MediumReadsWritten`
(`Dataflow/Instances.lean`, stage `sbm11Medium`): every `readAt name off len`
that succeeds returns `b.extract off (off + len)` of the bytes `b` written to
the object `name`, and `size name` is `some b.size`. It is the assumption
`ReadsWritten` of the native disk (`sbm11Disk`) stated for any medium; the
theorems over the files' bytes (`FileGenTheorems.store_written`) then hold
over every medium unchanged.

`ofObjects` is a pure model of a medium (a list of named byte arrays); it
satisfies the assumption by construction, and the `#guard` tests of
`Storage/Sbm11/QuerySessionTests.lean` read a generation through it.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/

namespace L4Factoidal.Storage.Medium

/-- **The host operations of a storage medium.** Object names are relative
paths that Lean builds (`objectName`); a host maps them to its own namespace
(a directory, an OPFS directory handle, a URL prefix). -/
structure Medium (m : Type → Type) where
  /-- Bytes `[off, off + len)` of the immutable object `name`. An error when
      the object is absent or shorter than `off + len`. -/
  readAt : (name : String) → (off len : Nat) → m (Except String ByteArray)
  /-- The length of the object `name`, `none` when it is absent. -/
  size : (name : String) → m (Except String (Option Nat))
  /-- Write the immutable object `name` (issue 1010 KR2). A host refuses a
      name that already exists. -/
  writeObject : (name : String) → ByteArray → m (Except String Unit)
  /-- Replace the pointer `name` by `new` when it holds `expected` (`none`:
      the pointer is absent); `true` when it did, `false` when another writer
      switched it first (issue 1010 KR3). -/
  switchPointer : (name : String) → (expected : Option String) → (new : String) → m (Except String Bool)

/-- The answer of a write operation of a read-only medium. -/
def readOnlyRefusal (op : String) : String :=
  s!"{op}: this medium is read only (issue 1010 KR2 and KR3 add writes)"

/-- A read-only medium: the two read operations of a host; both writes refuse. -/
def readOnly {m : Type → Type} [Monad m]
    (readAt : String → Nat → Nat → m (Except String ByteArray))
    (size : String → m (Except String (Option Nat))) : Medium m where
  readAt := readAt
  size := size
  writeObject := fun _ _ => pure (.error (readOnlyRefusal "writeObject"))
  switchPointer := fun _ _ _ => pure (.error (readOnlyRefusal "switchPointer"))

/-- A safe object or directory name component: not empty, not `.` or `..`,
no `/` or `\` (the rule of `Sbm11.Manifest.safeFileName` and of the
generation pointer). -/
def safeComponent (name : String) : Bool :=
  !name.isEmpty && name != "." && name != ".." && !(name.contains '/') && !(name.contains '\\')

/-- The object `file` of the generation directory `dir` (`""`: the root). -/
def objectName (dir file : String) : String :=
  if dir.isEmpty then file else dir ++ "/" ++ file

/-- The whole object `name`, or `none` when it is absent. -/
def readWhole? {m : Type → Type} [Monad m] (md : Medium m) (name : String) :
    m (Except String (Option ByteArray)) := do
  match ← md.size name with
  | .error e => pure (.error e)
  | .ok none => pure (.ok none)
  | .ok (some n) =>
    match ← md.readAt name 0 n with
    | .error e => pure (.error e)
    | .ok b =>
      if b.size == n then pure (.ok (some b))
      else pure (.error s!"{name}: read {b.size} bytes, the medium says {n}")

/-- The name of the current pointer of a collection root. -/
def currentName : String := "CURRENT"

/-- The generation directory a collection root names: the child its `CURRENT`
pointer names, or the root itself (`""`) when it has no pointer. A pointer
that is not UTF-8 or does not name a safe child is an error, as on disk
(`Harness.GenerationPointer.resolveStoreDirectory`). -/
def resolveGeneration {m : Type → Type} [Monad m] (md : Medium m) : m (Except String String) := do
  match ← readWhole? md currentName with
  | .error e => pure (.error e)
  | .ok none => pure (.ok "")
  | .ok (some b) =>
    match String.fromUTF8? b with
    | none => pure (.error "CURRENT is not valid UTF-8")
    | some name =>
      if safeComponent name then pure (.ok name)
      else pure (.error "CURRENT does not name a safe generation directory")

/-- **The pure model of a medium**: the objects are a list of names and
bytes (the first entry of a name wins); `readAt` cuts a range, and refuses a
range past the end; writes refuse. Every read it answers is the extract of the
bytes it holds, which is the assumption `MediumReadsWritten` by
construction. -/
def ofObjects {m : Type → Type} [Monad m] (objs : List (String × ByteArray)) : Medium m :=
  readOnly
    (fun name off len =>
      match objs.lookup name with
      | none => pure (.error s!"{name}: no such object")
      | some b =>
        if off + len ≤ b.size then pure (.ok (b.extract off (off + len)))
        else pure (.error s!"{name}: read of {len} bytes at {off} past the end ({b.size} bytes)"))
    (fun name => pure (.ok ((objs.lookup name).map (·.size))))

/-- A read through the model returns the extract of the object's bytes. -/
theorem ofObjects_readAt {m : Type → Type} [Monad m] (objs : List (String × ByteArray)) (name : String)
    (b : ByteArray) (h : objs.lookup name = some b) (off len : Nat) (hr : off + len ≤ b.size) :
    (ofObjects (m := m) objs).readAt name off len = pure (.ok (b.extract off (off + len))) := by
  simp [ofObjects, readOnly, h, hr]

/-- The size of an object of the model is the size of its bytes. -/
theorem ofObjects_size {m : Type → Type} [Monad m] (objs : List (String × ByteArray)) (name : String) :
    (ofObjects (m := m) objs).size name = pure (.ok ((objs.lookup name).map (·.size))) := rfl

private def demo : List (String × ByteArray) :=
  [("a", "hello".toUTF8), ("CURRENT", "g1".toUTF8), ("bad/CURRENT", "../x".toUTF8)]

#guard (Id.run ((ofObjects demo).readAt "a" 1 3)).toOption.map (·.toList) == some "ell".toUTF8.toList
#guard ((Id.run ((ofObjects demo).readAt "a" 3 3)) matches .error _)
#guard ((Id.run ((ofObjects demo).readAt "b" 0 0)) matches .error _)
#guard (Id.run ((ofObjects demo).size "b")).toOption == some none
#guard (Id.run (resolveGeneration (ofObjects demo))).toOption == some "g1"
#guard (Id.run (resolveGeneration (ofObjects (m := Id) [("a", ByteArray.empty)]))).toOption == some ""
#guard ((Id.run ((ofObjects demo).writeObject "c" ByteArray.empty)) matches .error _)
#guard objectName "" "manifest.sbm11" == "manifest.sbm11"
#guard objectName "g1" "manifest.sbm11" == "g1/manifest.sbm11"
#guard !safeComponent ".." && !safeComponent "a/b" && safeComponent "gen-1"

end L4Factoidal.Storage.Medium
