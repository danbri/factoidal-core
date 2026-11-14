/-
L4Factoidal.ClientStorage.FileSystem — the File System Standard (WHATWG fs): the origin
private file system of a storage key (`navigator.storage.getDirectory()`), its entries,
`FileSystemWritableFileStream` with its swap-file semantics, `FileSystemSyncAccessHandle`,
locks, `isSameEntry`, `resolve`, `move`, `remove`, and the usage that `StorageManager`
reports.

## Decisions

* **No host file system.** The tree of a storage key is a map from a path (the names from
  the root) to a directory or a file's bytes, in Lean memory. There is no operation that
  takes or answers a host path, and nothing is written to disk (the persistence policy is
  not decided). A name is checked by `validName` (not empty, not `.` or `..`, no `/` or
  `\`), so a path never leaves the root (`get_invalid_name`).
* **A handle is a path and a kind** (the standard's "file system locator"): it names an
  entry, it does not hold one. Two handles are the same entry when their paths and kinds
  are equal (`same_iff`); a handle whose entry was removed finds nothing (`NotFoundError`).
* **Swap file.** `createWritable` copies the file (or starts empty) into a buffer of the
  writable. `write`, `seek` and `truncate` change that buffer only (`writable_tree`: the
  tree is exactly as it was), and `close` replaces the file's bytes in one step or fails
  and changes nothing (`close_atomic`). `abort` drops the buffer.
* **Locks** (the standard's "take a lock"): writables in mode `siloed` share a file with
  each other; an `exclusive` writable and a `readwrite` access handle hold it alone;
  `read-only` and `readwrite-unsafe` access handles share it with their own mode. A file
  that is locked is not removed or moved (`NoModificationAllowedError`).
* **A path maps to a pod resource.** A path is the segments of an LWS path (`LWS.Model`:
  a directory is a container, a file a data resource with its bytes); the record
  docs/designissues/2026-11-14-client-storage.md, "Backends", says what a pod backend must
  prove.

The file pickers of the File System Access API are command `picker`, answered by
`ClientStorage/Picker.lean` (always refused: no host file is ever handed to a page).

Commands (`web_api` op 201; a path is its names joined by `/`, the root is the empty
string): see `op`. Answers are tokens: `ok` and values, or `!` + the exception's name.
-/
import L4Factoidal.ClientStorage.Core
import L4Factoidal.ClientStorage.Picker

namespace L4Factoidal.ClientStorage.Fs

open L4Factoidal.Net.Storage (get set get_set_same get_set_other)

/-- The names from the root of the origin private file system to an entry (the root: `[]`). -/
abbrev Path := List String

inductive Node where
  | dir
  | file (bytes : ByteArray) (modified : Nat)
  deriving Inhabited

def Node.isDir : Node → Bool
  | .dir => true
  | .file _ _ => false

/-- The entries of one storage key, by path. The root is not stored: it always exists. -/
structure Tree where
  entries : List (Path × Node) := []
  deriving Inhabited

def Tree.lookup (t : Tree) (p : Path) : Option Node := if p == [] then some .dir else get t.entries p
def Tree.put (t : Tree) (p : Path) (n : Node) : Tree := { entries := set t.entries p n }
/-- Without the entry at `p` and everything below it. -/
def Tree.removeAll (t : Tree) (p : Path) : Tree := { entries := t.entries.filter fun e => !p.isPrefixOf e.1 }
/-- The names and kinds (true: directory) of the entries directly in `p`, in the order made. -/
def Tree.children (t : Tree) (p : Path) : List (String × Bool) :=
  t.entries.filterMap fun e =>
    if e.1.length == p.length + 1 && p.isPrefixOf e.1 then some (e.1.getLastD "", e.2.isDir) else none

/-- The bytes the tree holds: the sum of its files' sizes. -/
def Tree.usage (t : Tree) : Nat :=
  sizeSum (fun e : Path × Node => match e.2 with | .file b _ => b.size | .dir => 0) t.entries

/-- A valid file name (fs §2.1): not empty, not `.` or `..`, and no path separator. -/
def validName (n : String) : Bool := n != "" && n != "." && n != ".." && !n.any fun c => c == '/' || c == '\\'

/-- A writable file stream: its file, its swap buffer, its position. -/
structure Writable where
  id : Nat
  path : Path
  buf : ByteArray
  pos : Nat := 0
  exclusive : Bool := false
  deriving Inhabited

/-- A sync access handle: its file, its mode (0 `readwrite`, 1 `read-only`, 2
`readwrite-unsafe`) and its cursor. -/
structure Access where
  id : Nat
  path : Path
  mode : Nat
  pos : Nat := 0
  deriving Inhabited

structure Live where
  writables : List Writable := []
  accesses : List Access := []
  next : Nat := 1
  /-- Counts the changes: the `lastModified` of a file is the count at its last change (no
  clock is read). -/
  clock : Nat := 1
  deriving Inhabited

structure Shelf where
  tree : Tree := {}
  live : Live := {}
  deriving Inhabited

instance : Usage Shelf := ⟨fun s => s.tree.usage⟩

/-! ## Tokens -/

abbrev Tok := ByteArray
def S (x : String) : Tok := x.toUTF8
def N (n : Nat) : Tok := (toString n).toUTF8
def ok (xs : List Tok := []) : List Tok := S "ok" :: xs
def fail (name : String) : List Tok := [S ("!" ++ name)]
def strAt (a : Array Tok) (i : Nat) : String := (String.fromUTF8? (a.getD i ByteArray.empty)).getD ""
def natAt (a : Array Tok) (i : Nat) : Nat := (strAt a i).toNat?.getD 0
def pathOf (s : String) : Path := if s == "" then [] else s.splitOn "/"
def pathStr (p : Path) : String := "/".intercalate p

/-! ## Locks, bytes -/

/-- The lock class a holder has on its file: 0 siloed writable, 1 exclusive writable, 2
`readwrite` access handle, 3 `read-only`, 4 `readwrite-unsafe`. -/
def holders (l : Live) (p : Path) : List Nat :=
  (l.writables.filter (·.path == p)).map (fun w => if w.exclusive then 1 else 0) ++
  (l.accesses.filter (·.path == p)).map (fun a => a.mode + 2)

/-- A new holder of class `c` may take the lock: the file is free, or held only by its own
class and that class shares. -/
def mayLock (l : Live) (p : Path) (c : Nat) : Bool :=
  (holders l p).all fun h => h == c && (c == 0 || c == 3 || c == 4)

/-- An entry at or below `p` is locked. -/
def lockedUnder (l : Live) (p : Path) : Bool :=
  l.writables.any (fun w => p.isPrefixOf w.path) || l.accesses.any (fun a => p.isPrefixOf a.path)

/-- `data` written into `buf` at `pos` (a gap is filled with zero bytes). -/
def splice (buf : ByteArray) (pos : Nat) (data : ByteArray) : ByteArray :=
  let head := if pos ≤ buf.size then buf.extract 0 pos else buf ++ ByteArray.mk (Array.replicate (pos - buf.size) 0)
  head ++ data ++ buf.extract (pos + data.size) buf.size

/-- `buf` cut or zero-filled to `size` bytes. -/
def resize (buf : ByteArray) (size : Nat) : ByteArray :=
  if size ≤ buf.size then buf.extract 0 size else buf ++ ByteArray.mk (Array.replicate (size - buf.size) 0)

/-! ## The writable's steps: they never touch the tree -/

/-- `wwrite id pos data`, `wseek id pos`, `wtrunc id size`, `wabort id`: a step of a
writable on its swap buffer. -/
def wstep (quota : Nat) (l : Live) (a : Array Tok) : Live × List Tok :=
  let id := natAt a 1
  match l.writables.find? (·.id == id) with
  | none => (l, fail "TypeError")
  | some w =>
    let setW (w : Writable) : Live := { l with writables := l.writables.map fun x => if x.id == id then w else x }
    match strAt a 0 with
    | "wwrite" =>
      let pos := (strAt a 2).toNat?.getD w.pos
      let data := a.getD 3 ByteArray.empty
      if pos + data.size > quota then ({ l with writables := l.writables.filter (·.id != id) }, fail "QuotaExceededError")
      else (setW { w with buf := splice w.buf pos data, pos := pos + data.size }, ok)
    | "wseek" => (setW { w with pos := natAt a 2 }, ok)
    | "wtrunc" =>
      let size := natAt a 2
      if size > quota then ({ l with writables := l.writables.filter (·.id != id) }, fail "QuotaExceededError")
      else (setW { w with buf := resize w.buf size, pos := min w.pos size }, ok)
    | _ => ({ l with writables := l.writables.filter (·.id != id) }, ok)

def isWritableStep (c : String) : Bool := c == "wwrite" || c == "wseek" || c == "wtrunc" || c == "wabort"

/-- `wclose id`: the file's bytes become the swap buffer, in one step; refused (and the
tree unchanged) when the stream is not open, its directory is gone, or the quota would be
passed. The lock is released either way. -/
def wclose (quota : Nat) (s : Shelf) (id : Nat) : Shelf × List Tok :=
  match s.live.writables.find? (·.id == id) with
  | none => (s, fail "TypeError")
  | some w =>
    let live := { s.live with writables := s.live.writables.filter (·.id != id), clock := s.live.clock + 1 }
    let after := s.tree.put w.path (.file w.buf s.live.clock)
    if (s.tree.lookup w.path.dropLast).isNone then ({ s with live }, fail "NotFoundError")
    else if after.usage > quota && after.usage > s.tree.usage then ({ s with live }, fail "QuotaExceededError")
    else ({ tree := after, live }, ok)

/-! ## The other commands -/

/-- A command that is neither a writable's step nor its close. -/
def other (quota : Nat) (s : Shelf) (a : Array Tok) : Shelf × List Tok :=
  let t := s.tree
  let l := s.live
  let tick (tree : Tree) : Shelf := { tree, live := { l with clock := l.clock + 1 } }
  match strAt a 0 with
  | "root" => (s, ok)
  -- File System Access `queryPermission`/`requestPermission`: every handle here is of the origin
  -- private file system of the caller's own storage key, so read and readwrite are granted
  | "perm" => (s, ok [S (if strAt a 1 == "read" || strAt a 1 == "readwrite" then "granted" else "denied")])
  | "picker" => (s, [S (Picker.answer ((a.toList.drop 1).map fun b => (String.fromUTF8? b).getD ""))])
  | "usage" => (s, ok [N t.usage, N quota])
  | "same" => (s, ok [S (if strAt a 1 == strAt a 3 && strAt a 2 == strAt a 4 then "1" else "0")])
  | "resolve" =>
    let d := pathOf (strAt a 1)
    let e := pathOf (strAt a 2)
    (s, if d.isPrefixOf e then ok ((e.drop d.length).map S) else [S "null"])
  | "get" =>
    -- get dir name kind(d|f) create
    let name := strAt a 2
    let p := pathOf (strAt a 1) ++ [name]
    let wantDir := strAt a 3 == "d"
    if !validName name then (s, fail "TypeError")
    else if !((t.lookup p.dropLast).map (·.isDir)).getD false then (s, fail "NotFoundError")
    else
      match t.lookup p with
      | some n => if n.isDir == wantDir then (s, ok) else (s, fail "TypeMismatchError")
      | none =>
        if strAt a 4 != "1" then (s, fail "NotFoundError")
        else (tick (t.put p (if wantDir then .dir else .file ByteArray.empty l.clock)), ok)
  | "list" =>
    let p := pathOf (strAt a 1)
    if !((t.lookup p).map (·.isDir)).getD false then (s, fail "NotFoundError")
    else (s, ok ((t.children p).flatMap fun c => [S c.1, S (if c.2 then "d" else "f")]))
  | "remove" =>
    -- remove dir name recursive: the entry `name` of `dir` (`removeEntry`); with the name
    -- empty, the entry at `dir` itself (`remove()` of a handle; the root: its contents)
    let name := strAt a 2
    let p := if name == "" then pathOf (strAt a 1) else pathOf (strAt a 1) ++ [name]
    let recursive := strAt a 3 == "1"
    if name != "" && !validName name then (s, fail "TypeError")
    else if name != "" && !((t.lookup p.dropLast).map (·.isDir)).getD false then (s, fail "NotFoundError")
    else
      match t.lookup p with
      | none => (s, fail "NotFoundError")
      | some n =>
        if lockedUnder l p then (s, fail "NoModificationAllowedError")
        else if n.isDir && !recursive && !(t.children p).isEmpty then (s, fail "InvalidModificationError")
        else (tick (t.removeAll p), ok)
  | "stat" =>
    match t.lookup (pathOf (strAt a 1)) with
    | some (.file b m) => (s, ok [N m, b])
    | _ => (s, fail "NotFoundError")
  | "move" =>
    -- move path newDir newName
    let p := pathOf (strAt a 1)
    let name := strAt a 3
    let q := pathOf (strAt a 2) ++ [name]
    if !validName name then (s, fail "TypeError")
    else
      match t.lookup p, p with
      | none, _ | _, [] => (s, fail "NotFoundError")
      | some n, _ =>
        if !((t.lookup q.dropLast).map (·.isDir)).getD false then (s, fail "NotFoundError")
        else if lockedUnder l p || lockedUnder l q then (s, fail "NoModificationAllowedError")
        else if p == q then (s, ok)
        else if p.isPrefixOf q || ((t.lookup q).map (·.isDir)).getD false || (n.isDir && (t.lookup q).isSome) then
          (s, fail "InvalidModificationError")
        else
          let moved := (t.entries.filter fun e => p.isPrefixOf e.1).map fun e => (q ++ e.1.drop p.length, e.2)
          let rest := ((t.removeAll p).removeAll q).entries
          (tick { entries := rest ++ moved }, ok)
  | "wopen" =>
    -- wopen path keepExistingData exclusive
    let p := pathOf (strAt a 1)
    match t.lookup p with
    | some (.file b _) =>
      let c := if strAt a 3 == "1" then 1 else 0
      if !mayLock l p c then (s, fail "NoModificationAllowedError")
      else
        let w : Writable := { id := l.next, path := p, buf := if strAt a 2 == "1" then b else ByteArray.empty, exclusive := c == 1 }
        ({ s with live := { l with writables := w :: l.writables, next := l.next + 1 } }, ok [N w.id])
    | _ => (s, fail "NotFoundError")
  | "aopen" =>
    -- aopen path mode
    let p := pathOf (strAt a 1)
    match t.lookup p with
    | some (.file _ _) =>
      let mode := natAt a 2
      if !mayLock l p (mode + 2) then (s, fail "NoModificationAllowedError")
      else ({ s with live := { l with accesses := { id := l.next, path := p, mode } :: l.accesses, next := l.next + 1 } }, ok [N l.next])
    | _ => (s, fail "NotFoundError")
  | "aclose" => ({ s with live := { l with accesses := l.accesses.filter (·.id != natAt a 1) } }, ok)
  | "aread" | "awrite" | "atrunc" | "asize" | "aflush" =>
    match l.accesses.find? (·.id == natAt a 1) with
    | none => (s, fail "InvalidStateError")
    | some h =>
      match t.lookup h.path with
      | some (.file b _) =>
        let setPos (pos : Nat) : Live := { l with accesses := l.accesses.map fun x => if x.id == h.id then { x with pos } else x }
        match strAt a 0 with
        | "asize" => (s, ok [N b.size])
        | "aflush" => (s, ok)
        | "aread" =>
          let off := (strAt a 2).toNat?.getD h.pos
          let out := b.extract off (off + natAt a 3)
          ({ s with live := setPos (off + out.size) }, ok [out])
        | "awrite" =>
          let off := (strAt a 2).toNat?.getD h.pos
          let data := a.getD 3 ByteArray.empty
          let after := t.put h.path (.file (splice b off data) l.clock)
          if h.mode == 1 then (s, fail "NoModificationAllowedError")
          else if after.usage > quota && after.usage > t.usage then (s, fail "QuotaExceededError")
          else ({ tree := after, live := { setPos (off + data.size) with clock := l.clock + 1 } }, ok [N data.size])
        | _ =>
          let size := natAt a 2
          let after := t.put h.path (.file (resize b size) l.clock)
          if h.mode == 1 then (s, fail "NoModificationAllowedError")
          else if after.usage > quota && after.usage > t.usage then (s, fail "QuotaExceededError")
          else ({ tree := after, live := { setPos (min h.pos size) with clock := l.clock + 1 } }, ok)
      | _ => (s, fail "NotFoundError")
  | _ => (s, fail "NotSupportedError")

/-- One command on the shelf of a storage key. -/
def op (quota : Nat) (s : Shelf) (a : Array Tok) : Shelf × List Tok :=
  if isWritableStep (strAt a 0) then
    let r := wstep quota s.live a
    ({ s with live := r.1 }, r.2)
  else if strAt a 0 == "wclose" then wclose quota s (natAt a 1)
  else other quota s a

/-- One command for the context whose storage key is `k`, on the in-memory shed. -/
def opFor (shed : Shed Shelf) (k : ClientStorage.Key) (a : Array Tok) : Shed Shelf × List Tok :=
  shed.act k (fun s => op defaultQuota s a) (fail "SecurityError")

/-! ## Theorems -/

/-- Kind: file system law (swap-file semantics). Says: a `write`, `seek`, `truncate` or
`abort` of a writable leaves the tree exactly as it was: nothing written through a writable
is visible (to `getFile`, to another handle, to `StorageManager`) before `close`. Does not
say: anything about a sync access handle, which writes in place by design. -/
theorem writable_tree (quota : Nat) (s : Shelf) (a : Array Tok) (h : isWritableStep (strAt a 0) = true) :
    (op quota s a).1.tree = s.tree := by
  simp [op, h]

/-- Kind: file system law (close is atomic). Says: `close` of a writable either leaves the
tree as it was (and fails), or replaces the bytes of the writable's one file by its buffer
and changes nothing else in the same step. Does not say: anything of durability. -/
theorem close_atomic (quota : Nat) (s : Shelf) (a : Array Tok) (h : strAt a 0 = "wclose") :
    (op quota s a).1.tree = s.tree ∨
      ∃ w m, s.live.writables.find? (·.id == natAt a 1) = some w ∧ (op quota s a).1.tree = s.tree.put w.path (.file w.buf m) := by
  have hop : op quota s a = wclose quota s (natAt a 1) := by unfold op; rw [h]; simp [isWritableStep]
  rw [hop]
  unfold wclose
  cases hf : s.live.writables.find? (·.id == natAt a 1) with
  | none => exact .inl rfl
  | some w =>
    dsimp only
    by_cases h1 : (s.tree.lookup w.path.dropLast).isNone = true
    · rw [if_pos h1]; exact .inl rfl
    · rw [if_neg h1]
      by_cases h2 : ((s.tree.put w.path (.file w.buf s.live.clock)).usage > quota &&
          (s.tree.put w.path (.file w.buf s.live.clock)).usage > s.tree.usage) = true
      · rw [if_pos h2]; exact .inl rfl
      · rw [if_neg h2]; exact .inr ⟨w, _, rfl, rfl⟩

/-- Kind: functional law. Says: after an entry is put, its path reads it. -/
theorem lookup_put_same (t : Tree) (p : Path) (n : Node) (h : p ≠ []) : ((t.put p n).lookup p).isSome := by
  have hp : (p == []) = false := by simpa using h
  simp [Tree.lookup, Tree.put, hp, get_set_same]

/-- Kind: file system law. Says: putting an entry changes what no other path reads: a
`close` or a create changes one path only. -/
theorem lookup_put_other (t : Tree) (p q : Path) (n : Node) (h : p ≠ q) : (t.put p n).lookup q = t.lookup q := by
  have hk : (p == q) = false := by simpa using h
  simp [Tree.lookup, Tree.put, get_set_other _ _ _ _ hk]

/-- Kind: file system law. Says: `resolve` answers a relative path exactly when the entry
is the directory itself or inside it, and that path leads from the directory to the entry. -/
theorem resolve_iff (d e r : Path) : (d.isPrefixOf e = true ∧ e.drop d.length = r) ↔ e = d ++ r := by
  constructor
  · rintro ⟨hp, hr⟩
    have := List.prefix_iff_eq_append.mp (List.isPrefixOf_iff_prefix.mp hp)
    rw [← hr]; exact this.symm
  · intro h
    subst h
    exact ⟨List.isPrefixOf_iff_prefix.mpr (List.prefix_append d r), by simp⟩

/-- Kind: file system law. Says: removing an entry (with everything below it) changes what
no path outside it reads. -/
theorem removeAll_lookup_other (t : Tree) (p q : Path) (h : p.isPrefixOf q = false) :
    (t.removeAll p).lookup q = t.lookup q := by
  unfold Tree.lookup Tree.removeAll L4Factoidal.Net.Storage.get
  by_cases hq : (q == []) = true
  · simp [hq]
  · simp only [hq]
    rw [List.find?_filter]
    have hfun : ∀ e : Path × Node, (decide ((!p.isPrefixOf e.1) = true ∧ (e.1 == q) = true)) = (e.1 == q) := by
      intro e
      by_cases he : e.1 = q
      · subst he; simp [h]
      · simp [he]
    simp only [hfun]

/-- Kind: file system law. Says: after an entry is removed, no path at or below it reads
anything (the root's own path apart). -/
theorem removeAll_lookup_under (t : Tree) (p q : Path) (h : p.isPrefixOf q = true) (hq : q ≠ []) :
    (t.removeAll p).lookup q = none := by
  have hq' : (q == []) = false := by simpa using hq
  unfold Tree.lookup Tree.removeAll L4Factoidal.Net.Storage.get
  simp only [hq']
  rw [List.find?_filter]
  have hfun : ∀ e : Path × Node, (decide ((!p.isPrefixOf e.1) = true ∧ (e.1 == q) = true)) = false := by
    intro e
    by_cases he : e.1 = q
    · subst he; simp [h]
    · simp [he]
  simp only [hfun]
  simp

/-- Kind: security invariant (no path leaves the root). Says: a name that is not valid
(empty, `.`, `..`, or with `/` or `\`) is refused with `TypeError` by `get` and the shelf
is unchanged, so no entry is ever made under such a name. Does not say: anything about a
host file system (there is none behind this tree). -/
theorem get_invalid_name (quota : Nat) (s : Shelf) (a : Array Tok) (hc : strAt a 0 = "get")
    (hn : validName (strAt a 2) = false) : op quota s a = (s, fail "TypeError") := by
  have hop : op quota s a = other quota s a := by unfold op; rw [hc]; simp [isWritableStep]
  rw [hop]
  unfold other
  simp [hc, hn]

/-- Kind: file system law. Says: `isSameEntry` is equality of path and kind, so it is
reflexive, symmetric and transitive. -/
theorem same_iff (quota : Nat) (s : Shelf) (a : Array Tok) (hc : strAt a 0 = "same") :
    (op quota s a).2 = ok [S "1"] ↔ (strAt a 1 = strAt a 3 ∧ strAt a 2 = strAt a 4) := by
  have hop : op quota s a = other quota s a := by unfold op; rw [hc]; simp [isWritableStep]
  rw [hop]
  unfold other
  simp only [hc]
  by_cases h : (strAt a 1 == strAt a 3 && strAt a 2 == strAt a 4) = true
  · simp only [h, if_true, true_iff]; simpa using h
  · have hne : ¬(strAt a 1 = strAt a 3 ∧ strAt a 2 = strAt a 4) := by simpa using h
    simp only [h, hne, iff_false]
    decide

/-- Kind: accounting law. Says: the usage of a shelf is the sum of the sizes of its stored
files (directories and open swap buffers count nothing). -/
theorem usage_eq (s : Shelf) :
    Usage.usage s = sizeSum (fun e : Path × Node => match e.2 with | .file b _ => b.size | .dir => 0) s.tree.entries := rfl

/-- Kind: security theorem (the file system is partitioned by storage key). Says: whatever
a context with one storage key does to its file system, the answer another key then gets
for any command is the answer it would have got without it: no file, name, size or id of
one key is read under another. Does not say: anything about two contexts with one key. -/
theorem opFor_noninterference (shed : Shed Shelf) (k k' : ClientStorage.Key) (a a' : Array Tok) (h : k ≠ k') :
    (opFor (opFor shed k a).1 k' a').2 = (opFor shed k' a').2 :=
  act_noninterference Shed.laws shed k k' _ _ _ _ h

/-! ## Checks (WPT fs/script-tests) -/

private def T (xs : List String) : Array Tok := (xs.map String.toUTF8).toArray
private def shown (r : List Tok) : String := " ".intercalate (r.map fun t => (String.fromUTF8? t).getD "?")
private def answers (s : Shelf) (cmds : List (List String)) : Shelf × List String :=
  cmds.foldl (fun (acc : Shelf × List String) c =>
    let (s, r) := op 100 acc.1 (T c)
    (s, acc.2 ++ [shown r])) (s, [])

private def s1 : Shelf := (answers {} [["get", "", "dir", "d", "1"], ["get", "dir", "a.txt", "f", "1"], ["get", "", "b", "f", "1"]]).1
#guard (answers {} [["get", "", "dir", "d", "1"], ["get", "dir", "a.txt", "f", "1"], ["get", "", "b", "f", "1"]]).2 == ["ok", "ok", "ok"]
#guard (answers s1 [["perm", "read"], ["perm", "readwrite"], ["perm", "x"]]).2 == ["ok granted", "ok granted", "ok denied"]
-- the pickers: refused, and the shelf is unchanged
#guard (answers s1 [["picker", "open", "0", "", ""], ["picker", "save", "1", "", ""], ["list", ""]]).2 == ["!SecurityError", "!TypeError", "ok dir d b f"]
#guard (answers s1 [["list", ""], ["list", "dir"], ["list", "nope"]]).2 == ["ok dir d b f", "ok a.txt f", "!NotFoundError"]
#guard (answers s1 [["get", "", "dir", "f", "0"], ["get", "", "b", "d", "1"], ["get", "", "zz", "f", "0"], ["get", "nope", "x", "f", "1"]]).2 ==
  ["!TypeMismatchError", "!TypeMismatchError", "!NotFoundError", "!NotFoundError"]
#guard (answers s1 [["get", "", "..", "f", "1"], ["get", "", ".", "d", "1"], ["get", "", "", "f", "1"], ["get", "", "a/b", "f", "1"], ["get", "", "a\\b", "f", "1"]]).2 ==
  ["!TypeError", "!TypeError", "!TypeError", "!TypeError", "!TypeError"]
#guard (answers s1 [["resolve", "", "dir/a.txt"], ["resolve", "dir", "dir/a.txt"], ["resolve", "dir", "dir"], ["resolve", "dir", "b"], ["same", "dir", "d", "dir", "d"], ["same", "dir", "d", "b", "f"]]).2 ==
  ["ok dir a.txt", "ok a.txt", "ok", "null", "ok 1", "ok 0"]
-- a writable: nothing is seen before close; close replaces the bytes; abort leaves them
private def w1 : List (List String) := [["wopen", "dir/a.txt", "0", "0"], ["wwrite", "1", "", "hello"], ["wwrite", "1", "0", "J"], ["wseek", "1", "7"], ["wwrite", "1", "", "!"]]
#guard (answers s1 (w1 ++ [["stat", "dir/a.txt"], ["usage"]])).2.drop 5 == ["ok 2 ", "ok 0 100"]
#guard (answers s1 (w1 ++ [["wclose", "1"], ["stat", "dir/a.txt"], ["usage"], ["wwrite", "1", "", "x"]])).2.drop 5 ==
  ["ok", "ok 4 Jello\x00\x00!", "ok 8 100", "!TypeError"]
#guard (answers s1 (w1 ++ [["wabort", "1"], ["stat", "dir/a.txt"]])).2.drop 5 == ["ok", "ok 2 "]
#guard (answers s1 (w1 ++ [["wtrunc", "1", "2"], ["wclose", "1"], ["stat", "dir/a.txt"]])).2.drop 7 == ["ok 4 Je"]
-- locks: siloed writables share; an exclusive one does not; a locked file is not removed; the quota
#guard (answers s1 [["wopen", "b", "1", "0"], ["wopen", "b", "1", "0"], ["wopen", "b", "1", "1"], ["aopen", "b", "0"], ["remove", "", "b", "0"], ["remove", "", "", "1"],
  ["wabort", "1"], ["wabort", "2"], ["wopen", "b", "1", "1"], ["wopen", "b", "1", "0"], ["wclose", "3"], ["aopen", "b", "0"], ["aopen", "b", "0"]]).2 ==
  ["ok 1", "ok 2", "!NoModificationAllowedError", "!NoModificationAllowedError", "!NoModificationAllowedError", "!NoModificationAllowedError",
   "ok", "ok", "ok 3", "!NoModificationAllowedError", "ok", "ok 4", "!NoModificationAllowedError"]
#guard (answers s1 [["wopen", "b", "0", "0"], ["wwrite", "1", "", String.ofList (List.replicate 101 'x')], ["wwrite", "1", "", "y"]]).2 ==
  ["ok 1", "!QuotaExceededError", "!TypeError"]
-- remove, move
#guard (answers s1 [["remove", "", "dir", "0"], ["remove", "", "dir", "1"], ["list", ""], ["remove", "", "dir", "0"], ["remove", "", "", "1"], ["list", ""],
  ["remove", "", "a/b", "0"], ["remove", "nope", "x", "0"]]).2 ==
  ["!InvalidModificationError", "ok", "ok b f", "!NotFoundError", "ok", "ok", "!TypeError", "!NotFoundError"]
#guard (answers s1 [["remove", "dir", "", "0"], ["remove", "dir/a.txt", "", "0"], ["remove", "dir", "", "0"], ["list", ""]]).2 ==
  ["!InvalidModificationError", "ok", "ok", "ok b f"]
#guard (answers s1 [["move", "dir/a.txt", "", "c.txt"], ["list", ""], ["list", "dir"], ["move", "dir", "", "d2"], ["list", ""], ["move", "b", "d2", "inner"], ["list", "d2"],
  ["move", "d2", "d2", "x"], ["move", "nope", "", "y"], ["move", "c.txt", "", "a/b"]]).2 ==
  ["ok", "ok dir d b f c.txt f", "ok", "ok", "ok b f c.txt f d2 d", "ok", "ok inner f", "!InvalidModificationError", "!NotFoundError", "!TypeError"]
-- a sync access handle writes in place
#guard (answers s1 [["aopen", "b", "0"], ["awrite", "1", "", "abcdef"], ["aread", "1", "2", "3"], ["asize", "1"], ["atrunc", "1", "2"], ["aread", "1", "0", "9"], ["aclose", "1"], ["asize", "1"]]).2 ==
  ["ok 1", "ok 6", "ok cde", "ok 6", "ok", "ok ab", "ok", "!InvalidStateError"]

end L4Factoidal.ClientStorage.Fs
