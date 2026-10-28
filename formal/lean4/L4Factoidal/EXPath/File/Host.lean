/-
L4Factoidal.EXPath.File.Host — the host interface of the EXPath File
Module 4.0: the file-system operations the `file:` functions need, as
a structure of operations in a monad `m`. The semantics of the
`file:` functions (`EXPath.File.Ops`) are written once against this
interface; the evaluator never does I/O itself.

Two instances:

* `memHost` — the pure in-memory file system `EXPath.File.FS`, in the
  monad `StateT FS M`. The `#guard`s, the theorems and the qt4tests
  runner use it (the runner loads the test set's `sandpit` directory
  into an `FS` and every write stays in memory).
* `ioHost` (`EXPath.File.IOHost`) — the real file system under one
  sandbox directory, in `ExceptT Err IO`. A path is mapped below the
  sandbox root, so no operation reaches a file outside it.
-/
import L4Factoidal.XPath4.Atomic
import L4Factoidal.EXPath.File.FS

namespace L4Factoidal.EXPath.File

open L4Factoidal.XPath4

/-- What `stat` reports: a regular file with its size, or a directory;
    with the last modification time as an `xs:dateTime` lexical form. -/
inductive Stat where
  | file (size : Nat) (mtime : String)
  | dir (mtime : String)
deriving Repr, Inhabited, BEq

def Stat.isDir : Stat → Bool | .dir _ => true | _ => false
def Stat.mtime : Stat → String | .file _ t => t | .dir t => t

/-- The file-system operations. Each works on one entry; the parent
    checks, recursion and error codes are in `EXPath.File.Ops`. -/
structure Host (m : Type → Type) where
  /-- The entry at a path, if any. -/
  stat : Path → m (Option Stat)
  /-- The octets of a regular file. -/
  read : Path → m (List Nat)
  /-- Create or replace a regular file (its parent is a directory). -/
  write : Path → List Nat → m Unit
  /-- Create one directory (its parent is a directory). -/
  mkdir : Path → m Unit
  /-- Remove a regular file or an empty directory. -/
  remove : Path → m Unit
  /-- The names in a directory, sorted. -/
  list : Path → m (List String)
  /-- A number not returned before (for temporary names). -/
  fresh : m Nat
  /-- The current working directory. -/
  cwd : Path
  /-- The default temporary-file directory. -/
  tmp : Path

/-- An `M` value in any monad that can throw `Err`. -/
def liftM' {m : Type → Type} [Monad m] [MonadExceptOf Err m] {α} (x : M α) : m α :=
  match x with
  | .ok a => pure a
  | .error e => throw e

/-! ## The in-memory instance -/

abbrev MemM := StateT FS M

def Entry.stat : Entry → Stat
  | .file bs t => .file bs.length t
  | .dir t => .dir t

/-- The in-memory host. `now` is the time every write records. -/
def memHost (fs0 : FS) (now : String) : Host MemM where
  stat p := do pure ((← get).get p |>.map Entry.stat)
  read p := do
    match (← get).get p with
    | some (.file bs _) => pure bs
    | _ => throw { code := "Q{http://expath.org/ns/file}io-error", msg := "not a regular file" }
  write p bs := modify (·.put p (.file bs now))
  mkdir p := modify (·.put p (.dir now))
  remove p := modify (·.erase p)
  list p := do pure ((← get).children p |>.map (·.1))
  fresh := do
    let fs ← get
    set { fs with next := fs.next + 1 }
    pure fs.next
  cwd := fs0.cwd
  tmp := fs0.tmp

end L4Factoidal.EXPath.File
