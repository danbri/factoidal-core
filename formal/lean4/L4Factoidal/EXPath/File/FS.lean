/-
L4Factoidal.EXPath.File.FS — an in-memory file system: the state that
the EXPath File Module 4.0 functions read and change when they run in
the pure evaluator.

A PATH is a list of segments from the root (`[]` is the root
directory `/`). An ENTRY is a regular file (its octets and its last
modification time) or a directory (its last modification time). The
root directory always exists and is not stored. An entry whose parent
directory is not stored is not reachable by any operation of
`EXPath.File.Ops`, which keeps the invariant that every stored entry's
parent is a stored directory or the root.

The theorems (write then read, isolation of other paths) are in
`EXPath.File.Theorems`. The real file system is reached only through
`EXPath.File.Host.ioHost`, which maps the same paths under a sandbox
directory.
-/
namespace L4Factoidal.EXPath.File

/-- A path from the root: its segments. -/
abbrev Path := List String

inductive Entry where
  | file (bytes : List Nat) (mtime : String)
  | dir (mtime : String)
deriving Repr, Inhabited, BEq

def Entry.isDir : Entry → Bool | .dir _ => true | _ => false
def Entry.mtime : Entry → String | .file _ t => t | .dir t => t

structure FS where
  /-- The entries other than the root, newest first. At most one entry
      per path (`put` removes the old one). -/
  entries : List (Path × Entry) := []
  /-- The current working directory (EXPath File 4.0 § file:current-dir). -/
  cwd : Path := []
  /-- The default temporary-file directory (§ file:temp-dir). -/
  tmp : Path := ["tmp"]
  /-- A counter for the names of temporary files and directories. -/
  next : Nat := 0
deriving Inhabited

namespace FS

/-- The entry at a path. The root is a directory. -/
def get (fs : FS) (p : Path) : Option Entry :=
  if p.isEmpty then some (.dir "") else fs.entries.lookup p

/-- Store an entry at a path, replacing the entry that was there. -/
def put (fs : FS) (p : Path) (e : Entry) : FS :=
  { fs with entries := (p, e) :: fs.entries.filter (fun x => x.1 != p) }

/-- Remove the entry at a path (not its descendants). -/
def erase (fs : FS) (p : Path) : FS :=
  { fs with entries := fs.entries.filter (fun x => x.1 != p) }

/-- The names and entries directly inside a directory, sorted by name. -/
def children (fs : FS) (p : Path) : List (String × Entry) :=
  let cs := fs.entries.filterMap (fun (q, e) =>
    if q.length == p.length + 1 && p.isPrefixOf q then some (q.getLast?.getD "", e) else none)
  cs.mergeSort (fun a b => decide (a.1 ≤ b.1))

/-- Every stored path at or below `p` (`p` itself included when stored). -/
def subtree (fs : FS) (p : Path) : List (Path × Entry) :=
  fs.entries.filter (fun x => p.isPrefixOf x.1)

end FS

/-! ## Path strings (UNIX form) -/

/-- Decode `%XX` escapes (in a `file:` URI). -/
def percentDecode (s : String) : String :=
  let hex (c : Char) : Option Nat :=
    if '0' ≤ c && c ≤ '9' then some (c.toNat - 48)
    else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
    else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55) else none
  let rec go : List Char → List Nat → List Nat
    | '%' :: a :: b :: r, acc =>
      match hex a, hex b with
      | some x, some y => go r ((x * 16 + y) :: acc)
      | _, _ => go (a :: b :: r) ('%'.toNat :: acc)
    | c :: r, acc => go r ((String.singleton c).toUTF8.data.toList.reverse.map (·.toNat) ++ acc)
    | [], acc => acc
  let bytes := (go s.toList []).reverse
  (String.fromUTF8? (ByteArray.mk (bytes.map UInt8.ofNat).toArray)).getD s

/-- The path part of a `file:` URI (`file:///a/b`, `file://localhost/a`,
    `file:/a`), decoded; `none` when `s` is not a `file:` URI. -/
def fileUriPath? (s : String) : Option String :=
  if s.startsWith "file://" then
    let rest := (s.drop 7).toString
    let rest := if rest.startsWith "localhost/" then (rest.drop 9).toString else rest
    some (percentDecode rest)
  else if s.startsWith "file:/" then some (percentDecode (s.drop 5).toString)
  else none

/-- Whether a path string is absolute (§ file:is-absolute): it starts
    with `/`, or it is a `file:` URI. -/
def isAbsolute (s : String) : Bool := s.startsWith "/" || (fileUriPath? s).isSome

/-- Resolve a path string against a base directory: `.` and empty
    segments are dropped, `..` removes the segment before it (and
    stays at the root). -/
def resolveSegs (base : Path) (s : String) : Path :=
  let s := (fileUriPath? s).getD s
  let start : Path := if s.startsWith "/" then [] else base
  (s.splitOn "/").foldl (fun acc seg =>
    if seg == "" || seg == "." then acc
    else if seg == ".." then acc.dropLast
    else acc ++ [seg]) start

/-- The string of an absolute path; a directory gets a trailing `/`. -/
def pathStr (p : Path) (isDir : Bool := false) : String :=
  let s := "/" ++ String.intercalate "/" p
  if isDir && !p.isEmpty then s ++ "/" else s

#guard resolveSegs ["a", "b"] "../c/./d" == ["a", "c", "d"]
#guard resolveSegs ["a"] "/x//y/" == ["x", "y"]
#guard resolveSegs [] "file:///tmp/a%20b" == ["tmp", "a b"]
#guard pathStr ["a", "b"] true == "/a/b/"
#guard (({} : FS).put ["a"] (.dir "t")).get ["a"] == some (.dir "t")

end L4Factoidal.EXPath.File
