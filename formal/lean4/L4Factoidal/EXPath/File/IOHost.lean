/-
L4Factoidal.EXPath.File.IOHost — the host interface of EXPath File 4.0
(`EXPath.File.Host`) over the real file system, confined to one
SANDBOX directory, and the loader that copies a directory tree into
the in-memory file system `EXPath.File.FS`.

Confinement: a path of the host interface is a list of segments from
the virtual root; `real` maps it below the sandbox directory, and the
segments never contain `..` or `/` (`resolveSegs` removes them). A
symbolic link is not followed: `stat` reports it as absent and the
operations refuse it, so no link inside the sandbox leads outside it.
This module is used only by the qt4tests runner (`--file-host io`);
the library evaluator does no I/O.
-/
import L4Factoidal.EXPath.File.Exec

namespace L4Factoidal.EXPath.File

open L4Factoidal.XPath4

/-- `xs:dateTime` (UTC) of a POSIX time in seconds: the civil-from-days
    algorithm of H. Hinnant ("chrono-Compatible Low-Level Date
    Algorithms"). -/
def dateTimeOfPosix (secs : Int) : String :=
  let days := secs / 86400
  let rem := secs % 86400
  let z := days + 719468
  let era := (if z ≥ 0 then z else z - 146096) / 146097
  let doe := z - era * 146097
  let yoe := (doe - doe / 1460 + doe / 36524 - doe / 146096) / 365
  let doy := doe - (365 * yoe + yoe / 4 - yoe / 100)
  let mp := (5 * doy + 2) / 153
  let d := doy - (153 * mp + 2) / 5 + 1
  let mo := if mp < 10 then mp + 3 else mp - 9
  let y := yoe + era * 400 + (if mo ≤ 2 then 1 else 0)
  let p2 (n : Int) : String := (if n < 10 then "0" else "") ++ toString n
  let p4 (n : Int) : String := String.ofList (List.replicate (4 - (toString n).length) '0') ++ toString n
  s!"{p4 y}-{p2 mo}-{p2 d}T{p2 (rem / 3600)}:{p2 (rem % 3600 / 60)}:{p2 (rem % 60)}Z"

#guard dateTimeOfPosix 0 == "1970-01-01T00:00:00Z"
#guard dateTimeOfPosix 1793188800 == "2026-10-28T12:00:00Z"

abbrev IOM := ExceptT Err IO

def ioErr {α} (msg : String) : IOM α := throw { code := "Q{" ++ nsFILE ++ "}io-error", msg }

/-- The real path of a host path under the sandbox `root`. -/
def real (root : String) (p : Path) : System.FilePath :=
  ⟨if p.isEmpty then root else root ++ pathStr p⟩

/-- `stat` without following links: a link is reported as absent. -/
def statReal (root : String) (p : Path) : IO (Option Stat) := do
  try
    let md ← (real root p).symlinkMetadata
    match md.type with
    | .dir => pure (some (.dir (dateTimeOfPosix md.modified.sec)))
    | .file => pure (some (.file md.byteSize.toNat (dateTimeOfPosix md.modified.sec)))
    | _ => pure none
  catch _ => pure none

/-- Run an IO action, turning an IO error into `file:io-error`. -/
def ioTry {α} (x : IO α) : IOM α := do
  match ← (x.toBaseIO) with
  | .ok a => pure a
  | .error e => ioErr (toString e)

/-- The host over the real file system below `root`. `cwd` and `tmp`
    are host paths (below `root`). -/
def ioHost (root : String) (cwd tmp : Path) (ctr : IO.Ref Nat) : Host IOM where
  stat p := statReal root p
  read p := do
    let some (.file _ _) ← statReal root p | ioErr ("not a regular file: " ++ pathStr p)
    let bs ← ioTry (IO.FS.readBinFile (real root p))
    pure (bs.data.toList.map UInt8.toNat)
  write p bs := do
    if let some (.dir _) ← statReal root p then ioErr ("a directory: " ++ pathStr p)
    ioTry (IO.FS.writeBinFile (real root p) (ByteArray.mk (bs.map UInt8.ofNat).toArray))
  mkdir p := ioTry (IO.FS.createDir (real root p))
  remove p := do
    match ← statReal root p with
    | some (.dir _) => ioTry (IO.FS.removeDir (real root p))
    | some (.file _ _) => ioTry (IO.FS.removeFile (real root p))
    | none => ioErr ("no such file or directory: " ++ pathStr p)
  list p := do
    let es ← ioTry (real root p).readDir
    pure ((es.toList.map (·.fileName)).mergeSort (fun a b => decide (a ≤ b)))
  fresh := ctr.modifyGet (fun n => (n, n + 1))
  cwd := cwd
  tmp := tmp

/-- Copy the directory tree at `src` (a real path) into the in-memory
    file system at host path `at_`. Every entry gets the modification
    time `mtime`, or its real one when `mtime` is `none`. Links are not
    followed. A loop over a work list of directories. -/
def loadTree (src : String) (at_ : Path) (fs : FS) (mtime : Option String) : IO FS := do
  let tm (md : IO.FS.Metadata) : String := mtime.getD (dateTimeOfPosix md.modified.sec)
  let mut fs := fs
  let mut todo : List (String × Path) := [(src, at_)]
  -- each directory is read once; the loop ends when the work list is empty
  for _ in [0:100000] do
    match todo with
    | [] => break
    | (d, p) :: rest =>
      todo := rest
      fs := fs.put p (.dir (tm (← (System.FilePath.mk d).symlinkMetadata)))
      for e in ← (System.FilePath.mk d).readDir do
        let md ← e.path.symlinkMetadata
        match md.type with
        | .dir => todo := (e.path.toString, p ++ [e.fileName]) :: todo
        | .file =>
          let bs ← IO.FS.readBinFile e.path
          fs := fs.put (p ++ [e.fileName]) (.file (bs.data.toList.map UInt8.toNat) (tm md))
        | _ => pure ()
  return fs

/-- The in-memory file system of a sandbox root: the tree under `root`
    as host paths, with the real modification times. -/
def snapshotOf (root : String) (fs0 : FS) : IO FS := do
  let mut fs : FS := { fs0 with entries := [] }
  for e in ← (System.FilePath.mk root).readDir do
    let md ← e.path.symlinkMetadata
    match md.type with
    | .dir => fs ← loadTree e.path.toString [e.fileName] fs none
    | .file =>
      let bs ← IO.FS.readBinFile e.path
      fs := fs.put [e.fileName] (.file (bs.data.toList.map UInt8.toNat) (dateTimeOfPosix md.modified.sec))
    | _ => pure ()
  return fs

/-- Evaluate an expression over the real file system under `root`.
    The pure parts read a snapshot of the sandbox taken before each of
    them (`snapshotOf`), so they see every earlier write. -/
def evalIO (root : String) (cwd tmp : Path) (env : Env) (e : Expr) : IO (Except Err Seq) := do
  let ctr ← IO.mkRef 0
  let h := ioHost root cwd tmp ctr
  let snap (env : Env) : IOM Env := do
    let fs ← snapshotOf root { cwd, tmp }
    pure { env with fileSys := some fs }
  (exec h snap 10000 env e).run

/-! ## qt4tests: the `sandpit` environment -/

/-- The host paths of a qt4tests run: the copy of the test set's
    `sandpit` directory is the current working directory
    `/work/sandpit`; the temporary-file directory is `/tmp`. -/
def sandpitCwd : Path := ["work", "sandpit"]
def sandpitTmp : Path := ["tmp"]

/-- The in-memory file system of a test case: the `sandpit` directory
    (a real path) copied to `/work/sandpit`. -/
def sandpitFS (sandpit : String) (mtime : String) : IO FS := do
  let fs : FS := { cwd := sandpitCwd, tmp := sandpitTmp }
  let fs := (fs.put ["work"] (.dir mtime)).put ["tmp"] (.dir mtime)
  loadTree sandpit sandpitCwd fs (some mtime)

/-- Write an in-memory file system out below a real directory. -/
def writeOut (root : String) (fs : FS) : IO Unit := do
  let es := fs.entries.mergeSort (fun a b => a.1.length ≤ b.1.length)
  for (p, e) in es do
    match e with
    | .dir _ => IO.FS.createDirAll (real root p)
    | .file bs _ => IO.FS.writeBinFile (real root p) (ByteArray.mk (bs.map UInt8.ofNat).toArray)

/-- Evaluate a qt4tests test expression with its `sandpit`: over the
    in-memory file system (`useIO` false), or over a copy of the
    sandpit in a new temporary directory that is removed afterwards
    (`useIO` true). Returns the result and the dynamic context with
    the file system after the evaluation, for the assertions. This form
    takes a parsed expression (an XQuery main module body, for example). -/
def evalSandpitExpr (useIO : Bool) (sandpit : String) (env : Env) (e : Expr) : IO (M Seq × Env) := do
  let fs ← sandpitFS sandpit env.now
  -- the test set's directory is `/work` (its `sandpit` is
  -- `/work/sandpit`), so the static base URI, when the environment
  -- gives none, is the test set file there
  let env := if env.baseUri == "" then { env with baseUri := "file:///work/test-set.xml" } else env
  if !useIO then
    match evalMem env fs e with
    | .ok (r, fs') => return (.ok r, { env with fileSys := some fs' })
    | .error x => return (.error x, { env with fileSys := some fs })
  else
    let root ← IO.FS.createTempDir
    try
      writeOut root.toString fs
      -- the real clock: the modification time of the new directory
      let env := { env with now := dateTimeOfPosix (← root.metadata).modified.sec }
      let r ← evalIO root.toString sandpitCwd sandpitTmp env e
      let fs' ← snapshotOf root.toString { cwd := sandpitCwd, tmp := sandpitTmp }
      return (r, { env with fileSys := some fs' })
    finally
      IO.FS.removeDirAll root

def evalSandpit (useIO : Bool) (sandpit : String) (env : Env) (src : String) : IO (M Seq × Env) := do
  match parseXPath src env.ns with
  | .error e => return (.error e, env)
  | .ok e => evalSandpitExpr useIO sandpit env e

end L4Factoidal.EXPath.File
