/-
L4Factoidal.EXPath.Hook — the one entry point through which the XPath
4.0 evaluator finds the EXPath function libraries: `XPath4.Ext`
asks `expathLookup` for any function name outside the `fn:` tables.

A `file:` function called from the pure evaluator runs on the
in-memory file system of the dynamic context (`Env.fileSys`) and
cannot change it: a function that writes is refused there. The
writing functions run in `EXPath.File.Exec`, which orders their
calls (EXPath File 4.0 § Function Execution: such calls must be
"statically explicit" and occur "only in contexts where the order of
execution is predictable").
-/
import L4Factoidal.EXPath.Binary.Lib
import L4Factoidal.EXPath.File.Ops

namespace L4Factoidal.EXPath

open L4Factoidal.XPath4

/-- A `file:` function in the pure evaluator. -/
def fileFnPure (loc : String) : Option LibFn :=
  if File.writingFns.contains loc then
    some (fun _ _ _ => File.fileErr "io-error"
      ("file:" ++ loc ++ " changes the file system; it is evaluated only where the order of evaluation is fixed (EXPath.File.Exec)"))
  else
    ((File.fileTable (File.memHost {} "")).lookup loc).map (fun _ => fun hk env args =>
      match env.fileSys, File.pathOnlyFns.contains loc with
      | none, false => File.fileErr "io-error" "no file system is available to this evaluation"
      | fs?, _ =>
        let fs := fs?.getD {}
        match (File.fileTable (File.memHost fs env.now)).lookup loc with
        | some f => (f hk env args).run' fs
        | none => err "XPST0017" ("unknown function file:" ++ loc))

/-- The implementation of an EXPath Binary 4.0 or File 4.0 function. -/
def expathLookup (q : QN) : Option LibFn :=
  if q.uri == Binary.nsBIN then Binary.binTable.lookup q.loc
  else if q.uri == File.nsFILE then fileFnPure q.loc
  else none

end L4Factoidal.EXPath
