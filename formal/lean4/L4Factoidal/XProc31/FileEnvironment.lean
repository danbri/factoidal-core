import L4Factoidal.XProc31.Core

namespace L4Factoidal.XProc31

def fixtureRelativePath (path : String) : Bool :=
  !path.isEmpty && !path.startsWith "/" && !path.contains '\\' && !path.contains ':' &&
  (path.splitOn "/").all (fun part => part != ".." && part != "." && part != "")

/-- Real copies prevent a tested write from following a fixture symlink back
into the source checkout. Special files and symlinks are refused. -/
def copyFixtureTree : Nat → System.FilePath → System.FilePath → IO Unit
  | 0, _, _ => throw (IO.userError "fixture tree depth limit")
  | fuel+1, source, target => do
    match (← source.symlinkMetadata).type with
    | .dir =>
      IO.FS.createDirAll target
      for entry in ← source.readDir do
        copyFixtureTree fuel entry.path (target / entry.fileName)
    | .file => IO.FS.writeBinFile target (← IO.FS.readBinFile source)
    | _ => throw (IO.userError "fixture symlink or special file is unsupported")

def needsFileEnvironment : Nat → XML.Node → Bool
  | 0, _ => false
  | fuel+1, node =>
    let name := tag node
    name == "file-environment" || name == "store" || name.startsWith "file-" ||
    name == "directory-list" || (kids node).any (needsFileEnvironment fuel)

/-- Materialize only the fixture vocabulary present in this suite. Metadata
settings which cannot be represented by the host IO API stay unsupported. -/
def prepareFileEnvironment (testPath sandbox : String) (root : XML.Node) : IO (Result String) := do
  let entries := (named root "file-environment").flatMap kids
  for entry in entries do
    if !["file", "folder"].contains (tag entry) then
      return unsupported ("file environment instruction " ++ tag entry)
    if !fixtureRelativePath (attr entry "path") then
      return unsupported "file environment path is not confined to the temporary directory"
    if attr entry "hidden" == "true" || attr entry "last-modified" != "" ||
        attr entry "readable" == "false" || attr entry "writable" == "false" then
      return unsupported "file environment permissions, hidden flag or timestamp metadata"
  let source : System.FilePath := testPath
  let some tests := source.parent | return error "" "fixture has no parent directory"
  let some suite := tests.parent | return error "" "fixture has no suite directory"
  let target : System.FilePath := sandbox
  IO.FS.createDirAll (target / "tests")
  for entry in ← suite.readDir do
    if entry.fileName != "tests" && entry.fileName != "testfolder" then
      copyFixtureTree 128 entry.path (target / entry.fileName)
  let file := source.fileName.getD "test.xml"
  let testCopy := target / "tests" / file
  IO.FS.writeBinFile testCopy (← IO.FS.readBinFile source)
  let environment := target / "testfolder"
  IO.FS.createDirAll environment
  for entry in entries do
    let destination := environment / attr entry "path"
    if tag entry == "folder" then IO.FS.createDirAll destination
    else
      if let some parent := destination.parent then IO.FS.createDirAll parent
      IO.FS.writeFile destination entry.textContent
  pure (.ok testCopy.toString)

#guard fixtureRelativePath "a/b.xml"
#guard !fixtureRelativePath "../outside"
#guard !fixtureRelativePath "/absolute"
#guard !fixtureRelativePath "file:///outside"

end L4Factoidal.XProc31
