import Harness.PosixRangeIO

/-!
Native POSIX adapter regressions over a private temporary directory.
These checks exercise the linked C implementation, not a replacement interpreter
or a durability proof. They do not simulate crashes or concurrent writers.
-/

namespace NativeRangeSmoke

open Harness.PosixRangeIO
open L4Factoidal.Storage.IndexedBlockWireV2

private def check (name : String) (valid : Bool) : IO Nat := do
  unless valid do
    throw (IO.userError s!"FAIL {name}")
  IO.println s!"PASS {name}"
  return 1

private def runReads (directory : System.FilePath) : IO Nat := do
  let file := directory / "range.bin"
  let missing := directory / "missing.bin"
  IO.FS.writeBinFile file "abcd".toUTF8
  let signedLimit := 2 ^ 63
  let unsignedLimit := 2 ^ 64
  let rawCases : List (String × UInt64 × UInt64 × ByteArray) :=
    [("middle", 1, 2, "bc".toUTF8),
     ("exact end", 3, 1, "d".toUTF8),
     ("short extent", 3, 2, ByteArray.empty),
     ("past end", 5, 1, ByteArray.empty),
     ("signed start", UInt64.ofNat signedLimit, 1, ByteArray.empty),
     ("signed end", UInt64.ofNat (signedLimit - 1), 2, ByteArray.empty),
     ("UInt64 maximum offset", UInt64.ofNat (unsignedLimit - 1), 1, ByteArray.empty),
     ("UInt64 maximum length", 0, UInt64.ofNat (unsignedLimit - 1), ByteArray.empty)]
  let mut passed := 0
  for (name, offset, length, expected) in rawCases do
    let actual ← preadRaw file.toString offset length
    passed := passed + (← check s!"preadRaw {name}" (actual == expected))
  passed := passed + (← check "preadRaw missing file"
    ((← preadRaw missing.toString 0 1) == ByteArray.empty))
  let checkedCases : List (String × ByteRange × Option ByteArray) :=
    [("middle", { offset := 1, length := 2 }, some "bc".toUTF8),
     ("exact end", { offset := 3, length := 1 }, some "d".toUTF8),
     ("short extent", { offset := 3, length := 2 }, none),
     ("past end", { offset := 5, length := 1 }, none),
     ("signed start", { offset := signedLimit, length := 1 }, none),
     ("signed end", { offset := signedLimit - 1, length := 2 }, none),
     ("Nat offset conversion wrap", { offset := unsignedLimit, length := 1 }, none),
     ("Nat length conversion wrap", { offset := 0, length := unsignedLimit }, none),
     ("UInt64 maximum offset", { offset := unsignedLimit - 1, length := 1 }, none)]
  for (name, range, expected) in checkedCases do
    let actual ← readRange? file.toString range
    passed := passed + (← check s!"readRange? {name}" (actual == expected))
  passed := passed + (← check "readRange? missing file"
    (← readRange? missing.toString { offset := 0, length := 1 }).isNone)
  return passed

private def runAppend (directory : System.FilePath) : IO Nat := do
  let file := directory / "append.dlog"
  let created := directory / "new.dlog"
  IO.FS.writeBinFile file "abcd".toUTF8
  let mut passed := 0
  passed := passed + (← check "append refuses stale expected size"
    (!(← appendSyncAtSizeRaw file.toString 3 "X".toUTF8)))
  passed := passed + (← check "stale append preserves bytes"
    ((← IO.FS.readBinFile file) == "abcd".toUTF8))
  passed := passed + (← check "append accepts current expected size"
    (← appendSyncAtSizeRaw file.toString 4 "ef".toUTF8))
  passed := passed + (← check "successful append writes all bytes"
    ((← IO.FS.readBinFile file) == "abcdef".toUTF8))
  passed := passed + (← check "append refuses an old winner's size"
    (!(← appendSyncAtSizeRaw file.toString 4 "X".toUTF8)))
  passed := passed + (← check "rejected second append preserves bytes"
    ((← IO.FS.readBinFile file) == "abcdef".toUTF8))
  passed := passed + (← check "append creates absent file at size zero"
    (← appendSyncAtSizeRaw created.toString 0 "new".toUTF8))
  passed := passed + (← check "new append file contains complete bytes"
    ((← IO.FS.readBinFile created) == "new".toUTF8))
  return passed

private def runReplace (directory : System.FilePath) : IO Nat := do
  let file := directory / "CURRENT"
  let created := directory / "NEW"
  let missingParent := directory / "absent" / "CURRENT"
  IO.FS.writeBinFile file "old-generation\n".toUTF8
  let mut passed := 0
  passed := passed + (← check "replace accepts existing control file"
    (← atomicReplaceFileSyncRaw file.toString "new-generation\n".toUTF8))
  passed := passed + (← check "replace writes the complete control file"
    ((← IO.FS.readBinFile file) == "new-generation\n".toUTF8))
  passed := passed + (← check "replace accepts shorter contents"
    (← atomicReplaceFileSyncRaw file.toString "x".toUTF8))
  passed := passed + (← check "shorter replacement leaves no old suffix"
    ((← IO.FS.readBinFile file) == "x".toUTF8))
  passed := passed + (← check "replace accepts empty contents"
    (← atomicReplaceFileSyncRaw file.toString ByteArray.empty))
  passed := passed + (← check "empty replacement truncates completely"
    ((← IO.FS.readBinFile file) == ByteArray.empty))
  passed := passed + (← check "replace creates absent control file"
    (← atomicReplaceFileSyncRaw created.toString "created\n".toUTF8))
  passed := passed + (← check "new control file contains complete bytes"
    ((← IO.FS.readBinFile created) == "created\n".toUTF8))
  passed := passed + (← check "replace refuses missing parent"
    (!(← atomicReplaceFileSyncRaw missingParent.toString "no".toUTF8)))
  passed := passed + (← check "failed replace creates no destination"
    (!(← missingParent.pathExists)))
  passed := passed + (← check "replace leaves no temporary files"
    ((← directory.readDir).all fun entry =>
      !entry.fileName.startsWith "CURRENT.tmp." && !entry.fileName.startsWith "NEW.tmp."))
  return passed

def run : IO Nat :=
  IO.FS.withTempDir fun directory => do
    let reads ← runReads directory
    let append ← runAppend directory
    let replace ← runReplace directory
    return reads + append + replace

end NativeRangeSmoke

def main : IO UInt32 := do
  try
    let passed ← NativeRangeSmoke.run
    IO.println s!"native range: {passed} pass, 0 fail"
    return 0
  catch error =>
    IO.eprintln s!"native range failure: {error}"
    return 1
