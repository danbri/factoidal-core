/-
Harness/Sbm11PackSpecCheck — `l4sbm11 packspec-check`: the bytes that the
pure packer specification `PackSpec.packSpec` gives against the files that
`l4sbm11-pack` wrote (https://github.com/danbri/factoidal/issues/776; row
L3c of docs/designissues/2026-10-12-sbm11-end-to-end-theorem.md).

  l4sbm11 packspec-check SOURCE GEN [--block-rows B] [--base IRI]

The command reads SOURCE through the source layer as one `Dataset`
(`Sbm11Pack.openDatasetSource`), takes its quads and declared named graphs,
computes `packSpec B` of them (B default 4096, the packer's default), and
compares byte for byte: GDV1, GDX1, and per permutation PRM1 and PRB1 with
the files of the generation GEN; and the named graph ids with those of the
session. It also runs `MemGen.check` on the generation `packSpec` gives.

The last line is `packspec-check: N files, E identical, D differ; named
graphs equal|differ; check = true|false`. Exit 0 only when every file is
identical, the named graphs are equal and `check` is true.

This is a test of the packer against its specification, not a proof: the
packer is an `IO` program over run files. With identical bytes,
`FileGenTheorems.Written` holds for the generation `packSpec` gives and the
files of GEN.

  l4sbm11 packfiles-check SOURCE GEN [--block-rows B] [--base IRI]

The in-memory packer `PackBytes.packText` (the packer of the wasm op
`sbm11PackFiles`, https://github.com/danbri/factoidal/issues/1009 stage 2)
against the files `l4sbm11-pack` wrote: SOURCE is read as one document in the
syntax its extension names, packed with the HACL* hasher, and every file it
gives (the eleven or ten data files, their `.merkle` sidecars and
`manifest.sbm11`) is compared byte for byte with the file of the same name in
GEN (a generation directory, or a collection root whose `CURRENT` names one).
A file of GEN that `packText` does not give is also reported. The last line is
`packfiles-check: N files, E identical, D differ, M only in GEN`. Exit 0 only
when every file is identical and no file is only in GEN.

This is a HARNESS: it does file I/O.
-/
import Harness.Sbm11Query
import Harness.Sbm11PackLib
import L4Factoidal.Storage.Sbm11.PackSpec
import L4Factoidal.Storage.Sbm11.PackBytes
import Harness.NativeHasher
import Harness.GenerationPointer

namespace Harness.Sbm11PackSpecCheck

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.MemGen
open Harness.Sbm11Query

def run (source dir : String) (blockRows : Nat) (base : Option String) : IO UInt32 := do
  let fmt ← match Sbm11Pack.chooseFormat source none with
    | .ok f => pure f
    | .error m => throw (IO.userError m)
  let src ← Sbm11Pack.openDatasetSource source fmt base
  let (qs, gs) ← src.foldBatches ((#[] : Array PackSpec.Quad), (#[] : Array Subject)) fun (qs, gs) b =>
    pure (qs ++ b.quads, gs ++ b.graphs)
  let some (G, F) := PackSpec.packSpec blockRows qs.toList gs.toList
    | IO.println "packspec-check: packSpec refuses the input"; return 1
  let ss ← openSession .none dir
  let mut n := 0
  let mut same := 0
  let check (what : String) (want got : ByteArray) : IO Bool := do
    if want == got then
      IO.println s!"identical {what} ({got.size} bytes)"; return true
    else
      IO.println s!"DIFFER    {what}: packSpec {want.size} bytes, file {got.size} bytes"; return false
  n := n + 1
  if ← check "GDV1" F.gdv (← IO.FS.readBinFile ss.g.gdvPath) then same := same + 1
  n := n + 1
  if ← check "GDX1" F.gdx (← IO.FS.readBinFile ss.g.gdxPath) then same := same + 1
  for p in [0:4] do
    let lp ← ss.perm p
    n := n + 1
    if ← check s!"PRM1 {p}" (F.prm p) (← IO.FS.readBinFile lp.prmPath) then same := same + 1
    n := n + 1
    if ← check s!"PRB1 {p}" (F.prb p) (← IO.FS.readBinFile lp.prbPath) then same := same + 1
  let named := (← ss.baseNamed).map (·.toUInt64)
  let namedOk := named == F.named
  let ok := G.check
  IO.println s!"packspec-check: {n} files, {same} identical, {n - same} differ; named graphs {if namedOk then "equal" else "differ"}; check = {ok}"
  return (if same == n && namedOk && ok then 0 else 1)

def runFiles (source dir0 : String) (blockRows : Nat) (base : Option String) : IO UInt32 := do
  let fmt ← match Sbm11Pack.chooseFormat source none with
    | .ok f => pure f
    | .error m => throw (IO.userError m)
  let some text := String.fromUTF8? (← IO.FS.readBinFile source)
    | IO.println s!"packfiles-check: {source}: UTF-8 error"; return 1
  let p ← match PackBytes.packText Harness.nativeHasher fmt base text blockRows with
    | .ok p => pure p
    | .error e => IO.println s!"packfiles-check: packText refuses the input: {e}"; return 1
  let dir := (← Harness.GenerationPointer.resolveStoreDirectory dir0).toString
  let mut same := 0
  for (name, want) in p.files do
    let path : System.FilePath := s!"{dir}/{name}"
    if !(← path.pathExists) then
      IO.println s!"DIFFER    {name}: packText {want.size} bytes, no file"
    else
      let got ← IO.FS.readBinFile path
      if want == got then
        IO.println s!"identical {name} ({got.size} bytes)"; same := same + 1
      else
        IO.println s!"DIFFER    {name}: packText {want.size} bytes, file {got.size} bytes"
  let mut onlyGen := 0
  for e in ← System.FilePath.readDir dir do
    if !(p.files.any (·.1 == e.fileName)) then
      IO.println s!"ONLY GEN  {e.fileName}"; onlyGen := onlyGen + 1
  let n := p.files.size
  IO.println s!"packfiles-check: {n} files, {same} identical, {n - same} differ, {onlyGen} only in GEN (quads {p.quads}, terms {p.terms}, named graphs {p.graphs})"
  return (if same == n && onlyGen == 0 then 0 else 1)

def main (args : List String) : IO UInt32 := do
  let rec opts : List String → Nat → Option String → Option (Nat × Option String)
    | [], b, base => some (b, base)
    | "--block-rows" :: v :: rest, _, base => v.toNat?.bind fun b => opts rest b base
    | "--base" :: v :: rest, b, _ => opts rest b (some v)
    | _, _, _ => none
  match args with
  | "packspec-check" :: source :: dir :: rest =>
    match opts rest 4096 none with
    | some (b, base) =>
      try run source dir b base
      catch e => IO.eprintln s!"l4sbm11 packspec-check: {e}"; return 1
    | none =>
      IO.eprintln "usage: l4sbm11 packspec-check SOURCE GEN [--block-rows B] [--base IRI]"
      return 2
  | "packfiles-check" :: source :: dir :: rest =>
    match opts rest 4096 none with
    | some (b, base) =>
      try runFiles source dir b base
      catch e => IO.eprintln s!"l4sbm11 packfiles-check: {e}"; return 1
    | none =>
      IO.eprintln "usage: l4sbm11 packfiles-check SOURCE GEN [--block-rows B] [--base IRI]"
      return 2
  | _ =>
    IO.eprintln "usage: l4sbm11 packspec-check|packfiles-check SOURCE GEN [--block-rows B] [--base IRI]"
    return 2

end Harness.Sbm11PackSpecCheck
