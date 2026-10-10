/-
L4Factoidal.RML.Compression — the compression formats an RML source or
target names with `rml:compression`.

Spec: RML-IO (https://w3id.org/rml/io/spec), "Compression formats":
`rml:none`, `rml:gzip`, `rml:zip`, `rml:targz`, `rml:tarxz`.

A codec is a total function of bytes (`L4Factoidal.Codec`). `decompress`
turns the bytes of a source file into the bytes of the document inside;
a format this module has no codec for is `unsupported`, and a file that
is not what its format says is `corrupt`. The two are different
answers: the first is a gap in the port, the second a bad file.
-/
import L4Factoidal.RML.Error
import L4Factoidal.Codec.Archive
import L4Factoidal.Codec.Xz

namespace L4Factoidal.RML

open L4Factoidal.Codec

inductive Compression where
  | none | gzip | zip | targz | tarxz
deriving Repr, DecidableEq, Inhabited

def Compression.ofIri? (iri : String) : Option Compression :=
  let n := "http://w3id.org/rml/"
  if iri.isEmpty || iri == n ++ "none" then some .none
  else if iri == n ++ "gzip" then some .gzip
  else if iri == n ++ "zip" then some .zip
  else if iri == n ++ "targz" then some .targz
  else if iri == n ++ "tarxz" then some .tarxz
  else Option.none

def Compression.label : Compression → String
  | .none => "none" | .gzip => "gzip" | .zip => "zip"
  | .targz => "tar.gz" | .tarxz => "tar.xz"

inductive CodecError where
  | unsupported (what : String)
  | corrupt (msg : String)

def CodecError.message : CodecError → String
  | .unsupported w => s!"no {w} codec"
  | .corrupt m => m

/-- Undo a compression: the one document inside. -/
def decompress (c : Compression) (b : ByteArray) : Except CodecError ByteArray :=
  let corrupt {α : Type} (r : Except String α) : Except CodecError α :=
    match r with
    | .ok a => .ok a
    | .error m => .error (.corrupt m)
  match c with
  | .none => .ok b
  | .gzip => corrupt (gunzip b)
  | .zip => corrupt ((unzipFirst b).map (·.2))
  | .targz => corrupt (do (untarFirst (← gunzip b)).map (·.2))
  | .tarxz =>
      match unxz b with
      | .error (.unsupported w) => .error (.unsupported w)
      | .error (.corrupt m) => .error (.corrupt m)
      | .ok tarBytes => corrupt ((untarFirst tarBytes).map (·.2))

/-- Apply a compression to a document. `entry` names the file inside an
    archive (zip, tar). -/
def compress (c : Compression) (entry : String) (b : ByteArray) : Except CodecError ByteArray :=
  match c with
  | .none => .ok b
  | .gzip => .ok (gzip b)
  | .zip => .ok (zipSingle entry b)
  | .targz => .ok (gzip (tarSingle entry b))
  | .tarxz => .ok (xz (tarSingle entry b))

/-! ## Build-time checks -/

private def doc : ByteArray := "x,y\n1,2\n".toUTF8

-- Every codec round-trips; the archive formats keep the entry name.
#guard (decompress .none doc).toOption == some doc
#guard match compress .gzip "a.csv" doc with
       | .ok c => (decompress .gzip c).toOption == some doc && c != doc | .error _ => false
#guard match compress .zip "a.csv" doc with
       | .ok c => (decompress .zip c).toOption == some doc && c != doc | .error _ => false
#guard match compress .targz "a.csv" doc with
       | .ok c => (decompress .targz c).toOption == some doc && c != doc | .error _ => false
-- A file of the wrong format is corrupt, not empty.
#guard match decompress .gzip doc with | .error (.corrupt _) => true | _ => false
#guard match decompress .zip doc with | .error (.corrupt _) => true | _ => false
#guard match decompress .targz doc with | .error (.corrupt _) => true | _ => false
#guard match compress .tarxz "a.csv" doc with
       | .ok c => (decompress .tarxz c).toOption == some doc && c != doc | .error _ => false
-- ...and an xz file without a tar archive in it, or a tar archive that is not
-- xz-compressed, is corrupt.
#guard match decompress .tarxz doc with | .error (.corrupt _) => true | _ => false
#guard match decompress .tarxz (xz doc) with | .error (.corrupt _) => true | _ => false
#guard match decompress .tarxz (tarSingle "a" doc) with | .error (.corrupt _) => true | _ => false
-- The IRIs.
#guard Compression.ofIri? "" == some .none
#guard Compression.ofIri? "http://w3id.org/rml/targz" == some .targz
#guard Compression.ofIri? "http://w3id.org/rml/bzip2" == none

end L4Factoidal.RML
