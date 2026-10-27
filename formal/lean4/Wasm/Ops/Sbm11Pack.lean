/-
Wasm.Ops.Sbm11Pack — packing an SBM11 generation inside the module
(https://github.com/danbri/factoidal/issues/1009; stage 2 of
docs/designissues/2026-10-24-sbm11-in-npm.md).

  sbm11PackFiles(syntax, base, index)      -- the document is the IN region
    -> {"ok":true,"index":I,"count":N,"name":"dict.gdv1","bytes":B,
        "quads":Q,"terms":T,"graphs":G}
       and the bytes of file I as the OUT region

`syntax` is a label of `RDF.formatOfLabel` (turtle, trig, nquads, ntriples,
rdfxml, jsonld); `base` is the base IRI of the document, `""` for none;
`index` is a decimal number below `count`. The files are those of
`L4Factoidal.Storage.Sbm11.PackBytes.packText`, in its order: the data files
in manifest order, each followed by its `.merkle` sidecar, then
`manifest.sbm11`. The host writes each file under `name` in one generation
directory (or keeps them in memory, `mapReader` in npm); it does not choose a
name, a length or a digest (iron rule 7).

A host asks for index 0, 1, ... with the same document each time. The module
keeps the files of the last document it packed (one memo entry: the syntax,
the base, the document bytes and the files), so the document is packed once,
not once per file. A call with another document, syntax or base packs again.
The answer for the last index (`count - 1`) clears the memo, so the files do
not stay in the module's heap after a host has read them all; a later call
packs again and gives the same bytes.

The hash is HACL* SHA-256 (`L4Factoidal.Crypto.sha256Hacl`), the hash of the
native packer, so the files are byte for byte those of `l4sbm11-pack
--via-dataset` (`l4sbm11 packfiles-check`).

Cap: `maxSbm11PackBytes`, the IN region. The whole document, its parse and
every file are in memory at once; this is the packer for small and medium
inputs on the module's 32-bit address space.
-/
import Wasm.Ops.Support
import L4Factoidal.Storage.Sbm11.PackBytes
import L4Factoidal.Crypto.SHA2Native

namespace L4Wasm.Ops

open L4Factoidal.JSON
open L4Factoidal.Storage.Sbm11.PackBytes (Packed packText)

/-- The largest document `sbm11PackFiles` reads: 67,108,864 bytes. -/
def maxSbm11PackBytes : Nat := 67108864

/-- The last pack: its input and its files. -/
structure Sbm11PackMemo where
  rdfSyntax : String
  base : String
  text : ByteArray
  packed : Packed

initialize sbm11PackMemo : IO.Ref (Option Sbm11PackMemo) ← IO.mkRef none

/-- The HACL* hasher of the native packer. -/
def sbm11PackHasher : L4Factoidal.Storage.BlockMerkle.Hasher := ⟨L4Factoidal.Crypto.sha256Hacl⟩

/-- The files of the document, from the memo when it holds the same input. -/
def sbm11Packed (rdfSyntax base : String) (text : ByteArray) : IO (Except String Packed) := do
  match ← sbm11PackMemo.get with
  | some m =>
    if m.rdfSyntax == rdfSyntax && m.base == base && m.text == text then return .ok m.packed
  | none => pure ()
  let some fmt := L4Factoidal.RDF.formatOfLabel rdfSyntax
    | return .error s!"sbm11PackFiles: unknown syntax {rdfSyntax} (turtle, trig, nquads, ntriples, rdfxml or jsonld)"
  let some doc := String.fromUTF8? text
    | return .error "sbm11PackFiles: the document is not UTF-8"
  match packText sbm11PackHasher fmt (if base.isEmpty then none else some base) doc with
  | .error e => return .error s!"sbm11PackFiles: {e}"
  | .ok p =>
    sbm11PackMemo.set (some { rdfSyntax, base, text, packed := p })
    return .ok p

/-- `sbm11PackFiles(rdfSyntax, base, index)`. -/
def sbm11PackFiles (rdfSyntax base index : String) (text : ByteArray) : IO (String × ByteArray) := do
  if text.size > maxSbm11PackBytes then
    return (errJson s!"sbm11PackFiles: the document has {text.size} bytes (at most {maxSbm11PackBytes})",
            ByteArray.empty)
  let some i := index.toNat?
    | return (errJson s!"sbm11PackFiles: index {index} is not a decimal number", ByteArray.empty)
  match ← sbm11Packed rdfSyntax base text with
  | .error e => return (errJson e, ByteArray.empty)
  | .ok p =>
    match p.files[i]? with
    | none =>
      return (errJson s!"sbm11PackFiles: index {i} is not below the file count {p.files.size}", ByteArray.empty)
    | some (name, bytes) =>
      if i + 1 == p.files.size then sbm11PackMemo.set none
      return (okWith [("index", .number (toString i)), ("count", .number (toString p.files.size)),
                      ("name", .string name), ("bytes", .number (toString bytes.size)),
                      ("quads", .number (toString p.quads)), ("terms", .number (toString p.terms)),
                      ("graphs", .number (toString p.graphs))],
              bytes)

/-- The op of this module (`blobIoOpNames`). -/
def sbm11PackOpNames : List String := ["sbm11PackFiles"]

end L4Wasm.Ops
