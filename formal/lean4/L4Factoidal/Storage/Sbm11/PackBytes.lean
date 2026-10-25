/-
L4Factoidal.Storage.Sbm11.PackBytes — every file of one SBM11 generation,
packed in memory with no file system
(https://github.com/danbri/factoidal/issues/1009; stage 2 of
docs/designissues/2026-10-24-sbm11-in-npm.md).

`packFiles h qs decl sourceBytes sourceSha` packs the quads `qs` (a triple and
its graph name, `none` for the default graph) and the declared named graphs
`decl` into the list of `(file name, bytes)` that `l4sbm11-pack` writes into
its output directory for the same quads:

* `dict.gdv1`, `dict.gdx1`, `graphs.gnl1` (only when the generation has a
  named graph), and `pso`, `pos`, `spo`, `osp` with `.prm1` and `.prb1`;
* `<file>.merkle` for each of those files: the 65,536-byte Merkle leaves;
* `manifest.sbm11`, last.

It does not produce `CURRENT`. That file is the activation pointer of a
collection root, which `l4sbm11 activate` writes after it checks a generation;
it is not a file of the generation.

`packText h fmt base text` reads `text` through the source layer as one
`Dataset` (`Source.parseDocument`, RDF 1.2, the `--via-dataset` path of
`l4sbm11-pack`) and packs its quads and named graphs; the manifest records the
UTF-8 length and the SHA-256 of `text` as the source.

## Where the bytes come from

The same functions as the native packer (`Harness/Sbm11PackLib.lean`), in the
same order, over arrays in memory in place of run files:

* the dictionary keys: `termKeyBytes?` of each distinct term (language tags in
  lower case by `normalizeTerm`) that has no inline id (`inlineCode?`), sorted
  by `Qlvr.cmpBytes` without duplicates; the id of rank `r` is
  `classTagOfByte (key 0) * 2^60 + r` (phase 2 of the packer);
* GDV1 and GDX1: `PackStream.Pages.push` and `Pages.finish`, one key at a time
  (`Pages.gdv_eq`, `Pages.entries_eq`: the bytes of `Dict.encodeDict?`);
* per permutation: the rows `Overlay.toPermRow k` of the SPO rows, sorted by
  `Row.le` (`mergeSortBy`), without repeats, cut and encoded by
  `PackStream.Cut.push` and `Cut.finish` (`Cut.packPerm_eq`: the bytes of
  `PackSpec.packPerm?`), then `encodePrm?`;
* GNL1: the graph ids of the quads and of `decl` (not 0), sorted without
  repeats, by `GraphList.encode?`;
* the manifest: per file its length, `h.digest` (SHA-256), and the Merkle root
  `rootWith h` of the leaves `leafWith h` of its 65,536-byte chunks
  (`Harness.Sbm11Gen.hashFile`), by `Manifest.encodeManifest?`.

The hash is the parameter `h` (a `BlockMerkle.Hasher`), so this library module
names no extern: the `#guard`s use `pureHasher` (pure Lean SHA-256); the wasm
op and the native differential pass `Crypto.sha256Hacl`, as the native packer
does.

`Harness/Sbm11PackSpecCheck.lean` (`l4sbm11 packfiles-check`) compares every
file of `packText` with the files `l4sbm11-pack` wrote, byte for byte.

## Loops

Every walk over input-sized data is a tail call with a fuel `Nat` first, or
`Array.foldl`; the sort is `Qlvr.mergeSortBy` (tail calls). No `for` loop in
`Id.run` (the generic `forIn` over a range took one native frame per element,
`Qlvr/Sort.lean`).

The whole input and every file are in memory at once: this is the packer for
small and medium inputs (a browser, a test). Large inputs use `l4sbm11-pack`,
whose memory does not grow with the source.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import Std.Data.HashMap
import Std.Data.HashSet
import L4Factoidal.Storage.Sbm11.PackSpec
import L4Factoidal.Storage.Sbm11.PackStream
import L4Factoidal.Storage.Sbm11.GraphList
import L4Factoidal.Storage.Sbm11.Manifest
import L4Factoidal.Storage.BlockMerkle
import L4Factoidal.Storage.DeltaLog
import L4Factoidal.Qlvr.Sort
import L4Factoidal.RDF.SourceJsonLd
import L4Factoidal.RDF.DatasetNormalize

namespace L4Factoidal.Storage.Sbm11.PackBytes

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Block
open L4Factoidal.Storage.Sbm11.Manifest
open L4Factoidal.Storage.BlockMerkle (Hasher leafWith rootWith pureHasher)
open L4Factoidal.Qlvr (cmpBytes mergeSortBy)

/-- The file name of the manifest. -/
def manifestName : String := "manifest.sbm11"

/-- A quad: a triple and its graph name (`none`: the default graph). -/
abbrev Quad := Triple × Option Subject

/-- The packer's default block size in rows (`l4sbm11-pack --block-rows`). -/
def defaultBlockRows : Nat := 4096

/-- The Merkle chunk of every file (`Harness.Sbm11Gen.chunkBytes`). -/
def chunkBytes : Nat := 65536

/-- The bytes of a list. -/
def ofList (l : List UInt8) : ByteArray := ⟨l.toArray⟩

/-! ## The dictionary -/

/-- The terms of a quad. -/
def quadTerms (q : Quad) : List Term :=
  [q.1.s.toTerm, .iri q.1.p, q.1.o] ++ (match q.2 with | some g => [g.toTerm] | none => [])

/-- Add the normalised form of `t0` when it has no inline id. -/
def addTerm (acc : Std.HashSet Term) (t0 : Term) : Std.HashSet Term :=
  let t := normalizeTerm t0
  match inlineCode? t with
  | some _ => acc
  | none => acc.insert t

/-- The distinct dictionary terms of the quads and of the declared graphs. -/
def dictTerms (qs : Array Quad) (decl : Array Subject) : Std.HashSet Term :=
  let s := qs.foldl (fun acc q => (quadTerms q).foldl addTerm acc) {}
  decl.foldl (fun acc g => addTerm acc g.toTerm) s

/-- The terms and, per term, its key and its index in the terms; or the first
    term the dictionary does not admit. -/
def keyPairs (ts : Std.HashSet Term) : Except String (Array Term × Array (ByteArray × Nat)) :=
  ts.fold (fun acc t =>
    match acc with
    | .error e => .error e
    | .ok (terms, arr) =>
      match termKeyBytes? t with
      | some k => .ok (terms.push t, arr.push (k, terms.size))
      | none => .error s!"term not admitted by the SBM11 dictionary: {repr t}") (.ok (#[], #[]))

/-- The sorted keys without repeats, and the id of each term. -/
structure TermDict where
  keys : Array ByteArray
  ids : Std.HashMap Term Nat

/-- Walk the sorted pairs from `i`: a key equal to the one before keeps its
    rank (the packer's phase 2 drops it). A tail call. -/
def rankGo (terms : Array Term) (ps : Array (ByteArray × Nat)) : Nat → Nat → TermDict → TermDict
  | 0, _, d => d
  | f + 1, i, d =>
    if h : i < ps.size then
      let (k, j) := ps[i]
      let isDup : Bool := match d.keys.back? with
        | some p => cmpBytes p k == .eq
        | none => false
      let keys := if isDup then d.keys else d.keys.push k
      let rank := keys.size - 1
      let id := classTagOfByte (k.get! 0) * two60 + rank
      match terms[j]? with
      | some t => rankGo terms ps f (i + 1) { keys, ids := d.ids.insert t id }
      | none => rankGo terms ps f (i + 1) { d with keys }
    else d

/-- The dictionary of the quads and of the declared graphs. -/
def buildDict (qs : Array Quad) (decl : Array Subject) : Except String TermDict := do
  let (terms, ps) ← keyPairs (dictTerms qs decl)
  let sorted := mergeSortBy ps (fun a b => cmpBytes a.1 b.1 != .gt)
  pure (rankGo terms sorted sorted.size 0 { keys := Array.mkEmpty sorted.size, ids := {} })

/-- The id of a term: its inline id, else its dictionary id. -/
def TermDict.idOf (d : TermDict) (t0 : Term) : Except String Nat :=
  let t := normalizeTerm t0
  match inlineCode? t with
  | some c => .ok c
  | none =>
    match d.ids[t]? with
    | some x => .ok x
    | none => .error s!"term without a dictionary id: {repr t}"

/-! ## GDV1 and GDX1 -/

/-- The bytes written so far: GDV1, the GDX1 entries, the page count. -/
structure DictOut where
  gdv : ByteArray
  ent : ByteArray
  pages : Nat

def DictOut.emit (o : DictOut) : Option (List UInt8 × Dict.DirEntry) → DictOut
  | none => o
  | some (bytes, e) =>
    { gdv := o.gdv ++ ofList bytes, ent := o.ent ++ ofList (Dict.entryBytes e), pages := o.pages + 1 }

/-- `Pages.push` over the keys from `i`. A tail call. -/
def pagesGo (keys : Array ByteArray) : Nat → Nat → PackStream.Pages → DictOut → PackStream.Pages × DictOut
  | 0, _, st, o => (st, o)
  | f + 1, i, st, o =>
    if h : i < keys.size then
      let (st', e) := st.push keys[i].data.toList
      pagesGo keys f (i + 1) st' (o.emit e)
    else (st, o)

/-- GDV1 and GDX1 of the sorted keys (phase 2 of the packer). -/
def dictFiles (keys : Array ByteArray) : ByteArray × ByteArray :=
  let o0 : DictOut := { gdv := ofList Dict.gdvHeader, ent := ByteArray.empty, pages := 0 }
  let (st, o) := pagesGo keys keys.size 0 ⟨#[], Dict.gdvHeader.length⟩ o0
  let o := o.emit st.finish
  let hdr := Dict.gdxMagic ++ L4Factoidal.Storage.writeU64LE (UInt64.ofNat keys.size) ++
    L4Factoidal.Storage.writeU64LE (UInt64.ofNat o.pages)
  (o.gdv, ofList hdr ++ o.ent)

/-! ## Rows, PRB1 and PRM1 -/

/-- The SPO rows of the quads from `i`. A tail call. -/
def rowsGo (d : TermDict) (qs : Array Quad) : Nat → Nat → Array Row → Except String (Array Row)
  | 0, _, acc => .ok acc
  | f + 1, i, acc =>
    if h : i < qs.size then
      let q := qs[i]
      match d.idOf q.1.s.toTerm, d.idOf (.iri q.1.p), d.idOf q.1.o,
            (match q.2 with | none => (Except.ok 0 : Except String Nat) | some g => d.idOf g.toTerm) with
      | .ok s, .ok p, .ok o, .ok g => rowsGo d qs f (i + 1) (acc.push ⟨s, p, o, g⟩)
      | .error e, _, _, _ | _, .error e, _, _ | _, _, .error e, _ | _, _, _, .error e => .error e
    else .ok acc

/-- One permutation being written: the cut, the PRB1 bytes, the PRM1 entries,
    the rows written and the last row. -/
structure PermAcc where
  cut : PackStream.Cut
  prb : ByteArray
  metas : Array BlockMeta
  rows : Nat
  prev : Option Row

def PermAcc.emit (a : PermAcc) : Option (BlockMeta × ByteArray) → PermAcc
  | none => a
  | some (m, bytes) => { a with prb := a.prb ++ bytes, metas := a.metas.push m }

/-- `Cut.push` over the sorted rows from `i`, without repeats (phase 3b of
    the packer). A tail call. -/
def permGo (B : Nat) (rows : Array Row) : Nat → Nat → PermAcc → PermAcc
  | 0, _, a => a
  | f + 1, i, a =>
    if h : i < rows.size then
      let x := rows[i]
      if a.prev == some x then permGo B rows f (i + 1) a
      else
        let (cut, out) := a.cut.push B x
        permGo B rows f (i + 1) ({ a with cut, rows := a.rows + 1, prev := some x }.emit out)
    else a

/-- PRM1 and PRB1 of permutation `k`, and its row count. -/
def permFiles (B k : Nat) (spo : Array Row) : Except String (ByteArray × ByteArray × Nat) :=
  let rows := mergeSortBy (spo.map (Overlay.toPermRow k)) Row.le
  let a0 : PermAcc := { cut := ⟨prbHeaderBytes, #[]⟩, prb := ofList (prbHeader k), metas := #[], rows := 0,
                        prev := none }
  let a := permGo B rows rows.size 0 a0
  let a := a.emit a.cut.finish
  match encodePrm? k a.metas.toList with
  | some prm => .ok (ofList prm, a.prb, a.rows)
  | none => .error s!"{permNames[k]!}: the PRM1 encoder refuses the block list"

/-! ## GNL1 -/

/-- The named graph ids: the graph ids of the rows and the declared graphs. -/
def graphIds (d : TermDict) (spo : Array Row) (decl : Array Subject) : Except String (List Nat) := do
  let fromRows := spo.foldl (fun acc r => if r.g != 0 then acc.push r.g else acc) #[]
  let all ← decl.foldl (fun acc g => do
      let a ← acc
      let x ← d.idOf g.toTerm
      pure (if x != 0 then a.push x else a)) (Except.ok fromRows)
  let sorted := mergeSortBy all (· ≤ ·)
  let uniq := sorted.foldl (fun acc x => if acc.back? == some x then acc else acc.push x) #[]
  pure uniq.toList

/-! ## Hashing and the manifest -/

/-- The Merkle leaves of `b` from byte `i`. A tail call. -/
def leavesGo (h : Hasher) (b : ByteArray) : Nat → Nat → Array ByteArray → Array ByteArray
  | 0, _, acc => acc
  | f + 1, i, acc =>
    if i < b.size then
      leavesGo h b f (i + chunkBytes) (acc.push (leafWith h (b.extract i (min b.size (i + chunkBytes)))))
    else acc

/-- The leaves of a file's 65,536-byte chunks (none for an empty file). -/
def leaves (h : Hasher) (b : ByteArray) : Array ByteArray :=
  leavesGo h b (b.size / chunkBytes + 1) 0 #[]

/-- The manifest entry of a file, and its `.merkle` sidecar. -/
def artifactOf (h : Hasher) (role : String) (b : ByteArray) : Artifact × ByteArray :=
  let ls := leaves h b
  let ref : ChunkedArtifact.Ref :=
    { totalBytes := b.size, chunkBytes, chunkCount := ls.size, root := rootWith h ls.toList }
  ({ role, file := fileOfRole role, bytes := b.size, sha256 := h.digest b, merkle := ref },
   ls.foldl (· ++ ·) (ByteArray.emptyWithCapacity (32 * ls.size)))

/-! ## The pack -/

/-- A generation in memory: its files in the order the manifest names them,
    each followed by its `.merkle` sidecar, then `manifest.sbm11`; and the
    counts the packer prints. -/
structure Packed where
  files : Array (String × ByteArray)
  quads : Nat
  terms : Nat
  graphs : Nat

/-- Every file of the generation of `qs` and `decl` (see the module comment).
    `sourceBytes` and `sourceSha` are what the manifest records as the source. -/
def packFiles (h : Hasher) (qs : Array Quad) (decl : Array Subject) (sourceBytes : Nat)
    (sourceSha : ByteArray) (blockRows : Nat := defaultBlockRows) : Except String Packed := do
  let d ← buildDict qs decl
  let (gdv, gdx) := dictFiles d.keys
  let spo ← rowsGo d qs qs.size 0 (Array.mkEmpty qs.size)
  let (prm0, prb0, n0) ← permFiles blockRows 0 spo
  let (prm1, prb1, _) ← permFiles blockRows 1 spo
  let (prm2, prb2, _) ← permFiles blockRows 2 spo
  let (prm3, prb3, _) ← permFiles blockRows 3 spo
  let gids ← graphIds d spo decl
  let gnl ← match gids with
    | [] => pure none
    | xs => match GraphList.encode? xs with
      | some bs => pure (some (ofList bs))
      | none => throw "the graph list encoder refuses the named graph ids"
  let bytesOf (role : String) : ByteArray :=
    match role with
    | "GDV1" => gdv | "GDX1" => gdx | "GNL1" => gnl.getD ByteArray.empty
    | "PRM1-PSO" => prm0 | "PRB1-PSO" => prb0 | "PRM1-POS" => prm1 | "PRB1-POS" => prb1
    | "PRM1-SPO" => prm2 | "PRB1-SPO" => prb2 | "PRM1-OSP" => prm3 | "PRB1-OSP" => prb3
    | _ => ByteArray.empty
  let rs := if gnl.isSome then rolesWithGraphs else roles
  let (arts, files) := rs.foldl (fun (arts, files) role =>
      let b := bytesOf role
      let (a, side) := artifactOf h role b
      (arts.push a, (files.push (a.file, b)).push (a.file ++ ".merkle", side)))
    ((#[] : Array Artifact), (#[] : Array (String × ByteArray)))
  let m : Manifest := { layout := sbm11Layout, sourceBytes, sourceSha256 := sourceSha, quads := n0,
                        terms := d.keys.size, artifacts := arts.toList }
  match encodeManifest? m with
  | some bytes =>
    pure { files := files.push (manifestName, ofList bytes), quads := n0, terms := d.keys.size,
           graphs := gids.length }
  | none => throw "the SBM11 manifest encoder refuses the manifest"

/-- The generation of an RDF dataset: its quads (`Dataset.quadList`) and its
    named graphs, empty ones included. -/
def packDataset (h : Hasher) (ds : Dataset) (sourceBytes : Nat) (sourceSha : ByteArray)
    (blockRows : Nat := defaultBlockRows) : Except String Packed :=
  packFiles h ds.quadList.toArray (ds.named.map (·.name)).toArray sourceBytes sourceSha blockRows

/-- The generation of a document: `text` read through the source layer in
    syntax `fmt` (RDF 1.2), with the length and SHA-256 of its UTF-8 bytes as
    the source. -/
def packText (h : Hasher) (fmt : RdfFormat) (base : Option String) (text : String)
    (blockRows : Nat := defaultBlockRows) : Except String Packed :=
  match Source.parseDocument Source.withJsonLd fmt .rdf12 base text with
  | .error e => .error s!"parse error at {e.pos}: {e.msg}"
  | .ok ds =>
    let bytes := text.toUTF8
    packDataset h ds bytes.size (h.digest bytes) blockRows

/-! ## Tests -/

private def exI (s : String) (h : isIri s := by rfl) : WfIri := ⟨s, h⟩
private def q1 : Quad := (⟨.iri (exI "http://ex.org/a"), exI "http://ex.org/p", .literal (Literal.langString "x" "EN")⟩, none)
private def q2 : Quad := (⟨.iri (exI "http://ex.org/b"), exI "http://ex.org/p", .iri (exI "http://ex.org/a")⟩,
  some (.iri (exI "http://ex.org/g")))

private def tiny : Except String Packed :=
  packFiles pureHasher #[q1, q2, q1] #[] 0 (pureHasher.digest ByteArray.empty)

private def fileOf (p : Packed) (name : String) : ByteArray :=
  (p.files.find? (·.1 == name)).map (·.2) |>.getD ByteArray.empty

-- 11 files with the graph list, 11 sidecars, the manifest
#guard match tiny with
  | .ok p => p.files.size == 23 && p.quads == 2 && p.terms == 5 && p.graphs == 1
  | .error _ => false
-- the manifest decodes, names 11 files and records their lengths
#guard match tiny with
  | .ok p =>
    match decodeManifest (fileOf p manifestName).data.toList with
    | some m => m.artifacts.length == 11 && m.quads == 2 && m.terms == 5 &&
        m.artifacts.all (fun a => a.bytes == (fileOf p a.file).size)
    | none => false
  | .error _ => false
-- GDV1, GDX1 and each PRM1 and PRB1 are the bytes of the specification `packSpec`
#guard match tiny, PackSpec.packSpec defaultBlockRows [q1, q2, q1] [] with
  | .ok p, some (_, F) =>
    fileOf p "dict.gdv1" == F.gdv && fileOf p "dict.gdx1" == F.gdx &&
    (List.range 4).all (fun k =>
      fileOf p s!"{permNames[k]!}.prm1" == F.prm k && fileOf p s!"{permNames[k]!}.prb1" == F.prb k)
  | _, _ => false
-- a generation with no named graph has no graph list: 10 files, 10 sidecars, the manifest
#guard match packFiles pureHasher #[q1] #[] 0 (pureHasher.digest ByteArray.empty) with
  | .ok p => p.files.size == 21 && p.graphs == 0
  | .error _ => false
-- a declared empty named graph is in the graph list
#guard match packFiles pureHasher #[q1] #[.iri (exI "http://ex.org/g")] 0 (pureHasher.digest ByteArray.empty) with
  | .ok p => p.files.size == 23 && p.graphs == 1
  | .error _ => false
-- a document: two N-Quads lines, one repeated
#guard match packText pureHasher .nquads none
    "<http://ex.org/a> <http://ex.org/p> \"x\"@EN .\n<http://ex.org/a> <http://ex.org/p> \"x\"@en .\n" with
  | .ok p => p.quads == 1 && p.files.size == 21
  | .error _ => false
#guard match packText pureHasher .nquads none "<http://ex.org/a> <http://ex.org/p> ." with
  | .ok _ => false
  | .error _ => true

end L4Factoidal.Storage.Sbm11.PackBytes
