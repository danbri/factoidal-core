/-
Harness/Sbm11Export — `l4sbm11 export`: write the dataset a SBM11 generation
stores in any of the six RDF syntaxes (https://github.com/danbri/factoidal/issues/837
item 6; record `docs/designissues/2026-10-11-shardborough-vs-qlever.md` section
11.2).

  l4sbm11 export GEN --format F [--out FILE] [--graph default|all|IRI]
                 [--prefix LABEL=IRI]... [--verify merkle|none]

F is ntriples, nquads, turtle, trig, rdfxml or jsonld (`RDF.formatOfLabel`).
Without `--out` the document goes to standard output. With `--out`, the document
is written to `FILE.tmp-PID` and renamed to FILE when it is complete, so a failed
export leaves no partial FILE.

The export reads the SPO permutation block by block, in key order, and gives each
quad to the serialiser layer (`L4Factoidal/RDF/Sink.lean`, `Sink.Writer`). This
file names no syntax: the format is an `RdfFormat` and the writer decides the
text. The store does not know the syntax of the document it was packed from, and
the export does not choose a syntax for it.

Memory. The export holds one block of the SPO permutation, a window of
`pageLimit` dictionary pages, the verified chunks of the blocks and pages it is
reading (dropped as it goes), and a 64 KiB output buffer, so it does not grow with
the generation (rows `sbm11-export-*-memory` of `tests/stack/lean_scaling.py`).
N-Quads and N-Triples write one line for each quad. Turtle writes the
triples of a subject as one statement and TriG does the same inside a block that
it closes when the graph of the next quad changes (a graph that the SPO order
interleaves with others gets several blocks; TriG accepts that). Both keep one
statement, not the dataset. RDF/XML and JSON-LD keep the quads and write at the
end (https://github.com/danbri/factoidal/issues/846 and
https://github.com/danbri/factoidal/issues/847).

Graphs. N-Triples, Turtle and RDF/XML have no graph name. When the generation
holds a quad in a named graph, the export is refused before any output, unless
`--graph` chooses: `default` (the default graph only), `all` (the union of all
graphs; a triple that is in several graphs is written once) or an IRI (the triples
of that graph). N-Quads, TriG and JSON-LD write every graph and refuse `--graph`.

Prefixes. Turtle and TriG write every IRI in full unless `--prefix LABEL=IRI`
gives a namespace (the label without its colon), which is declared at the start and
used for the IRIs it covers whose local part the parser accepts.

Exit 1 on any error. A summary and VmHWM go to standard error.
-/
import Harness.Sbm11Gen
import L4Factoidal.RDF.SinkJsonLd

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.Block
open Harness.Sbm11Gen

namespace Sbm11Export

structure Opts where
  format : Option String := none
  out : Option String := none
  graph : Option String := none
  prefixes : List (String × String) := []

def parseOpts : List String → Opts → Option Opts
  | [], o => some o
  | "--format" :: v :: rest, o => parseOpts rest { o with format := some v }
  | "--out" :: v :: rest, o => parseOpts rest { o with out := some v }
  | "--graph" :: v :: rest, o => parseOpts rest { o with graph := some v }
  | "--prefix" :: v :: rest, o =>
      match v.splitOn "=" with
      | label :: iriParts =>
          if label.isEmpty || iriParts.isEmpty then none
          else parseOpts rest { o with prefixes := o.prefixes ++ [(label, "=".intercalate iriParts)] }
      | [] => none
  | _, _ => none

def usage : String :=
  "usage: l4sbm11 export GEN --format F [--out FILE] [--graph default|all|IRI] [--prefix LABEL=IRI]... [--verify merkle|none]\n" ++
  "  F is ntriples, nquads, turtle, trig, rdfxml or jsonld. Without --out the document goes to standard output.\n" ++
  "  --graph chooses the quads of a syntax with no graph name (ntriples, turtle, rdfxml) when the generation has named graphs."

/-- A writer's error as it is: the command line prefixes it with `l4sbm11:`. -/
def okw {α : Type} : Except String α → IO α
  | .ok a => pure a
  | .error e => throw (IO.userError e)

def term2subject (what : String) (t : Term) : IO Subject :=
  match t.toSubject? with
  | some s => pure s
  | none => throw (IO.userError s!"the store holds a {what} that is not an IRI or a blank node")

/-- The first graph id other than the default graph in the SPO permutation, if
    any. A scan of the `g` column only; no term is decoded. -/
def firstNamedGraphId (g : Gen) : IO (Option Nat) := do
  let src ← permSrc g 2
  for i in [0:src.metas.size] do
    let c ← readBlock g src i
    for j in [0:c.size] do
      if c.g[j]! != 0 then return some c.g[j]!
  pure none

/-- Which graph ids the export keeps, decided on the id before any term is
    decoded. -/
inductive Keep where
  | everything
  | defaultOnly
  | graph (id : Nat)

def Keep.keeps : Keep → Nat → Bool
  | .everything, _ => true
  | .defaultOnly, gid => gid == 0
  | .graph id, gid => gid == id

/-- The dictionary pages the export keeps (64 terms each). The SPO order visits
    the subjects in dictionary order and the objects in any order, so the cache
    is a window, not the dictionary. -/
def pageLimit : Nat := 256

def runExport (dir : String) (v : Verify) (o : Opts) : IO UInt32 := do
  let t0 ← IO.monoNanosNow
  let some label := o.format
    | IO.eprintln usage; return 2
  let some fmt := formatOfLabel label
    | IO.eprintln s!"l4sbm11 export: unknown format '{label}'; give --format with one of ntriples, nquads, turtle, trig, rdfxml, jsonld"; return 2
  let g ← openGen v dir
  let namedOk := Source.hasNamedGraphs fmt
  if namedOk && o.graph.isSome then
    IO.eprintln s!"l4sbm11 export: {formatName fmt} has graph names and writes every graph; --graph applies to ntriples, turtle and rdfxml"
    return 2
  -- the quads a syntax with no graph name writes
  let (choice, keep) ← match o.graph with
    | none => pure (Sink.GraphChoice.refuse, Keep.everything)
    | some "default" => pure (Sink.GraphChoice.defaultOnly, Keep.defaultOnly)
    | some "all" => pure (Sink.GraphChoice.union, Keep.everything)
    | some iri =>
        if h : isIri iri = true then
          match ← idOfTerm g (.iri ⟨iri, h⟩) with
          | some gid => pure (Sink.GraphChoice.named (.iri ⟨iri, h⟩), Keep.graph gid)
          | none => throw (IO.userError s!"the graph <{iri}> is not in the store")
        else throw (IO.userError s!"--graph takes default, all or an IRI: {iri}")
  if !namedOk && o.graph.isNone then
    -- refuse before any output, not after the first named quad
    if let some gid := ← firstNamedGraphId g then
      let cache ← IO.mkRef ({} : Std.HashMap Nat (Array ByteArray))
      let name ← ok "export" (L4Factoidal.Syntax.Term.toNTriples .rdf12 (← termOfId g cache gid))
      throw (IO.userError s!"the generation has quads in named graphs (the first graph is {name}), and {formatName fmt} has no graph name; choose with --graph default, --graph all or --graph IRI")
  let table : L4Factoidal.Syntax.PrefixTable := o.prefixes.map fun (l, iri) => (iri, l ++ ":")
  let (w0, header) ← okw (Sink.Writer.init Sink.withJsonLd fmt { version := .rdf12, graphs := choice, prefixes := table })
  -- the output: standard output, or a temporary file renamed at the end
  let pid ← IO.Process.getPID
  let tmp := o.out.map fun p => s!"{p}.tmp-{pid}"
  let (put, flushOut) : (String → IO Unit) × IO Unit ← match tmp with
    | some p => do
        let h ← IO.FS.Handle.mk p .write
        pure (fun text => h.putStr text, h.flush)
    | none => do
        let h ← IO.getStdout
        pure (fun text => h.putStr text, h.flush)
  let finishOk : Option (Nat × Nat) ←
    try
      let src ← permSrc g 2
      let cache ← IO.mkRef ({} : Std.HashMap Nat (Array ByteArray))
      let mut w := w0
      let mut buf := header
      let mut quads := 0
      let mut bytes := 0
      for i in [0:src.metas.size] do
        let c ← readBlock g src i
        for j in [0:c.size] do
          let gid := c.g[j]!
          if !keep.keeps gid then continue
          let st ← termOfIdLimit g cache pageLimit true c.c0[j]!
          let pt ← termOfIdLimit g cache pageLimit true c.c1[j]!
          let ot ← termOfIdLimit g cache pageLimit true c.c2[j]!
          let s ← term2subject "subject" st
          let p ← match pt with
            | .iri i => pure i
            | _ => throw (IO.userError "the store holds a predicate that is not an IRI")
          let graphName ← if gid == 0 then pure none else some <$> (do term2subject "graph name" (← termOfIdLimit g cache pageLimit true gid))
          let (w', text) ← okw (w.push { s, p, o := ot } graphName)
          w := w'
          buf := buf ++ text
          quads := quads + 1
          if buf.utf8ByteSize ≥ 65536 then
            put buf
            bytes := bytes + buf.utf8ByteSize
            buf := ""
        -- the block is finished: its chunks are not read again
        let m := src.metas[i]!
        dropChunkRange g src.cache src.prbRef m.offset m.size
      buf := buf ++ (← okw w.finish)
      put buf
      bytes := bytes + buf.utf8ByteSize
      flushOut
      pure (some (quads, bytes))
    catch e =>
      IO.eprintln s!"l4sbm11 export: {e}"
      pure none
  match finishOk with
  | none =>
      if let some p := tmp then
        try IO.FS.removeFile p catch _ => pure ()
      pure 1
  | some (quads, bytes) =>
      if let some p := tmp then
        IO.FS.rename p o.out.get!
      let t1 ← IO.monoNanosNow
      IO.eprintln s!"sbm11: export format={formatLabel fmt} quads={quads} bytes={bytes} verify={g.verify.name} read-bytes={← g.readBytes.get} fetched-bytes={← g.fetchedBytes.get} file-bytes={← g.fileBytes.get} ms={ms t0 t1} peak-rss={← vmHWM}"
      pure 0

end Sbm11Export
