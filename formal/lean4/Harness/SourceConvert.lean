/-
Harness/SourceConvert — `l4source-convert`: read a document in any of the six
RDF syntaxes through the source layer and write it in any of the six, with the
library serialisers.

  l4source-convert SOURCE OUT [--from F] [--to G] [--base IRI]

F and G are labels of `RDF.formatOfLabel`; without them the extension of
SOURCE and of OUT decide (`RDF.formatOfPath`). There is no default syntax. The
source is read whole (`Source.parseDocument`), so the dataset is in memory.

The graph-only syntaxes (N-Triples, Turtle, RDF/XML) have no place for a graph
name: a dataset with named graphs is written with every triple in one graph
(the triples of all graphs together), and the tool says so on stderr.

Writers: the batch meaning of the serialiser layer (`Sink.serializeDataset`,
`L4Factoidal/RDF/Sink.lean`), which is the library's whole-graph serialisers:
N-Quads `Dataset.toNQuads`; N-Triples `Graph.toNTriples`; Turtle
`turtleOfGraphAuto`; TriG `Sink.datasetToTrig` (N-Triples lines for the default
graph, then a block per named graph); RDF/XML `RdfXmlWrite.graphToRdfXml`; JSON-LD
`FromRdf.fromRdf` in the RFC 8785 canonical form (expanded form). `l4sbm11 export`
writes a store with the stream meaning (`Sink.Writer`).

This is a harness: it reads and writes files. `tests/sbm11/` and the
per-syntax measurement of the shard packers use it to write one dataset in
every syntax (docs/designissues/2026-10-11-shardborough-vs-qlever.md, the
source layer).
-/
import L4Factoidal.RDF.SourceJsonLd
import L4Factoidal.RDF.SinkJsonLd

open L4Factoidal.RDF

namespace Harness.SourceConvert

/-- The dataset as text in syntax `fmt`: the batch writers of the serialiser
    layer (`Sink.serializeDataset`), the library's whole-graph serialisers. -/
def serialize (fmt : RdfFormat) (ds : Dataset) : Except String String :=
  Sink.serializeDataset Sink.withJsonLd fmt .rdf12 ds

def usage : String :=
  "usage: l4source-convert SOURCE OUT [--from F] [--to G] [--base IRI]  (F, G: ntriples, nquads, turtle, trig, rdfxml, jsonld; else the extension)"

private def pick (path : String) (flag : Option String) : IO RdfFormat := do
  let r := match flag with
    | some l => (formatOfLabel l).elim (Except.error s!"unknown format '{l}'") Except.ok
    | none => (formatOfPath path).elim
        (Except.error s!"cannot tell the RDF syntax of {path} from its name; give --from or --to") Except.ok
  match r with
  | .ok f => pure f
  | .error m => throw (IO.userError m)

def run (src out : String) (from_ to_ base : Option String) : IO UInt32 := do
  let fIn ← pick src from_
  let fOut ← pick out to_
  let t0 ← IO.monoNanosNow
  let text ← IO.FS.readFile src
  let ds ← match L4Factoidal.RDF.Source.parseDocument L4Factoidal.RDF.Source.withJsonLd fIn .rdf12 base text with
    | .ok ds => pure ds
    | .error e => throw (IO.userError s!"{src}: parse error at {e.pos}: {e.msg}")
  let t1 ← IO.monoNanosNow
  if !Source.hasNamedGraphs fOut && !ds.named.isEmpty then
    IO.eprintln s!"l4source-convert: {formatLabel fOut} has no graph name; the {ds.named.length} named graphs are written together"
  match serialize fOut ds with
  | .error m => throw (IO.userError s!"{out}: {m}")
  | .ok s =>
      IO.FS.writeFile out s
      let t2 ← IO.monoNanosNow
      IO.println s!"l4source-convert: {src} ({formatLabel fIn}) -> {out} ({formatLabel fOut}): bytes {text.utf8ByteSize} -> {s.utf8ByteSize}, read-ms {(t1 - t0) / 1000000}, write-ms {(t2 - t1) / 1000000}"
      pure 0

def parseArgs : List String → Option String × Option String × Option String → Option (Option String × Option String × Option String)
  | [], o => some o
  | "--from" :: v :: rest, (_, t, b) => parseArgs rest (some v, t, b)
  | "--to" :: v :: rest, (f, _, b) => parseArgs rest (f, some v, b)
  | "--base" :: v :: rest, (f, t, _) => parseArgs rest (f, t, some v)
  | _, _ => none

end Harness.SourceConvert

def main (args : List String) : IO UInt32 := do
  try
    match args with
    | src :: out :: rest =>
      match Harness.SourceConvert.parseArgs rest (none, none, none) with
      | some (f, t, b) => Harness.SourceConvert.run src out f t b
      | none => IO.eprintln Harness.SourceConvert.usage; pure 2
    | _ => IO.eprintln Harness.SourceConvert.usage; pure 2
  catch e =>
    IO.eprintln s!"l4source-convert: {e}"
    pure 1
