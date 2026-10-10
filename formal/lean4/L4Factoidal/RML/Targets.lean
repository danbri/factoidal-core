/-
L4Factoidal.RML.Targets — export the generated quads to their logical
targets, serialised.

Spec: RML-IO (https://w3id.org/rml/io/spec), "Logical Target in RML" and
"Logical Target vocabulary": a term map MAY name logical targets; a
triple is exported to the target of EVERY term map involved in
generating it, and a triple none of whose term maps names a target goes
to the processor's default target. A target says how its triples are
serialised (`rml:serialization`, default N-Quads), compressed and
encoded.

## What a target receives

The quads carry the names of the targets they belong to (`QuadOut.targets`,
set by `RML.Eval`). `quadsFor` picks them. A serialisation that has no
place for a graph name (every format but N-Quads, TriG and JSON-LD)
receives the UNION of the graphs: a triple generated into a named graph
is written without its graph, since the format cannot say it.

## The check is a round trip through an independent reader

`ourDump` serialises the quads and reads the bytes back with the parser
of the same format, which is how a consumer of the file sees them.
Comparing that with the expected file read the same way tests the
serialiser and the reader together, not the quads against themselves.
-/
import L4Factoidal.RML.Eval
import L4Factoidal.RML.Encoding
import L4Factoidal.RML.Compression
import L4Factoidal.Syntax.NQuads
import L4Factoidal.Syntax.NTriples
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TurtleSerialize
import L4Factoidal.Syntax.TriG
import L4Factoidal.Syntax.RdfJson
import L4Factoidal.Syntax.RdfXml
import L4Factoidal.Syntax.RdfXmlWrite
import L4Factoidal.JSONLD.FromRdf
import L4Factoidal.JSONLD.ToRdf
import L4Factoidal.JSON.Serialize

namespace L4Factoidal.RML

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.JSON

/-- The serialisations RML-IO names with the W3C `formats:` vocabulary
    (https://www.w3.org/ns/formats/). -/
inductive Serialization where
  | nquads | ntriples | n3 | turtle | trig | jsonld | rdfjson | rdfxml
deriving Repr, DecidableEq, Inhabited

def formatsNs : String := "http://www.w3.org/ns/formats/"

/-- The serialisation a `rml:serialization` IRI names; empty is N-Quads.
    `none` for a format this port does not write. -/
def Serialization.ofIri? (iri : String) : Option Serialization :=
  if iri.isEmpty || iri == formatsNs ++ "N-Quads" then some .nquads
  else if iri == formatsNs ++ "N-Triples" then some .ntriples
  else if iri == formatsNs ++ "N3" then some .n3
  else if iri == formatsNs ++ "Turtle" then some .turtle
  else if iri == formatsNs ++ "TriG" then some .trig
  else if iri == formatsNs ++ "JSON-LD" then some .jsonld
  else if iri == formatsNs ++ "RDF_JSON" then some .rdfjson
  else if iri == formatsNs ++ "RDF_XML" then some .rdfxml
  else none

/-- The quads that belong to a target. `none` is the default target: the
    quads no term map sent anywhere else. -/
def quadsFor (target : Option String) (qs : List QuadOut) : List QuadOut :=
  match target with
  | none => qs.filter (fun q => q.targets.isEmpty)
  | some t => qs.filter (fun q => q.targets.contains t)

private def graphSubject? : Term → Option Subject
  | .iri i => some (.iri i)
  | .bnode b => some (.bnode b)
  | _ => none

private def tripleOf (q : QuadOut) : Triple := { s := q.s, p := q.p, o := q.o }

/-- A graph is a SET of triples: the first occurrence of each is kept. -/
def dedupGraph (g : Graph) : Graph :=
  g.foldl (fun acc t => if acc.any (fun u => u.eqb t) then acc else acc ++ [t]) []

/-- The quads as an RDF dataset: the default graph, and one named graph
    per graph name in first-use order. -/
def datasetOfQuads (qs : List QuadOut) : Dataset :=
  let dflt := dedupGraph ((qs.filter (fun q => q.g.isNone)).map tripleOf)
  let names : List Subject := qs.foldl (fun acc q =>
    match q.g.bind graphSubject? with
    | some n => if acc.any (fun m => m.eqb n) then acc else acc ++ [n]
    | none => acc) []
  { default := dflt
    named := names.map (fun n =>
      { name := n
        graph := dedupGraph ((qs.filter (fun q =>
          match q.g.bind graphSubject? with | some m => m.eqb n | none => false)).map tripleOf) }) }

/-- Every blank node label of a term, in order of appearance. -/
private def termBnodes : Term → List String
  | .bnode b => [b]
  | .tripleTerm s _ o => (match s with | .bnode b => [b] | _ => []) ++ termBnodes o
  | _ => []

private def relabelTerm (m : List (String × String)) : Term → Term
  | .bnode b => .bnode ((m.find? (·.1 == b)).map (·.2) |>.getD b)
  | .tripleTerm s p o =>
      .tripleTerm (match s with | .bnode b => .bnode ((m.find? (·.1 == b)).map (·.2) |>.getD b) | s => s)
        p (relabelTerm m o)
  | t => t

private def relabelSubject (m : List (String × String)) : Subject → Subject
  | .bnode b => .bnode ((m.find? (·.1 == b)).map (·.2) |>.getD b)
  | s => s

/-- Give every blank node a label every serialisation can write: `b0`,
    `b1`, in order of first appearance. The labels the evaluator makes
    carry template text and graph names (`l/a~g~http://...`), which no
    syntax accepts as a blank node label, and the mapping from old to new
    is injective, so two blank nodes stay two. -/
def relabelBlankNodes (ds : Dataset) : Dataset :=
  let graphTriples := ds.default ++ ds.named.flatMap (·.graph)
  let names := ds.named.map (·.name)
  let labels : List String :=
    (graphTriples.flatMap (fun t => (match t.s with | .bnode b => [b] | _ => []) ++ termBnodes t.o)) ++
    (names.flatMap (fun n => match n with | .bnode b => [b] | _ => []))
  let uniq := labels.foldl (fun acc l => if acc.contains l then acc else acc ++ [l]) ([] : List String)
  let m : List (String × String) := uniq.zipIdx.map (fun (l, k) => (l, "b" ++ toString k))
  let rt (t : Triple) : Triple := { t with s := relabelSubject m t.s, o := relabelTerm m t.o }
  { default := ds.default.map rt
    named := ds.named.map (fun ng => { name := relabelSubject m ng.name, graph := ng.graph.map rt }) }

/-- The union of a dataset's graphs: for a serialisation with no graphs. -/
def datasetUnion (ds : Dataset) : Graph :=
  dedupGraph (ds.default ++ ds.named.flatMap (·.graph))

/-- TriG written plainly: the default graph's triples, then each named
    graph as `<name> { ... }`, triples as N-Triples lines (which TriG
    accepts as they are). -/
def trigOfDataset (ds : Dataset) : Except String String := do
  let mut out := (← Graph.toNTriples ds.default .rdf12)
  for ng in ds.named do
    out := out ++ Subject.toNTriples ng.name ++ " {\n" ++ (← Graph.toNTriples ng.graph .rdf12) ++ "}\n"
  return out

/-- Serialise a dataset in a format. -/
def serializeDataset (fmt : Serialization) (ds0 : Dataset) : Except String String :=
  let ds := relabelBlankNodes ds0
  match fmt with
  | .nquads   => Syntax.Dataset.toNQuads ds .rdf12
  | .ntriples => Graph.toNTriples (datasetUnion ds) .rdf12
  | .n3 | .turtle => .ok (turtleOfGraphAuto (datasetUnion ds))
  | .trig     => trigOfDataset ds
  | .jsonld   =>
      match JSONLD.FromRdf.fromRdf ds {} with
      | some j => .ok (toStringCompact j)
      | none => .error "the dataset has no JSON-LD form"
  | .rdfjson  => RdfJson.graphToRdfJson (datasetUnion ds)
  | .rdfxml   => RdfXmlWrite.graphToRdfXml (datasetUnion ds)

private def ofParse {α : Type} (e : Except ParseError α) : Except String α :=
  match e with
  | .ok a => .ok a
  | .error err => .error err.msg

/-- Read a serialised dataset back. -/
def parseDump (fmt : Serialization) (text : String) : Except String Dataset :=
  let asDataset (g : Graph) : Dataset := { default := g, named := [] }
  match fmt with
  | .nquads   => ofParse (parseNQuads text .rdf12)
  | .ntriples => (ofParse (parseNTriples text .rdf12)).map asDataset
  | .n3 | .turtle => (ofParse (parseTurtle text none .rdf12)).map asDataset
  | .trig     => ofParse (parseTriG text none .rdf12)
  | .jsonld   =>
      match JSONLD.parseJsonLd (fun _ => none) text none none none none with
      | .ok ds => .ok ds
      | .error _ => .error "not a JSON-LD document this port can read without a remote context"
  | .rdfjson  => (RdfJson.parseRdfJson text).map asDataset
  | .rdfxml   => (ofParse (RdfXml.parseRdfXml text none)).map asDataset

/-- Why a target could not be written or read: the port lacks something
    (`unsupported`, with the name of what), or the data is wrong. -/
inductive TargetError where
  | unsupported (bucket reason : String)
  | failed (msg : String)

def TargetError.message : TargetError → String
  | .unsupported b r => s!"{b}: {r}"
  | .failed m => m

private def liftStr {α : Type} (e : Except String α) : Except TargetError α :=
  match e with | .ok a => .ok a | .error m => .error (.failed m)

private def liftCodec {α : Type} (e : Except CodecError α) : Except TargetError α :=
  match e with
  | .ok a => .ok a
  | .error (.unsupported w) => .error (.unsupported s!"{w} codec" s!"no {w} codec")
  | .error (.corrupt m) => .error (.failed m)

/-- The file name inside an archive: the target's file name without its
    compression extension. -/
def entryName (t : LogicalTarget) : String :=
  let base := ((t.path.splitOn "/").getLast?).getD t.path
  let strip := [".tar.gz", ".tar.xz", ".gz", ".zip", ".xz"]
  match strip.find? (fun x => base.endsWith x) with
  | some x => (base.dropEnd x.length).toString
  | none => base

/-- The bytes a target holds for the quads it receives: serialised,
    encoded, compressed. -/
def renderTarget (t : LogicalTarget) (qs : List QuadOut) : Except TargetError ByteArray := do
  if !t.accessKind.isEmpty then
    throw (.unsupported "target access" s!"the target has {t.accessKind}")
  let fmt ← match Serialization.ofIri? t.serialization with
    | some f => pure f
    | none => throw (.unsupported "serialisation" s!"'{t.serialization}' is not a serialisation this port writes")
  let enc ← match Encoding.ofIri? t.encoding with
    | some e => pure e
    | none => throw (.failed s!"'{t.encoding}' is not an encoding RML-IO defines")
  let comp ← match Compression.ofIri? t.compression with
    | some c => pure c
    | none => throw (.failed s!"'{t.compression}' is not a compression RML-IO defines")
  let text ← liftStr (serializeDataset fmt (datasetOfQuads qs))
  liftCodec (compress comp (entryName t) (encodeText enc text))

/-- Read the bytes of a target file back into a dataset: decompressed,
    decoded, parsed in the target's serialisation. -/
def readTarget (t : LogicalTarget) (bytes : ByteArray) : Except TargetError Dataset := do
  let fmt ← match Serialization.ofIri? t.serialization with
    | some f => pure f
    | none => throw (.unsupported "serialisation" s!"'{t.serialization}' is not a serialisation this port reads")
  let enc ← match Encoding.ofIri? t.encoding with
    | some e => pure e
    | none => throw (.failed s!"'{t.encoding}' is not an encoding RML-IO defines")
  let comp ← match Compression.ofIri? t.compression with
    | some c => pure c
    | none => throw (.failed s!"'{t.compression}' is not a compression RML-IO defines")
  let raw ← liftCodec (decompress comp bytes)
  let text ← match decodeBytes enc raw with
    | some s => pure s
    | none => throw (.failed "the file is not valid text in the target's encoding")
  liftStr (parseDump fmt text)

/-- What a consumer of the target's file sees: write, then read back. -/
def ourDump (t : LogicalTarget) (qs : List QuadOut) : Except TargetError Dataset := do
  readTarget t (← renderTarget t qs)

/-! ## Build-time checks -/

private def iri! (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"urn:invalid", rfl⟩

private def quad (s p o : String) (targets : List String) (g : Option String := none) : QuadOut :=
  { s := .iri (iri! s), p := iri! p, o := .literal (Literal.string o),
    g := g.map (fun x => Term.iri (iri! x)), targets := targets }

private def qs : List QuadOut :=
  [ quad "http://ex/a" "http://ex/p" "1" []
  , quad "http://ex/a" "http://ex/q" "2" ["t1"]
  , quad "http://ex/b" "http://ex/q" "3" ["t1", "t2"]
  , quad "http://ex/c" "http://ex/q" "4" ["t2"] (some "http://ex/g") ]

-- The default target takes the quads that name no target; a named target
-- takes every quad that names it, so a quad can go to two targets.
#guard (quadsFor none qs).length == 1
#guard (quadsFor (some "t1") qs).length == 2
#guard (quadsFor (some "t2") qs).length == 2
#guard (quadsFor (some "t3") qs).isEmpty

-- A named graph shows up as a named graph, and a union has no graph.
#guard (datasetOfQuads qs).named.length == 1
#guard (datasetOfQuads qs).default.length == 3
#guard (datasetUnion (datasetOfQuads qs)).length == 4
-- A repeated quad is one triple.
#guard (datasetOfQuads (qs ++ qs)).default.length == 3

private def target (fmt : String) : LogicalTarget :=
  { id := "t", path := "d", serialization := fmt }

/-- A dataset read back from a serialisation has the same triples. -/
private def roundTrips (fmt : String) (withGraph : Bool) : Bool :=
  match ourDump (target fmt) qs with
  | .error _ => false
  | .ok ds =>
      (ds.default ++ ds.named.flatMap (·.graph)).length == 4 &&
      (if withGraph then ds.named.length == 1 else ds.named.isEmpty)

#guard roundTrips "" true
#guard roundTrips (formatsNs ++ "N-Quads") true
#guard roundTrips (formatsNs ++ "TriG") true
#guard roundTrips (formatsNs ++ "N-Triples") false
#guard roundTrips (formatsNs ++ "Turtle") false
#guard roundTrips (formatsNs ++ "N3") false
#guard roundTrips (formatsNs ++ "RDF_JSON") false
#guard roundTrips (formatsNs ++ "RDF_XML") false
#guard roundTrips (formatsNs ++ "JSON-LD") true
-- An unknown format and a non-file target are errors, not an empty file.
#guard (ourDump (target "http://example.com/fmt") qs).toOption.isNone
#guard (ourDump { target "" with accessKind := "x" } qs).toOption.isNone
-- Compressed targets round-trip through their codec.
#guard match ourDump { target "" with compression := "http://w3id.org/rml/gzip" } qs with
       | .ok ds => (ds.default ++ ds.named.flatMap (·.graph)).length == 4 | .error _ => false
#guard match ourDump { target "" with compression := "http://w3id.org/rml/zip", path := "d.nq.zip" } qs with
       | .ok ds => (ds.default ++ ds.named.flatMap (·.graph)).length == 4 | .error _ => false
#guard match ourDump { target "" with compression := "http://w3id.org/rml/targz", path := "d.nq.tar.gz" } qs with
       | .ok ds => (ds.default ++ ds.named.flatMap (·.graph)).length == 4 | .error _ => false
#guard match ourDump { target "" with compression := "http://w3id.org/rml/tarxz", path := "d.nq.tar.xz" } qs with
       | .ok ds => (ds.default ++ ds.named.flatMap (·.graph)).length == 4 | .error _ => false
#guard entryName { target "" with path := "./dump1.nq.tar.gz" } == "dump1.nq"
#guard entryName { target "" with path := "dump1.nq.gz" } == "dump1.nq"
#guard entryName { target "" with path := "dump1.nq" } == "dump1.nq"
-- Blank node labels no syntax accepts are replaced by labels it does, and
-- two blank nodes stay two.
private def oddBnodeQuads : List QuadOut :=
  [ { s := .bnode "l/a~g~http://ex/g", p := iri! "http://ex/p", o := .bnode "x y", g := none }
  , { s := .bnode "x y", p := iri! "http://ex/p", o := .literal (Literal.string "v"), g := none } ]
#guard match serializeDataset .nquads (datasetOfQuads oddBnodeQuads) with
       | .ok t => (t.splitOn "_:b0").length == 2 && (t.splitOn "_:b1").length == 3
       | .error _ => false
#guard match ourDump (target "") oddBnodeQuads with
       | .ok ds => ds.default.length == 2
       | .error _ => false
-- UTF-16 target: the bytes differ from UTF-8 and read back the same.
#guard match renderTarget { target "" with encoding := utf16Iri } qs,
             renderTarget (target "") qs with
       | .ok a, .ok b => a.size > b.size
       | _, _ => false
#guard match ourDump { target "" with encoding := utf16Iri } qs with
       | .ok ds => (ds.default ++ ds.named.flatMap (·.graph)).length == 4
       | .error _ => false

end L4Factoidal.RML
