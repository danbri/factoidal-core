/-
L4Factoidal.RML.Open — from a logical source description and the bytes
of its file to the list of logical iterations.

Spec: RML-IO (https://w3id.org/rml/io/spec), "Logical Source in RML":
the source access description (`rml:FilePath` with `rml:root` and
`rml:path`), `rml:encoding`, `rml:compression` and `rml:null`; and
RML-IO-Registry for the reference formulations.

## Reading a file is the host's job; deciding what is in it is not

`FileAccess` is the only seam to the file system. It maps a root and a
path to bytes, or to nothing. Everything after that is a total function
of the bytes: undo the compression, decode the text, parse it in the
reference formulation's format, cut it into iterations. A host (the
test runner, an HTTP server) supplies `FileAccess`; the semantics never
call `IO`.

## Four ways a source is rejected

Each is a SOURCE error (`RML.Error`), found here and not at term
generation: the file cannot be read; its compression or encoding is not
one this module has; its text is not a document of the declared
format; its iterator is not an expression of the declared formulation.
A CSV file with a row whose width differs from the header's is a
document that is not CSV in the sense RML needs, and invalidates the
whole source (`RMLSTC0010a`, `RMLSTC0010b`) rather than yielding the
rows that happen to fit.

## Scope

JSONPath, CSV and XPath over files. `rml:SQL2008Table` and
`rml:SQL2008Query` need a database; a source with a D2RQ access
description is rejected with a source error that says so.
-/
import L4Factoidal.RML.Model
import L4Factoidal.RML.Record
import L4Factoidal.RML.Encoding
import L4Factoidal.RML.Compression
import L4Factoidal.RML.Sources
import L4Factoidal.JSON.Parser
import L4Factoidal.XML.Parser

namespace L4Factoidal.RML

open L4Factoidal.JSON
open L4Factoidal.XPath.Full

/-- The seam to the file system: a root (the IRI of
    `rml:MappingDirectory` or `rml:CurrentWorkingDirectory`, the text of
    a literal directory, or empty) and a path, to the file's bytes. -/
structure FileAccess where
  read : String → String → Option ByteArray

private def srcErr (ls : LogicalSource) (msg : String) : RmlError :=
  RmlError.source ls.path "RML-IO, Logical Source: source" msg

/-- The rows of a CSV document as table records. The first row names
    the columns. A column whose value is one of the source's `rml:null`
    values is left out of the row, so a reference to it selects nothing.
    A blank line is not a row. -/
def csvRecords (text : String) (nulls : List String) : Except String (List Record) :=
  match csvParseRows text with
  | [] => .ok []
  | header :: rows =>
      let rows := rows.filter (fun r => r != [""])
      if rows.any (fun r => r.length != header.length) then
        .error "a CSV row has a different number of fields than the header"
      else
        .ok (rows.map (fun r =>
          Record.ofColumns header ((header.zip r).filter (fun p => !nulls.contains p.2))))

/-- The iterations of a JSON document: what the iterator selects, or the
    document itself when the source states none. -/
def jsonRecords (iterator : Option String) (doc : Json) : Except String (List Record) :=
  match iterator with
  | none => .ok [.json doc]
  | some itr =>
      match parseJsonPath itr with
      | none => .error s!"'{itr}' is not a valid JSONPath iterator"
      | some _ => .ok ((evalPath itr doc).map Record.json)

/-- The iterations of an XML document: the nodes the XPath iterator
    selects from the document node. -/
def xmlRecords (iterator : Option String) (ns : List (String × String)) (doc : Doc)
    : Except String (List Record) :=
  match iterator with
  | none => .ok [Record.xml doc (.doc doc) ns]
  | some itr =>
      match evalText { doc := doc, item := .doc doc, nsctx := ns } itr with
      | some (.nodes its) => .ok (its.map (fun i => Record.xml doc i ns))
      | _ => .error s!"'{itr}' is not an XPath iterator that selects nodes"

/-- Guess a formulation from a file name, for a source that states none
    (RML-IO: the formulation is inferred from the kind of source). -/
def inferFormulation (path : String) : String :=
  if path.endsWith ".json" then jsonPathIri
  else if path.endsWith ".csv" then csvIri
  else if path.endsWith ".xml" then xpathIri
  else ""

/-- Open a logical source: the bytes, undone, decoded, parsed, cut into
    iterations. -/
def openRecords (ls : LogicalSource) (fa : FileAccess) : Except RmlError (List Record) :=
  if !ls.accessKind.isEmpty then
    .error (RmlError.unsupported ls.path "RML-IO, Source" "database source"
      s!"the source is a database ({ls.accessKind}); this port has no database access")
  else
  match fa.read ls.root ls.path with
  | none => .error (srcErr ls s!"the file '{ls.path}' cannot be read")
  | some raw =>
  match Compression.ofIri? ls.compression with
  | none => .error (srcErr ls s!"'{ls.compression}' is not a compression RML-IO defines")
  | some comp =>
  match decompress comp raw with
  | .error (.unsupported w) =>
      .error (RmlError.unsupported ls.path "RML-IO, Compression formats" s!"{w} codec"
        s!"the file '{ls.path}' is {comp.label}-compressed and this port has no {w} decoder")
  | .error (.corrupt m) => .error (srcErr ls s!"the {comp.label} file is corrupt: {m}")
  | .ok bytes =>
  match Encoding.ofIri? ls.encoding with
  | none => .error (srcErr ls s!"'{ls.encoding}' is not an encoding RML-IO defines")
  | some enc =>
  match decodeBytes enc bytes with
  | none => .error (srcErr ls s!"the file is not valid {if enc == .utf16 then "UTF-16" else "UTF-8"}")
  | some text =>
  let form := if ls.refFormulation.isEmpty then inferFormulation ls.path else ls.refFormulation
  let wrap (r : Except String (List Record)) : Except RmlError (List Record) :=
    match r with
    | .ok rs => .ok rs
    | .error m => .error (srcErr ls m)
  if form == jsonPathIri then
    match parseJson text with
    | .error _ => .error (srcErr ls "the file is not valid JSON")
    | .ok j => wrap (jsonRecords ls.iterator j)
  else if form == csvIri then
    wrap (csvRecords text ls.nulls)
  else if form == xpathIri then
    match L4Factoidal.XML.parseXML text with
    | .error _ => .error (srcErr ls "the file is not well-formed XML")
    | .ok d => wrap (xmlRecords ls.iterator ls.namespaces d.children)
  else if form == sparqlResultsCsvIri then
    .error (RmlError.unsupported ls.path "RML-IO, Reference formulations" "SPARQL query source"
      "the source is a file queried with SPARQL; this port does not yet run the query")
  else if form == "http://w3id.org/rml/SQL2008Table" || form == "http://w3id.org/rml/SQL2008Query" then
    .error (RmlError.unsupported ls.path "RML-IO, Reference formulations" "database source"
      s!"the reference formulation '{form}' needs a relational database")
  else .error (RmlError.unsupported ls.path "RML-IO, Reference formulations"
      "reference formulation" s!"the reference formulation '{form}' is not supported by this port")

/-! ## Build-time checks -/

private def files (entries : List (String × String)) : FileAccess :=
  { read := fun _ p => (entries.find? (fun e => e.1 == p)).map (fun e => e.2.toUTF8) }

private def jsonLs : LogicalSource :=
  { path := "a.json", iterator := some "$[*]", refFormulation := jsonPathIri }

#guard match openRecords jsonLs (files [("a.json", "[{\"id\":1},{\"id\":2}]")]) with
       | .ok rs => rs.length == 2 | .error _ => false
-- A missing file, bad JSON and a bad iterator are SOURCE errors.
#guard match openRecords jsonLs (files []) with | .error _ => true | .ok _ => false
#guard match openRecords jsonLs (files [("a.json", "[{")]) with | .error _ => true | .ok _ => false
#guard match openRecords { jsonLs with iterator := some "$[*]]" }
         (files [("a.json", "[]")]) with | .error _ => true | .ok _ => false
-- No iterator: the whole document is one record.
#guard match openRecords { jsonLs with iterator := none } (files [("a.json", "[1,2]")]) with
       | .ok rs => rs.length == 1 | .error _ => false

private def csvLs : LogicalSource :=
  { path := "a.csv", refFormulation := csvIri }

#guard match openRecords csvLs (files [("a.csv", "id,name\n1,A\n2,B\n")]) with
       | .ok rs => rs.length == 2 | .error _ => false
-- A short row invalidates the whole source (RMLSTC0010a/b), and a
-- trailing blank line does not count as a row.
#guard match openRecords csvLs (files [("a.csv", "id,name,age\n6,Phoebe Buffay 37\n")]) with
       | .error _ => true | .ok _ => false
#guard match openRecords csvLs (files [("a.csv", "id,name\n1,A\n\n")]) with
       | .ok rs => rs.length == 1 | .error _ => false
-- `rml:null` drops a column from the row.
#guard match openRecords { csvLs with nulls := [""] } (files [("a.csv", "id,name\n1,\n")]) with
       | .ok [r] => (r.values "name").1.isEmpty && (r.values "id").1.length == 1
       | _ => false
#guard match openRecords csvLs (files [("a.csv", "id,name\n1,\n")]) with
       | .ok [r] => (r.values "name").1.length == 1
       | _ => false

private def xmlLs : LogicalSource :=
  { path := "a.xml", refFormulation := xpathIri, iterator := some "/people/person" }

private def peopleXml : String :=
  "<people><person id=\"1\"><name>A</name></person><person id=\"2\"><name>B</name></person></people>"

#guard match openRecords xmlLs (files [("a.xml", peopleXml)]) with
       | .ok rs => rs.length == 2 | .error _ => false
#guard match openRecords xmlLs (files [("a.xml", peopleXml)]) with
       | .ok (r :: _) => (r.values "@id").1 == [{ lexical := "1" }] &&
                         (r.values "name/text()").1 == [{ lexical := "A" }]
       | _ => false
-- A sibling's data through `..`.
#guard match openRecords { xmlLs with iterator := some "/people/person/name" }
         (files [("a.xml", peopleXml)]) with
       | .ok (_ :: r :: _) => (r.values "../@id").1 == [{ lexical := "2" }]
       | _ => false
#guard match openRecords xmlLs (files [("a.xml", "<people>")]) with
       | .error _ => true | .ok _ => false

-- A database source and an unknown formulation are `unsupported`, not
-- guessed and not an empty source.
#guard match openRecords { csvLs with accessKind := "http://www.wiwiss.fu-berlin.de/suhl/bizer/D2RQ/0.1#Database" }
         (files [("a.csv", "id\n1\n")]) with
       | .error e => e.kind == .unsupported && e.bucket == "database source" | .ok _ => false
#guard match openRecords { csvLs with refFormulation := "http://w3id.org/rml/SQL2008Table" }
         (files [("a.csv", "id\n1\n")]) with
       | .error e => e.kind == .unsupported && e.bucket == "database source" | .ok _ => false
#guard match openRecords { csvLs with refFormulation := "http://example.com/Formulation" }
         (files [("a.csv", "id\n1\n")]) with
       | .error e => e.kind == .unsupported | .ok _ => false
-- Encoding: UTF-16 text is read when the source says so, and not otherwise.
private def utf16Files : FileAccess :=
  { read := fun _ _ => some (encodeText .utf16 "id,name\n1,Zoë\n") }
#guard match openRecords { csvLs with encoding := utf16Iri } utf16Files with
       | .ok [r] => (r.values "name").1 == [{ lexical := "Zoë" }]
       | _ => false
#guard match openRecords csvLs utf16Files with | .error _ => true | .ok _ => false
-- A file that is not in the compression it names is a source error.
#guard match openRecords { csvLs with compression := "http://w3id.org/rml/gzip" }
         (files [("a.csv", "id\n1\n")]) with
       | .error e => e.kind == .source | .ok _ => false
-- A compressed file is read through its codec; tar.xz is a gap and says so.
private def gz : FileAccess :=
  { read := fun _ _ => (compress .gzip "a.csv" "id,name\n1,A\n".toUTF8).toOption }
#guard match openRecords { csvLs with compression := "http://w3id.org/rml/gzip" } gz with
       | .ok rs => rs.length == 1 | .error _ => false
#guard match openRecords { csvLs with compression := "http://w3id.org/rml/tarxz" } gz with
       | .error e => e.kind == .unsupported && e.bucket == "tar.xz codec" | .ok _ => false

end L4Factoidal.RML
