/-
Capability-aware planner, KR 2.3: a file read through a Façade-X style
mapping (as SPARQL Anything does) as capabilities.

https://github.com/danbri/factoidal/issues/801. Description document: a
SPARQL Anything service IRI, `x-sparql-anything:` followed by
comma-separated `key=value` options (https://sparql-anything.readthedocs.io,
"Configuration"). Read here: `location` (required), `media-type` (else the
file extension), `csv.headers` (default `false`), `csv.delimiter` (default
`,`), `namespace` (default `http://sparql.xyz/facade-x/data/`), `root`
(default `location` followed by `#`; a location without a scheme needs
`root`). When the file is at hand, its header row is read as a probe.

The mapping (Façade-X, CSV): the root container `<root> rdf:type fx:root`;
`<root> rdf:_n <row n>` for each data row `n` (from 1), with the row IRI
`<root>row<n>`; for each non-empty cell, `<row n> xyz:<column> "cell"` with
headers, `<row n> rdf:_<k> "cell"` without. Cells are `xsd:string`
literals. The container IRIs are this reader's choice (SPARQL Anything
mints blank nodes by default); the triples are otherwise the Façade-X
CSV triples.

Capabilities: a triple-form free scan (`facadex:scan`) and, when the
header row is known, one predicate-form free scan per column. Cost
model: `perCall` is the file size in bytes (each call reads the file),
`perRow` 1. Exact (`Exactness.exact`): the triples are a function of the
file. JSON and other formats are open, with an expected-failure case
naming https://github.com/danbri/factoidal/issues/801.
-/
import L4Factoidal.Planner.Kinds.Common
import L4Factoidal.CSVW.Dialect

namespace L4Factoidal.Planner.Kinds.FacadeX

open L4Factoidal.RDF L4Factoidal.SPARQL L4Factoidal.Planner L4Factoidal.Planner.Kinds

def fxNs : String := "http://sparql.xyz/facade-x/ns/"
def xyzNs : String := "http://sparql.xyz/facade-x/data/"
def rdfNs : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#"
def fxRoot : WfIri := ⟨fxNs ++ "root", rfl⟩
def rdfType : WfIri := ⟨rdfNs ++ "type", rfl⟩

def schemePrefix : String := "x-sparql-anything:"

structure Options where
  location : String
  format : String
  headers : Bool
  delimiter : String
  ns : String
  root : WfIri
  deriving Repr

def option? (kvs : List (String × String)) (k : String) : Option String := kvs.lookup k

def extensionOf (loc : String) : String := ((loc.splitOn ".").getLast?.getD "").toLower

/-- Read the options of a SPARQL Anything service IRI. -/
def readOptions (iri : String) : Except String Options := do
  if !iri.startsWith schemePrefix then throw s!"not a SPARQL Anything IRI: {iri}"
  let body := (iri.drop schemePrefix.length).toString
  let kvs := (body.splitOn ",").filterMap (fun kv =>
    match kv.splitOn "=" with
    | k :: v :: rest => some (k, "=".intercalate (v :: rest))
    | _ => none)
  let loc ← match option? kvs "location" with
    | some l => pure l
    | none => throw "SPARQL Anything IRI: no location"
  let fmt := match option? kvs "media-type" with
    | some "text/csv" => "csv"
    | some "application/json" => "json"
    | some m => m
    | none => extensionOf loc
  let rootText := (option? kvs "root").getD (loc ++ "#")
  let root ← match mkWfIri? rootText with
    | some r => if rootText.contains ' ' then throw s!"root is not an IRI: {rootText}" else pure r
    | none => throw s!"root is not an IRI (a relative location needs the root option): {rootText}"
  pure { location := loc, format := fmt,
         headers := (option? kvs "csv.headers") == some "true",
         delimiter := (option? kvs "csv.delimiter").getD ",",
         ns := (option? kvs "namespace").getD xyzNs, root := root }

def nameChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '-' || c == '.'

/-- The predicate of a column. -/
def columnIri? (o : Options) (name : String) : Option WfIri :=
  if !name.isEmpty && name.all nameChar then mkWfIri? (o.ns ++ name) else none

def memberIri? (k : Nat) : Option WfIri := mkWfIri? (rdfNs ++ "_" ++ toString k)

def rowIri? (o : Options) (n : Nat) : Option WfIri := mkWfIri? (o.root.val ++ "row" ++ toString n)

def dialectOf (o : Options) (headers : Bool) : L4Factoidal.CSVW.ResolvedDialect :=
  ({ delimiter := some o.delimiter, headerRowCount := some (if headers then 1 else 0) } :
    L4Factoidal.CSVW.Dialect).resolve

/-- The header row, read as a probe. -/
def headerOf (o : Options) (text : String) : List String :=
  match (L4Factoidal.CSVW.read (dialectOf o true) text).header with
  | r :: _ => r.cells
  | [] => []

/-- The predicate of each column: header names, or `rdf:_k`. -/
def columnPreds (o : Options) (text : String) : Except String (List WfIri) :=
  if o.headers then
    (headerOf o text).mapM (fun h => match columnIri? o h with
      | some p => .ok p
      | none => .error s!"column name is not a local name: {h}")
  else
    let width := ((L4Factoidal.CSVW.read (dialectOf o false) text).rows.map (·.cells.length)).foldl max 0
    (List.range width).mapM (fun k => match memberIri? (k + 1) with
      | some p => .ok p
      | none => .error "rdf:_k")

/-- The Façade-X triples of a CSV file. -/
def triplesOf (o : Options) (text : String) : Except String Graph := do
  if o.format != "csv" then throw s!"format {o.format}: only csv is read"
  let preds ← columnPreds o text
  let rows := (L4Factoidal.CSVW.read (dialectOf o o.headers) text).rows
  let root : Subject := .iri o.root
  let mut out : Array Triple := #[{ s := root, p := rdfType, o := .iri fxRoot }]
  let mut n := 0
  for r in rows do
    n := n + 1
    let some ri := rowIri? o n | throw "row IRI"
    let some mi := memberIri? n | throw "rdf:_n"
    out := out.push { s := root, p := mi, o := .iri ri }
    for (cell, p) in r.cells.zip preds do
      if !cell.isEmpty then
        out := out.push { s := .iri ri, p := p, o := .literal (Literal.string cell) }
  pure out.toList

/-- The capabilities. `text` is the file when it is at hand (the header
probe); without it only the triple-form scan is described. -/
def describe (iri : String) (text : Option String := none) : Except String (List Described) := do
  let o ← readOptions iri
  if o.format != "csv" then throw s!"format {o.format}: only csv is read"
  let size := (text.map (·.utf8ByteSize)).getD 1
  let cost : CostModel := { perCall := max 1 size, perRow := 1 }
  let scan : Described :=
    { kind := "facadex", partition := none, mapping := graphMapping none,
      cap := { name := "facadex:scan", arity := 3, inputs := [], location := o.location,
               cost := cost, exactness := .exact } }
  let preds ← match text with
    | some t => columnPreds o t
    | none => pure []
  pure (scan :: preds.map (fun p =>
    { kind := "facadex", partition := some p, mapping := graphMapping (some p),
      cap := { name := s!"facadex:{localName p}", arity := 2, inputs := [], location := o.location,
               cost := cost, exactness := .exact } }))

end L4Factoidal.Planner.Kinds.FacadeX
