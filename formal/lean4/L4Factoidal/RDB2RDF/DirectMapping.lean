/-
L4Factoidal.RDB2RDF.DirectMapping — the Direct Mapping of a relational
database to an RDF graph.

Spec: A Direct Mapping of Relational Data to RDF, W3C Recommendation
27 September 2012 (https://www.w3.org/TR/2012/REC-rdb-direct-mapping-20120927/),
§2 (IRIs: table IRI, literal property IRI, reference property IRI, row node)
and §4 (the triples: a type triple per row, a literal triple per non-NULL
cell, a reference triple per foreign key whose columns are all non-NULL).
Literal triples use the natural RDF literal of R2RML 2012 §10.2
(`R2RML2012.naturalRVal`). Percent-encoding (§2.2) is the IRI-safe form of
R2RML 2012 §7.3 (`RML.encodeIriSafe`): every ASCII character other than an
unreserved character is percent-encoded; non-ASCII characters stay.

A row of a table with a primary key has an IRI. A row of a table without one
has a blank node, `t<i>r<j>` for row `j` of table `i`; a reference to such a
row uses the same blank node.

Tracking: https://github.com/danbri/factoidal/issues/1165.
-/
import L4Factoidal.RDB2RDF.NaturalLiteral
import L4Factoidal.RML.Mapping
import L4Factoidal.RDF.Graph

namespace L4Factoidal.RDB2RDF.DM2012

open L4Factoidal.SQL
open L4Factoidal.RDF
open L4Factoidal.RDB2RDF.R2RML2012

def enc (s : String) : String := L4Factoidal.RML.encodeIriSafe s

def rdfType : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

/-- §2.2 table IRI. -/
def tableIri (base : String) (t : Table) : String := base ++ enc t.name

/-- §2.2 literal property IRI. -/
def literalPropIri (base : String) (t : Table) (c : String) : String :=
  base ++ enc t.name ++ "#" ++ enc c

/-- §2.2 reference property IRI. -/
def referencePropIri (base : String) (t : Table) (fk : FKey) : String :=
  base ++ enc t.name ++ "#ref-" ++ ";".intercalate (fk.cols.map enc)

def cellOf (t : Table) (row : List Value) (c : String) : Value :=
  match t.colIndex? c with
  | some i => row[i]?.getD .null
  | none => .null

/-- The lexical form that a key value has in a row node IRI. -/
def keyLexical (v : Value) : String :=
  match naturalRVal v with
  | some r => r.lexical
  | none => ""

/-- The row node of row `j` of table `i` (§2.2). -/
inductive RowNode where
  | iri (s : String)
  | bnode (s : String)
  deriving DecidableEq, Repr

def rowNode (base : String) (i : Nat) (t : Table) (j : Nat) (row : List Value) : RowNode :=
  if t.primaryKey.isEmpty then .bnode s!"t{i}r{j}"
  else .iri (base ++ enc t.name ++ "/" ++
    ";".intercalate (t.primaryKey.map fun c => enc c ++ "=" ++ enc (keyLexical (cellOf t row c))))

def mkIri? (s : String) : Except String WfIri :=
  if h : isIri s then .ok ⟨s, h⟩ else .error s!"not an IRI: {s}"

def RowNode.toSubject : RowNode → Except String Subject
  | .iri s => do let i ← mkIri? s; pure (.iri i)
  | .bnode b => .ok (.bnode b)

def literalTerm (r : L4Factoidal.RML.RVal) : Except String Term := do
  let dt ← mkIri? (r.natural.getD "http://www.w3.org/2001/XMLSchema#string")
  match Literal.toWf? { lexicalForm := r.lexical, datatype := dt, langTag := none, direction := none } with
  | some l => pure (.literal l)
  | none => throw s!"not a well-formed literal: {r.lexical}"

/-- The row of `refTable` whose `refCols` hold the values `vals` (SQL
    equality), with its index. -/
def findReferenced (t : Table) (refCols : List String) (vals : List Value) : Option (Nat × List Value) :=
  (t.rows.zipIdx).findSome? fun (row, j) =>
    let ok := (refCols.zip vals).all fun (c, v) =>
      match compareValues (cellOf t row c) v with
      | .ok (some .eq) => true
      | _ => false
    if ok then some (j, row) else none

def tableIndex (db : Database) (name : String) : Option (Nat × Table) :=
  (db.tables.zipIdx).findSome? fun (t, i) => if t.name == name then some (i, t) else none

/-- The triples of one row (§4.2 to §4.4). -/
def rowTriples (base : String) (db : Database) (i : Nat) (t : Table) (j : Nat) (row : List Value) :
    Except String (List Triple) := do
  let s ← (rowNode base i t j row).toSubject
  let ty ← mkIri? rdfType
  let tIri ← mkIri? (tableIri base t)
  let mut out : List Triple := [Triple.mk s ty (.iri tIri)]
  for (c, v) in t.columns.zip row do
    match naturalRVal v with
    | none => pure ()
    | some r =>
      let p ← mkIri? (literalPropIri base t c.name)
      let o ← literalTerm r
      out := out ++ [Triple.mk s p o]
  for fk in t.foreignKeys do
    let vals := fk.cols.map (cellOf t row)
    if vals.any (· == .null) then continue
    let some (ri, rt) := tableIndex db fk.refTable | throw s!"no table {fk.refTable}"
    match findReferenced rt fk.refCols vals with
    | none => throw s!"{t.name}: foreign key {fk.cols} has no referenced row in {rt.name}"
    | some (rj, rrow) =>
      let o ← (rowNode base ri rt rj rrow).toSubject
      let p ← mkIri? (referencePropIri base t fk)
      out := out ++ [Triple.mk s p o.toTerm]
  pure out

/-- The direct graph of a database (§4.1): the union of the row triples of
    every row of every table. -/
def directGraph (base : String) (db : Database) : Except String Graph := do
  let mut g : Graph := []
  for (t, i) in db.tables.zipIdx do
    for (row, j) in t.rows.zipIdx do
      let ts ← rowTriples base db i t j row
      g := g ++ ts
  pure g

/-! ## Build-time checks: the DM 2012 §2 example -/

private def example2 : Except String Database := runScript
  "CREATE TABLE \"Addresses\" (\"ID\" INT, PRIMARY KEY(\"ID\"), \"city\" VARCHAR(30), \"state\" CHAR(2));
   CREATE TABLE \"People\" (\"ID\" INT, PRIMARY KEY(\"ID\"), \"fname\" VARCHAR(30), \"addr\" INT,
     FOREIGN KEY(\"addr\") REFERENCES \"Addresses\"(\"ID\"));
   INSERT INTO \"Addresses\" (\"ID\", \"city\", \"state\") VALUES (18, 'Cambridge', 'MA');
   INSERT INTO \"People\" (\"ID\", \"fname\", \"addr\") VALUES (7, 'Bob', 18);
   INSERT INTO \"People\" (\"ID\", \"fname\", \"addr\") VALUES (8, 'Sue', NULL);"

-- 4 Addresses triples, 4 for Bob (type, ID, fname, addr) + 1 reference, 3 for Sue.
#guard match example2.bind (directGraph "http://foo.example/DB/") with
  | .ok g => g.length == 12
  | .error _ => false

end L4Factoidal.RDB2RDF.DM2012
