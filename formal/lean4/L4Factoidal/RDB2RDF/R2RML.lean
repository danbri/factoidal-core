/-
L4Factoidal.RDB2RDF.R2RML — R2RML 2012 over the RML evaluator and the SQL
subset in Lean.

Spec: R2RML: RDB to RDF Mapping Language, W3C Recommendation 27 September
2012 (https://www.w3.org/TR/2012/REC-r2rml-20120927/). Design record:
`docs/designissues/2026-11-01-r2rml-and-direct-mapping.md` §2.

An R2RML mapping graph is read into the `RML.Model` by a term table
(`toRmlGraph`), then validated and evaluated by `RML.Run`, `RML.Validate`
and `RML.Eval`. There is no second evaluator. The R2RML 2012 parts that
RML-Core does not have are stated here, each with its section:

* §5 logical tables: `rr:tableName t` is the query `SELECT * FROM t`
  (§5.1); `rr:sqlQuery q` is `q` (§5.2). Both become an RML logical source
  with the reference formulation `rml:SQL2008Query` and the query text as
  the iterator. The rows come from `SQL.runQuery` (`sqlSourceTable`), so
  the type of each result column is a Lean decision.
* §5.3 `rr:sqlVersion`: the IRI must be `rr:SQL2008` or one of the
  identifiers that the RDB2RDF working group listed for other SQL
  versions; any other IRI rejects the mapping.
* §5 duplicate column names: a logical table whose effective SQL query
  has two columns with the same name is an error.
* §6 column names are SQL identifiers (SQL:2008 Part 2 §5.2): a
  delimited identifier `"Name"` keeps its case, a regular identifier is
  folded to upper case. `rr:column`, `rr:child`, `rr:parent` and the
  references of `rr:template` are rewritten to the normal form, which
  is the name `SQL.runQuery` gives the result column.
* §7.3 `rr:inverseExpression` is an optimisation hint; it has no effect
  on the output and is dropped.
* §10.2 natural RDF literals: each non-NULL cell is the record value
  `R2RML2012.naturalRVal` gives; NULL has no value, so a term map that
  references it generates nothing (§7.4, §11).

Tracking: https://github.com/danbri/factoidal/issues/1165.
-/
import L4Factoidal.RDB2RDF.NaturalLiteral
import L4Factoidal.RML.Run

namespace L4Factoidal.RDB2RDF.R2RML2012

open L4Factoidal.RDF
open L4Factoidal.SQL
open L4Factoidal.RML

def rrNs : String := "http://www.w3.org/ns/r2rml#"
def rr (l : String) : String := rrNs ++ l

/-- The reference formulation of a logical table in the RML model. -/
def sqlQueryIri : String := rmlNs ++ "SQL2008Query"

/-- The SQL version identifiers R2RML 2012 §5.3 accepts: `rr:SQL2008`, and
    the list the RDB2RDF working group kept for other versions
    (http://www.w3.org/2001/sw/wiki/RDB2RDF/SQL_Version_IRIs). -/
def knownSqlVersions : List String :=
  ["SQL2008", "Oracle", "MySQL", "MSSQLServer", "HSQLDB", "PostgreSQL", "DB2",
   "Informix", "Ingres", "Progress", "SybaseASE", "SybaseSQLAnywhere",
   "Virtuoso", "Firebird"].map rr

/-! ## Identifiers and templates -/

/-- The normal form of a SQL identifier (SQL:2008 Part 2 §5.2): a delimited
    identifier without its quotes (a doubled quote is one quote), a regular
    identifier in upper case. -/
def normIdent (s : String) : String :=
  if s.length ≥ 2 && s.startsWith "\"" && s.endsWith "\"" then
    ((s.drop 1).dropEnd 1).toString.replace "\"\"" "\""
  else s.toUpper

/-- Escape the characters an RML template escapes: `\`, `{` and `}`. -/
def escTemplate (s : String) : String :=
  s.foldl (fun acc c =>
    if c == '\\' || c == '{' || c == '}' then (acc.push '\\').push c else acc.push c) ""

/-- An R2RML template with each column reference in normal form. A template
    that is not valid stays as it is, so that `RML.Validate` reports it. -/
def normTemplate (raw : String) : String :=
  match parseTemplateStrict raw with
  | .error _ => raw
  | .ok segs => String.join (segs.map fun
      | .literal l => escTemplate l
      | .reference r => "{" ++ escTemplate (normIdent r) ++ "}")

/-! ## The term table -/

def mkIriE (s : String) : Option WfIri :=
  if h : isIri s then some ⟨s, h⟩ else none

/-- An `rr:` IRI as the `rml:` IRI with the same local name (`rr:IRI`,
    `rr:Literal`, `rr:BlankNode`, `rr:defaultGraph`, `rr:TriplesMap`). -/
def renameIri (i : WfIri) : WfIri :=
  if i.val.startsWith rrNs then
    let l := (i.val.drop rrNs.length).toString
    let local' := if l == "column" then "reference"
      else if l == "logicalTable" then "logicalSource" else l
    (mkIriE (rmlNs ++ local')).getD i
  else i

def litMap (f : String → String) : Term → Term
  | .literal l => .literal (Literal.string (f l.val.lexicalForm))
  | t => t

def renameTerm : Term → Term
  | .iri i => .iri (renameIri i)
  | t => t

/-- The query text of a logical table, with a trailing `;` removed (a
    query is one statement). -/
def stripQuery (q : String) : String :=
  let t := q.trimAscii.toString
  if t.endsWith ";" then (t.dropEnd 1).toString else t

/-- The effective SQL query of a logical table (R2RML 2012 §5): for
    `rr:tableName t` the query `SELECT * FROM t` (§5.1), for `rr:sqlQuery q`
    the query `q` (§5.2). -/
def effectiveQuery (local' v : String) : String :=
  if local' == "tableName" then "SELECT * FROM " ++ v else stripQuery v

/-- One triple of an R2RML mapping graph as the triples of the RML mapping
    graph. -/
def translateTriple (t : Triple) : List Triple :=
  let p := t.p.val
  if !p.startsWith rrNs then [{ t with o := renameTerm t.o }]
  else
    let l := (p.drop rrNs.length).toString
    let mk := fun (q : String) (o : Term) =>
      match mkIriE q with
      | some qi => [({ s := t.s, p := qi, o := o } : Triple)]
      | none => []
    let lit := fun (o : Term) => match o with
      | .literal lv => some lv.val.lexicalForm
      | _ => none
    if l == "sqlVersion" || l == "inverseExpression" then []
    else if l == "tableName" || l == "sqlQuery" then
      match lit t.o with
      | some v =>
          let q := effectiveQuery l v
          mk (rmlNs ++ "iterator") (.literal (Literal.string q)) ++
          (match mkIriE sqlQueryIri with
           | some f => mk (rmlNs ++ "referenceFormulation") (.iri f)
           | none => [])
      | none => mk (rmlNs ++ "iterator") t.o
    else if l == "column" || l == "child" || l == "parent" then
      mk (renameIri t.p).val (litMap normIdent t.o)
    else if l == "template" then
      mk (renameIri t.p).val (litMap normTemplate t.o)
    else mk (renameIri t.p).val (renameTerm t.o)

/-- The RML mapping graph of an R2RML mapping graph. -/
def toRmlGraph (g : Graph) : Graph := g.flatMap translateTriple

/-! ## Checks R2RML 2012 adds -/

def rdfTypeIri : String := "http://www.w3.org/1999/02/22-rdf-syntax-ns#type"

/-- The triples map nodes of an R2RML mapping graph. -/
def r2rmlTriplesMaps (g : Graph) : List String :=
  ((g.filter (fun t =>
      (t.p.val == rdfTypeIri && (match t.o with | .iri i => i.val == rr "TriplesMap" | _ => false)) ||
      t.p.val == rr "logicalTable" || t.p.val == rr "subjectMap" ||
      t.p.val == rr "subject" || t.p.val == rr "predicateObjectMap")).map
    (fun t => subjKey t.s)).foldl (fun acc n => if acc.contains n then acc else acc ++ [n]) []

def mapErr (site clause msg : String) : RmlError := RmlError.mapping site clause msg

/-- A valid language tag for `rr:language` (R2RML 2012 §7.6; RFC 5646
    §2.2.9 "valid"): well-formed (`RDF.isWellFormedLangTag`), and its primary
    language subtag is not one the IANA Language Subtag Registry cannot hold:
    four letters are reserved (RFC 5646 §2.2.1 rule 3) and no subtag of five
    to eight letters is registered. The other subtags are not checked against
    the registry: https://github.com/danbri/factoidal/issues/1221. -/
def validLanguageTag (tag : String) : Bool :=
  isWellFormedLangTag tag &&
  (let first := (tag.splitOn "-").headD ""
   !(first.length ≥ 4 && first.length ≤ 8 && first.all Char.isAlpha))

/-- The R2RML 2012 MUST clauses that the RML-Core validator does not
    check: one logical table per triples map (§6), one of `rr:tableName`
    and `rr:sqlQuery` per logical table (§5), a known SQL version
    identifier (§5.3), and a valid `rr:language` (§7.6). -/
def r2rmlErrors (g : Graph) : List RmlError :=
  (g.filterMap (fun t =>
    if t.p.val != rr "language" then none
    else match t.o with
      | .literal l =>
          if validLanguageTag l.val.lexicalForm then none
          else some (mapErr (subjKey t.s) "R2RML 2012 §7.6, Language Tags"
            s!"'{l.val.lexicalForm}' is not a valid language tag")
      | _ => some (mapErr (subjKey t.s) "R2RML 2012 §7.6, Language Tags"
               "rr:language must be a literal"))) ++
  (r2rmlTriplesMaps g).flatMap (fun tm =>
    match nodesOf g tm (rr "logicalTable") with
    | [lt] =>
        let n := (objectsOf g lt (rr "tableName")).length + (objectsOf g lt (rr "sqlQuery")).length
        (if n != 1 then
          [mapErr tm "R2RML 2012 §5, Defining a Logical Table"
            "a logical table has exactly one rr:tableName or rr:sqlQuery"]
         else []) ++
        (objectsOf g lt (rr "sqlVersion")).filterMap (fun v =>
          match v with
          | .iri i => if knownSqlVersions.contains i.val then none
              else some (mapErr tm "R2RML 2012 §5.3, R2RML Views"
                s!"{i.val} is not a SQL version identifier")
          | _ => some (mapErr tm "R2RML 2012 §5.3, R2RML Views" "rr:sqlVersion must be an IRI"))
    | [] => [mapErr tm "R2RML 2012 §6, Mapping Logical Tables to RDF with Triples Maps"
               "a triples map has exactly one rr:logicalTable, and this one has none"]
    | _ => [mapErr tm "R2RML 2012 §6, Mapping Logical Tables to RDF with Triples Maps"
              "a triples map has exactly one rr:logicalTable, and this one has more than one"])

/-! ## Logical tables as RML sources -/

/-- Does a list of names have a repeated element? -/
def hasDup : List String → Bool
  | [] => false
  | x :: xs => xs.contains x || hasDup xs

/-- The logical rows of a logical table (R2RML 2012 §5): the result of its
    effective SQL query, each row a record whose cells are the natural RDF
    literals (§10.2) of its non-NULL values. -/
def sqlRecords (db : Database) (ls : LogicalSource) : Except RmlError (List Record) :=
  match ls.iterator with
  | none => .error (RmlError.source "" "R2RML 2012 §5, Defining a Logical Table"
      "the logical table has no SQL query")
  | some q =>
      match runQuery db q with
      | .error e => .error (RmlError.source q "R2RML 2012 §5, effective SQL query" e)
      | .ok rs =>
          let names := rs.columns.filterMap (·.1)
          if hasDup names then
            .error (RmlError.source q "R2RML 2012 §5, Defining a Logical Table"
              "the effective SQL query has two columns with the same name")
          else
            .ok (rs.rows.map fun row =>
              let cells := (rs.columns.zip row).filterMap fun ((n?, _), v) =>
                n?.bind fun n => (naturalRVal v).map (n, ·)
              Record.table cells names)

/-- The source table of a mapping over a database. -/
def sqlSourceTable (db : Database) (m : Mapping) : SourceTable :=
  m.foldl (fun (acc : SourceTable) tm =>
    if tm.source.isAbsent || acc.any (fun e => e.1 == tm.source) then acc
    else acc ++ [(tm.source, sqlRecords db tm.source)]) []

/-- Run an R2RML 2012 mapping graph over a database. `base` is the base IRI
    of §11 that resolves relative IRIs. A rejected run has no quads. -/
def runR2RML (g : Graph) (db : Database) (base : String) : EvalResult :=
  let errs := r2rmlErrors g
  if !errs.isEmpty then { quads := [], errors := errs }
  else runMappingGraphWith (toRmlGraph g) (some base) (sqlSourceTable db)

/-! ## Build-time checks -/

#guard normIdent "\"Name\"" == "Name"
#guard normIdent "Name" == "NAME"
#guard normIdent "\"a\"\"b\"" == "a\"b"
#guard normTemplate "http://example.com/{\"ID\"}/{Name}" == "http://example.com/{ID}/{NAME}"
#guard normTemplate "\\{\\{ {\"ISO 3166\"} \\}\\}" == "\\{\\{ {ISO 3166} \\}\\}"
#guard stripQuery "  SELECT 1 FROM t;\n " == "SELECT 1 FROM t"
#guard hasDup ["ID", "Name", "ID"]
#guard validLanguageTag "en" && validLanguageTag "es" && validLanguageTag "en-US"
#guard !validLanguageTag "english" && !validLanguageTag "spanish" && !validLanguageTag "abcd"
-- Expected failure, https://github.com/danbri/factoidal/issues/1221: `zz` is
-- not a registered language subtag, so `zz-QQ` is not valid. This guard
-- states the current answer; it fails when the registry check lands, and is
-- then flipped to `!validLanguageTag "zz-QQ"`.
#guard validLanguageTag "zz-QQ"
#guard !hasDup ["ID", "Name"]

end L4Factoidal.RDB2RDF.R2RML2012
