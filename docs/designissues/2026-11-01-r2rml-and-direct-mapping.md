# R2RML and the Direct Mapping in Lean: design record

Date: 2026-11-01. Tracking: https://github.com/danbri/factoidal/issues/1165
(spec track A, item 5). Specifications:

- R2RML: RDB to RDF Mapping Language, W3C Recommendation 27 September 2012
  (https://www.w3.org/TR/2012/REC-r2rml-20120927/). Below: "R2RML 2012".
- A Direct Mapping of Relational Data to RDF, W3C Recommendation 27 September
  2012 (https://www.w3.org/TR/2012/REC-rdb-direct-mapping-20120927/). Below:
  "DM 2012".
- Tests: the W3C RDB2RDF test cases, Editor's Draft 24 July 2012, vendored in
  `third_party/testing/rdb2rdf-tests/` (provenance:
  `third_party/testing/rdb2rdf-tests-PROVENANCE.md`): 26 databases, 24 Direct
  Mapping cases, 63 R2RML cases (14 of them must be rejected).

## 1. Decision: an in-engine SQL subset in Lean, no host database

Each test database is a SQL script (`create.sql`). The R2RML cases also send
SQL queries (`rr:sqlQuery`) to the database. The options were a host database
(SQLite or PostgreSQL through a seam, as `RML.FileAccess.sparql` is a seam for
SPARQL) or a SQL subset in Lean.

We take the SQL subset in Lean. Reasons:

1. Iron rule 7 (decisions in Lean). The values that R2RML 2012 §10.2 maps to
   RDF literals (the natural RDF literal of a SQL value) depend on the SQL
   datatype of each column of the query result. A host database decides those
   types, and each host decides them differently (SQLite has no `DATE`, no
   `BOOLEAN` and no fixed column types). With the subset in Lean, the type of
   each result column is a Lean function of the schema and the query.
2. The corpus is small. The 26 scripts use only: `CREATE TABLE` (column types
   `INTEGER`/`INT`, `VARCHAR(n)`, `CHAR(n)`, `REAL`, `FLOAT`, `DATE`,
   `TIMESTAMP`, `BOOLEAN`, `VARBINARY(n)`; column constraints `PRIMARY KEY`;
   table constraints `PRIMARY KEY (...)`, `UNIQUE (...)`,
   `FOREIGN KEY (...) REFERENCES t (...)`), `ALTER TABLE ... ADD FOREIGN KEY`,
   and `INSERT INTO t [(cols)] VALUES (...)` with integer, decimal, string,
   `X'..'` binary, `TRUE`/`FALSE` and `NULL` values. The 22 `rr:sqlQuery`
   texts use only: `SELECT` lists of columns, `t.col`, `*`, `t.*`, `AS`
   aliases, string concatenation `||`, a simple `CASE`, `COUNT(col)` with
   `GROUP BY`; `FROM` with one or more tables (cross product); `WHERE` with
   `=`, `<` and `AND`.
3. The RML suite that is vendored already (`third_party/testing/rml`) has 60
   PostgreSQL, MySQL and SQL Server cases with `resource.sql` scripts. Today
   `RML/Open.lean` refuses every `rml:SQL2008Table` and `rml:SQL2008Query`
   source. The same SQL subset can give those cases their rows (a later step).
4. A host database stays possible. The SQL engine is behind one function
   type, `Database → String → Except SqlError ResultSet`, as SPARQL is behind
   `FileAccess.sparql`. A host engine can replace it; then its result is an
   assumption of the run, not a Lean decision.

Not in the subset, and refused with an error that names the SQL feature: every
statement and expression form that the corpus does not use (outer joins,
subqueries, `UPDATE`, `DELETE`, functions other than `COUNT`). A refusal is a
failure of the case, not an exclusion.

Identifiers follow SQL:2008 Part 2 §5.2: a regular identifier is folded to
upper case; a delimited identifier (`"Name"`) keeps its case. R2RML 2012 §6
uses these rules for `rr:column`, `rr:tableName` and template references
(tests `R2RMLTC0002f`, `R2RMLTC0002g`). Where the expected output of a case
needs another folding (PostgreSQL folds to lower case), the case decides,
and this record is updated with the case name.

## 2. Modules

- `L4Factoidal/SQL/Syntax.lean`: SQL values (`null`, integer, exact numeric,
  approximate numeric, character string, boolean, date, timestamp, binary),
  SQL datatypes, the lexer and the parser of the subset (statements and
  queries). Both are loops or fuel-bounded recursions.
- `L4Factoidal/SQL/Database.lean`: tables with columns, keys and rows; running
  a script; evaluating a query to a result set with typed columns.
- `L4Factoidal/RDB2RDF/NaturalLiteral.lean`: R2RML 2012 §10.2, the natural RDF
  literal and the natural RDF datatype of a SQL value, with the canonical
  lexical forms of XSD 1.1. DM 2012 §2.3 uses the same mapping.
- `L4Factoidal/RDB2RDF/DirectMapping.lean`: DM 2012 §2 to §4: row nodes (IRI
  when the table has a primary key, a blank node when it does not), the table
  IRI, literal triples and reference triples, with the percent-encoding of
  §2.2.
- `L4Factoidal/RDB2RDF/R2RML.lean` (next step): read an R2RML mapping graph
  into the existing `RML.Model` (the `rr:` to `rml:` term table of
  `docs/designissues/2026-07-05-rml-program-plan.md` § "R2RML compatibility
  is not a namespace swap"), with the logical table as a source whose
  records are the SQL result rows (`RML.Record.table`). The term maps, the
  templates, the joins and the graph maps run through `RML.Eval`, not a
  second evaluator. R2RML 2012 differences from RML-Core (the default term
  types, `rr:inverseExpression`, the SQL equality of join conditions, the
  natural literals of §10.2) are parameters of that translation, each with
  the section it comes from.
- `Harness/Rdb2RdfRun.lean`, `lake exe l4rdb2rdf`, `tests/rdb2rdf/run.sh`: read
  the 26 manifests, run each Direct Mapping and R2RML case, compare with the
  expected graph or dataset by `Graph.isomorphicOutcome` (the three-way
  result). Print "N pass, M fail (out of T)".

## 3. Theorems that connect the specifications (version-named)

1. `dm2012_as_r2rml2012`: for a database whose tables have primary keys, the
   Direct Mapping graph equals the R2RML result of the default mapping that
   R2RML 2012 §1 and DM 2012 §1 describe (one triples map per table,
   subject template from the primary key, one predicate-object map per column,
   one reference object map per foreign key). Order: after the R2RML step.
2. `dm2012_literal_natural`: every literal of a Direct Mapping graph is the
   natural RDF literal of R2RML 2012 §10.2 of a non-NULL cell of its row (DM
   2012 §2.3 refers to R2RML for this mapping).
3. `dm2012_row_node_injective`: two rows of one table with primary keys give
   the same row node only when their key values are equal (the §2.2
   percent-encoding is injective).
4. `sql_select_star`: `SELECT * FROM t` gives the rows of `t` in insertion
   order, so the Direct Mapping of a table and the R2RML logical table
   `rr:tableName t` read the same rows (R2RML 2012 §5.1).

## 4. Status (2026-11-01)

Step 1 is done: `bash tests/rdb2rdf/run.sh` gives Direct Mapping 24 pass, 0
fail (out of 24). Theorems landed: `dm2012_rowNode_bnode_iff`,
`dm2012_rowNode_iri_prefix` (`RDB2RDF/DirectMappingTheorems.lean`). Approximate
numerics are held as the exact decimal of their literal; every double of the
corpus (`80.25`, `1.65`, `30`, ...) has the canonical form that the expected
graphs give.

Step 2 is done (2026-11-01): `RDB2RDF/R2RML.lean` reads an R2RML mapping
graph into the RML model by a term table (`toRmlGraph`: `rr:` to `rml:`,
`rr:column` to `rml:reference`, `rr:logicalTable` to `rml:logicalSource`,
the logical table as the iterator query under `rml:SQL2008Query`, SQL
identifiers in normal form in `rr:column`, `rr:child`, `rr:parent` and the
template references; `rr:sqlVersion` and `rr:inverseExpression` dropped
after the checks). The RML validator and evaluator run it unchanged; the
records are `sqlRecords` rows. R2RML-only checks: one logical table per
triples map, one of `rr:tableName`/`rr:sqlQuery`, a known SQL version
identifier, no duplicate result column names, and a valid `rr:language`
(well-formed, with a primary subtag the IANA registry can hold; the other
subtags are not checked against the registry:
https://github.com/danbri/factoidal/issues/1221). `bash tests/rdb2rdf/run.sh`:
R2RML 63 pass, 0 fail (out of 63). Theorems landed
(`RDB2RDF/R2RMLTheorems.lean`): `r2rml2012_cell_natural`,
`r2rml2012_null_no_value`, `r2rml2012_tableName_query`,
`r2rml2012_rejected_no_quads`. Open: `dm2012_as_r2rml2012`, section 3
item 1 (https://github.com/danbri/factoidal/issues/1222); items 3 and 4 of
section 3 are not stated yet.

## 5. Order of work

1. This record, the vendored suite, the SQL subset, the natural literals, the
   Direct Mapping and its runner (24 cases).
2. R2RML over `RML.Eval` (63 cases), the theorems of section 3.
3. The RML suite's SQL cases through the same SQL subset.
4. The W3C completeness ledger rows and the changelog entry for each step.
