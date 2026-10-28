/-
L4Factoidal.XPath4.RecordTypes — the named record types of F&O 4.0
(`fn:dateTime-record`, `fn:uri-structure-record`, ...), as the source text
of an equivalent `record(...)` type.

Generated from the `fos:record-type` elements of
`specifications/xpath-functions-40/src/function-catalog.xml` of
https://github.com/qt4cg/qtspecs at commit
b4723ff52fd9d4fabf2b4cd33bd44f21939c512c. Two changes: a field whose type
allows the empty sequence is optional (`name?`), and a field whose type is a
function type is written `fn(*)` (the record's function fields are
matched, and coerced, as function items of any signature).
-/
namespace L4Factoidal.XPath4

def recordTypesRaw : List (String × String) := [
  ("uri-structure-record", "record(\"uri\"? as xs:string?, \"scheme\"? as xs:string?, \"absolute\"? as xs:boolean?, \"hierarchical\"? as xs:boolean?, \"authority\"? as xs:string?, \"userinfo\"? as xs:string?, \"host\"? as xs:string?, \"port\"? as xs:integer?, \"path\"? as xs:string?, \"query\"? as xs:string?, \"fragment\"? as xs:string?, \"path-segments\"? as xs:string*, \"query-parameters\"? as map(xs:string, xs:string*)?, \"filepath\"? as xs:string?)"),
  ("element-conversion-plan-record", "record(\"child\"? as xs:string?, \"type\"? as enum('integer', 'decimal', 'double', 'boolean', 'string')?)"),
  ("attribute-conversion-plan-record", "record(\"type\"? as enum('integer', 'decimal', 'double', 'boolean', 'string', 'skip')?)"),
  ("location-record", "record(\"system-id\"? as xs:anyURI?, \"public-id\"? as xs:string?, \"line-number\"? as xs:integer?, \"column-number\"? as xs:integer?)"),
  ("schema-type-record", "record(\"name\"? as xs:QName?, \"is-simple\" as xs:boolean, \"base-type\" as fn(*), \"primitive-type\"? as fn(*)?, \"members\"? as fn(*)?, \"simple-content-type\"? as fn(*)?, \"matches\"? as fn(*)?, \"constructor\"? as fn(*)?, \"validate\" as fn(*), \"valid\" as fn(*))"),
  ("compiled-regex-record", "record(\"pattern\" as xs:string, \"flags\" as xs:string, \"matches\" as fn(*), \"tokenize\" as fn(*), \"replace\" as fn(*), \"analyze-string\" as fn(*), \"matching-segments\" as fn(*))"),
  ("matching-segment-record", "record(\"substring\" as xs:string, \"position\" as xs:integer, \"groups\" as map((xs:integer | xs:string), map(*)))"),
  ("captured-group-record", "record(\"value\" as xs:string, \"position\" as xs:integer, \"nr\" as xs:integer, \"name\"? as xs:string?)"),
  ("load-xquery-module-record", "record(\"variables\" as map(xs:QName, item()*), \"functions\" as map(xs:QName, map(xs:integer, fn(*))))"),
  ("dateTime-record", "record(\"year\"? as xs:integer?, \"month\"? as xs:integer?, \"day\"? as xs:integer?, \"hours\"? as xs:integer?, \"minutes\"? as xs:integer?, \"seconds\"? as xs:decimal?, \"timezone\"? as xs:dayTimeDuration?)"),
  ("parsed-csv-structure-record", "record(\"columns\"? as xs:string*, \"column-index\"? as map(xs:string,xs:integer)?, \"rows\"? as array(xs:string)*, \"get\" as fn(*))"),
  ("random-number-generator-record", "record(\"number\" as xs:double, \"next\" as fn(*), \"permute\" as fn(*), \"take\" as fn(*))"),
  ("division-record", "record(\"quotient\" as xs:decimal, \"remainder\" as xs:decimal)"),
  ("sort-key-record", "record(\"key\"? as fn(*)?, \"collation\"? as xs:string?, \"order\"? as enum('ascending', 'descending')?)"),
  ("array-sort-key-record", "record(\"key\"? as fn(*)?, \"collation\"? as xs:string?, \"order\"? as enum('ascending', 'descending')?)"),
  ("validation-result-record", "record(\"is-valid\" as xs:boolean, \"typed-node\"? as xnode()?, \"error-details\"? as map(*)*)")
]

end L4Factoidal.XPath4
