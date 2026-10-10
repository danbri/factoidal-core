/-
L4Factoidal.RML.Record — one logical iteration of a logical source, and
the values a reference expression selects from it.

Spec: RML-Core, "Defining Iterables and Logical Sources" (a logical
iteration is an item the iterable produces) and "Generating values with
expressions" (an expression evaluates on a logical iteration to a list
of values); RML-IO-Registry for the reference formulations.

## One type for every source kind

RML-Core evaluates the same term maps whatever the source: a JSON
object, a CSV row, an XML element. What differs is how a reference
expression is READ against the iteration, so the record is a sum with
one reader per form and everything downstream asks only
`Record.values`.

* `json`  — a JSON value; the expression is a JSONPath (`RML.JsonPath`).
  A value keeps the datatype JSON gives it: `10` is an `xsd:integer`.
* `table` — a CSV row, or a row of query results: column names bound to
  values. The expression is a column name. Absent and NULL columns are
  simply not in the list, which is how a reference to them selects
  nothing.
* `xml`   — an element, with the document it sits in (XPath's `..` and
  `//` need the whole tree) and the namespace declarations in scope for
  the expression; the expression is XPath 1.0 (`XPath.Eval`).
-/
import L4Factoidal.RML.Value
import L4Factoidal.RML.JsonPath
import L4Factoidal.RML.Error
import L4Factoidal.XPath.Eval

namespace L4Factoidal.RML

open L4Factoidal.JSON
open L4Factoidal.XPath.Full

inductive Record where
  | json  (j : Json)
  | table (cells : List (String × RVal))
  | xml   (doc : Doc) (item : Item) (ns : List (String × String))

instance : Inhabited Record := ⟨.json .null⟩

/-- A table row from plain string cells. -/
def Record.ofCells (cells : List (String × String)) : Record :=
  .table (cells.map (fun (k, v) => (k, ({ lexical := v } : RVal))))

private def dataErr (clause msg : String) : RmlError := RmlError.data "" clause msg

/-- The values a JSONPath selects from a JSON value, and the errors.

    A reference selecting SEVERAL values is not an error: RML says a term
    map generates one term per value. A reference that selects a JSON
    ARRAY or OBJECT is: it denotes no value, and RML-Core's term
    generation rules need a value to build a term from. The corpus has
    this case (`RMLTC0025b`: `$.amounts` where `$.amounts[*]` was meant)
    and expects the mapping to be rejected. `null` selects nothing, as
    RML-Core's "Empty" does (`RMLTC0013a`). -/
def jsonValuesE (rec' : Json) (r : String) : List RVal × List RmlError :=
  (evalPath r rec').foldl (fun (acc : List RVal × List RmlError) j =>
    match j with
    | .array _ | .object _ =>
        (acc.1, acc.2 ++ [dataErr "RML-Core, Generated RDF Term of a Term Map: reference value"
          s!"reference '{r}' selects a JSON array or object, not a value"])
    | _ =>
        match rvalOf j with
        | some v => (acc.1 ++ [v], acc.2)
        | none   => acc) ([], [])

/-- The values an XPath expression selects, relative to an element.
    A node-set contributes the string value of each node, in document
    order; a string, number or boolean contributes itself. An expression
    the XPath engine cannot read is an error, not an empty node-set. -/
def xmlValuesE (doc : Doc) (item : Item) (ns : List (String × String)) (expr : String)
    : List RVal × List RmlError :=
  match evalText { doc := doc, item := item, nsctx := ns } expr with
  | none =>
      ([], [dataErr "RML-IO-Registry, XPath reference formulation"
              s!"'{expr}' is not an XPath expression this engine can evaluate"])
  | some (.nodes its) => (its.map (fun i => ({ lexical := i.stringValue } : RVal)), [])
  | some (.frag _) => ([], [])
  | some v => ([({ lexical := v.toStr } : RVal)], [])

/-- The values a reference expression selects from a record, and the data
    errors met. -/
def Record.values (r : Record) (expr : String) : List RVal × List RmlError :=
  match r with
  | .json j => jsonValuesE j expr
  | .table cells =>
      (((cells.find? (fun c => c.1 == expr)).map (fun c => [c.2])).getD [], [])
  | .xml doc item ns => xmlValuesE doc item ns expr

/-! ## Build-time checks -/

private def person : Json :=
  .object [("fname", .string "Bob"), ("n", .number "7"),
           ("amounts", .array [.number "30", .number "40"]),
           ("nick", .null)]

#guard ((Record.json person).values "$.fname").1 == [{ lexical := "Bob" }]
#guard ((Record.json person).values "$.fname").2.isEmpty
#guard ((Record.json person).values "$.n").1 ==
       [{ lexical := "7", natural := some (xsdNs ++ "integer") }]
#guard ((Record.json person).values "$.amounts[*]").1.length == 2
#guard ((Record.json person).values "$.amounts").2.length == 1
#guard ((Record.json person).values "$.nick").1.isEmpty
#guard ((Record.json person).values "$.nick").2.isEmpty
#guard ((Record.json person).values "$.absent").1.isEmpty
#guard ((Record.json person).values "$.absent").2.isEmpty
-- A row: a present column, an absent one, the first of two equal names.
#guard ((Record.ofCells [("id", "1"), ("name", "A")]).values "name").1 == [{ lexical := "A" }]
#guard ((Record.ofCells [("id", "1")]).values "name").1.isEmpty
#guard ((Record.ofCells [("id", "1"), ("id", "2")]).values "id").1 == [{ lexical := "1" }]

end L4Factoidal.RML
