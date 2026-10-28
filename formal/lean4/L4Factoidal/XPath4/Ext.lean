/-
L4Factoidal.XPath4.Ext — the Stage 2 function tables, put in front of
the Stage 1 library (`XPath4.Lib`): an entry here replaces the Stage 1
entry of the same name.
-/
import L4Factoidal.XPath4.XmlParse
import L4Factoidal.XPath4.Format
import L4Factoidal.XPath4.Json
import L4Factoidal.XPath4.Regex4
import L4Factoidal.XPath4.Serialize
import L4Factoidal.XPath4.ElemMap
import L4Factoidal.XPath4.Fn4
import L4Factoidal.XPath4.Uri
import L4Factoidal.XPath4.Csv
import L4Factoidal.XPath4.DeepEqual
import L4Factoidal.XPath4.Html
import L4Factoidal.XPath4.Update

namespace L4Factoidal.XPath4

def extTable : List (String × LibFn) :=
  xmlParseTable ++ formatTable ++ jsonTable ++ regexTable ++ serializeTable ++ elemMapTable ++ fn4Table ++
  uriTable ++ csvTable ++ deepEqualTable ++ htmlTable ++ updateTable

/-- Look up a built-in function: the Stage 2 tables first. -/
def libLookupAll (q : QN) : Option LibFn :=
  if q.uri == nsFN then
    match extTable.lookup q.loc with
    | some f => some f
    | none => libLookup q
  else libLookup q

end L4Factoidal.XPath4
