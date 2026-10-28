/-
L4Factoidal.EXPath.Hook — the one entry point through which the XPath
4.0 evaluator finds the EXPath function libraries: `XPath4.Ext`
asks `expathLookup` for any function name outside the `fn:` tables.
-/
import L4Factoidal.EXPath.Binary.Lib

namespace L4Factoidal.EXPath

open L4Factoidal.XPath4

/-- The implementation of an EXPath Binary 4.0 or File 4.0 function. -/
def expathLookup (q : QN) : Option LibFn :=
  if q.uri == Binary.nsBIN then Binary.binTable.lookup q.loc
  else none

end L4Factoidal.EXPath
