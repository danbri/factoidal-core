/- Static namespaces of fn:parse-QName function items, F&O 4.0 §10.1.2.
   https://qt4cg.org/specifications/xpath-functions-40/Overview.html#func-parse-QName
   Executable regressions, not equivalence proofs.
-/
import L4Factoidal.XQuery4.LoadModule

namespace L4Factoidal.XPath4.QNameContextTests

open L4Factoidal.XPath4 L4Factoidal.XQuery4

private def result (src : String) : String :=
  let env : Env := {}
  match evalQuery src { env with host := loadModuleHost env env.host } with
  | .ok xs => showSeq xs
  | .error e => e.code

private def loaded (maker body : String) : String :=
  "declare namespace X = 'urn:x'; declare namespace x = 'urn:caller'; " ++
  "declare namespace y = 'urn:caller-only'; " ++
  "let $module := load-xquery-module('urn:x', {'content': '" ++
  "module namespace x = \"urn:x\"; declare default element namespace \"urn:default\"; " ++
  "declare variable $x:f := " ++ maker ++ ";'}) " ++
  "let $f := $module?variables?#X:f return " ++ body

private def named := "fn:parse-QName#1"
private def looked := "function-lookup(QName(\"http://www.w3.org/2005/xpath-functions\", \"parse-QName\"), 1)"
private def placeholder :=  "fn:parse-QName(?)"
private def summary := "$f(\"x:xxx\") ! (prefix-from-QName(.), namespace-uri-from-QName(.), local-name-from-QName(.))"

-- Creation-site module prefixes override a conflicting caller prefix.
#guard result (loaded named summary) == "x urn:x xxx"
#guard result (loaded looked summary) == "x urn:x xxx"
#guard result (loaded placeholder summary) == "x urn:x xxx"
-- The caller cannot introduce a prefix absent at creation.
#guard result (loaded named "$f(\"y:xxx\")") == "FONS0004"
#guard result (loaded looked "$f(\"y:xxx\")") == "FONS0004"
#guard result (loaded placeholder "$f(\"y:xxx\")") == "FONS0004"
-- The NCName case is in no namespace regardless of either default namespace.
#guard result (loaded named "namespace-uri-from-QName($f(\"local\"))") == ""
#guard result (loaded looked "namespace-uri-from-QName($f(\"local\"))") == ""
-- Name/arity metadata and ordinary argument/error behavior are preserved.
#guard result (loaded named "function-name($f) eq QName(\"http://www.w3.org/2005/xpath-functions\", \"parse-QName\")") == "true"
#guard result (loaded looked "function-name($f) eq QName(\"http://www.w3.org/2005/xpath-functions\", \"parse-QName\")") == "true"
#guard result (loaded named "function-arity($f)") == "1"
#guard result (loaded looked "function-arity($f)") == "1"
#guard result (loaded named "empty($f(()))") == "true"
#guard result (loaded named "$f(\"bad:name:again\")") == "FOCA0002"
#guard result (loaded named "$f(42)") == "XPTY0004"
-- A raw XPath environment may carry lexical namespace variables. They are
-- captured without the static marker that would admit caller late bindings.
#guard let old : Env := { ns := [("p", "urn:base")], vars := [(nsBindingVar "p", sStr "urn:lexical")] }
       match evalString "parse-QName#1" old with
       | .ok [f] => match apply 10000 { ns := [("p", "urn:caller")] } f [sStr "p:n"] with
         | .ok [.atom ⟨_, .qn q⟩] => q.uri == "urn:lexical"
         | _ => false
       | _ => false

end L4Factoidal.XPath4.QNameContextTests
