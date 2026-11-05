/-
Selectable feature regressions through the XPath and XQuery entry points.
XPath 4.0 §2.2.1 and §2.4.1; XQuery 4.0 §6.2; F&O 4.0 fn:system-properties,
fn:load-xquery-module, fn:transform and fn:serialize.
These are executable checks, not equivalence proofs.
-/
import L4Factoidal.XQueryUpdate.Query
import L4Factoidal.XSLT4.QtFnTransform
import L4Factoidal.XPath4.UnicodeBridgeTests
import L4Factoidal.XPath4.GenerateTests
import L4Factoidal.XPath4.QNameContextTests

namespace L4Factoidal.XPath4.FeatureTests

open L4Factoidal.XPath4 L4Factoidal.XQuery4

private def configured (name : String) : Env :=
  ({} : Env).restrictFeatures (({} : FeatureSettings).disable name)

private def code (r : M Seq) : String :=
  match r with
  | .ok s => showSeq s
  | .error e => e.code

private def xp (feature src : String) : String := code (evalString src (configured feature))
private def xq (feature src : String) : String := code (evalQuery src (configured feature))
private def upd (feature src : String) : String :=
  code ((·.1) <$> L4Factoidal.XQueryUpdate.evalUpdQuery src (configured feature))

-- Unavailable functions are rejected before evaluation, including dead branches.
#guard xp "fn-invisible-xml" "if (false()) then invisible-xml('a') else 1" == "XPST0017"
#guard xp "fn-invisible-xml" "invisible-xml#1" == "XPST0017"
#guard xp "binary" "Q{http://expath.org/ns/binary}hex('00')" == "XPST0017"
#guard xp "expath-file" "Q{http://expath.org/ns/file}exists('x')" == "XPST0017"
#guard xp "binary" "empty(function-lookup(QName('http://expath.org/ns/binary', 'hex'), 1))" == "true"
#guard xp "fn-invisible-xml" "empty(function-lookup(QName('http://www.w3.org/2005/xpath-functions', 'invisible-xml'), 1))" == "true"
#guard xq "fn-invisible-xml" "declare function local:f() { invisible-xml#1 }; 1" == "XPST0017"
#guard xq "binary" "if (false()) then Q{http://expath.org/ns/binary}hex('00') else 1" == "XPST0017"

-- Restrictions compose without restoring a feature disabled earlier.
#guard let e := (({} : Env).restrictFeatures { binary := false }).restrictFeatures { file := false }
       !e.features.binary && !e.features.file

-- An input tree with a schema type and typed value becomes untyped.
private def typedRec : NRec :=
  { kind := .element
    name := { uri := "", loc := "e" }
    tann := some { uri := nsXS, loc := "integer" }
    tval := some [Atomic.ofInt 42] }
private def typedDoc : Doc := { nodes := #[typedRec] }
private def typedEnv : Env :=
  { docs := #[typedDoc], ctx := some [.node (NodeRef.mk' 0 0)], pos := 1, size := 1 }
#guard code (evalString "data(.) instance of xs:integer" typedEnv) == "true"
#guard code (evalString "data(.) instance of xs:untypedAtomic" (typedEnv.restrictFeatures { typedData := false })) == "true"
#guard code (evalString ". instance of element(*, xs:untyped)" (typedEnv.restrictFeatures { typedData := false })) == "true"

-- The mandatory function signatures retain their specified invocation errors.
#guard xp "fn-load-xquery-module" "load-xquery-module('urn:none')" == "FOQM0006"
#guard xp "fn-load-xquery-module" "load-xquery-module#1('urn:none')" == "FOQM0006"
#guard xp "fn-load-xquery-module" "function-lookup(QName('http://www.w3.org/2005/xpath-functions', 'load-xquery-module'), 1)('urn:none')" == "FOQM0006"
#guard xp "fn-transform-XSLT" "transform(map{})" == "FOXT0004"
#guard xp "fn-transform-XSLT" "transform#1(map{})" == "FOXT0004"
#guard xp "fn-transform-XSLT" "function-lookup(QName('http://www.w3.org/2005/xpath-functions', 'transform'), 1)(map{})" == "FOXT0004"
#guard xp "serialization" "serialize(1)" == "FODC0010"
#guard xp "serialization" "serialize#1(1)" == "FODC0010"
#guard xq "serialization" "declare option output:method 'invalid'; 1" == "1"

#guard xq "schemaImport" "import schema namespace s = 'urn:s'; 1" == "XQST0009"
#guard upd "schemaImport" "import schema namespace s = 'urn:s'; 1" == "XQST0009"
#guard xq "schemaValidation" "if (false()) then validate { <a/> } else 1" == "XQST0075"
#guard upd "schemaValidation" "if (false()) then validate { <a/> } else 1" == "XQST0075"
#guard xp "schemaValidation" "json-to-xml('null', map { 'validate': true() })" == "FOJS0004"
#guard xq "typedData" "<e/> instance of element(*, xs:untyped)" == "true"
#guard xq "typedData" "declare variable $v as element(*, xs:untyped?)+ := <e/>; exists($v/*)" == "false"

#guard xp "schemaImport" "system-properties()?#schema-aware" == "false"
#guard xp "typedData" "system-properties()?#schema-aware" == "false"
#guard xp "typedData" "system-properties()?#accepts-typed-data" == "false"
#guard xp "binary" "system-properties()?#supports-binary-library" == "false"
#guard xp "expath-file" "system-properties()?#supports-file-library" == "false"
#guard xp "fn-invisible-xml" "system-properties()?#supports-invisible-xml" == "false"
#guard xp "fn-transform-XSLT" "system-properties()?#supports-dynamic-xslt" == "false"
#guard xp "fn-load-xquery-module" "system-properties()?#supports-dynamic-xquery" == "false"

-- Retained signatures support references and partial application; only
-- invocation raises the optional-feature error.
#guard xp "fn-transform-XSLT" "transform(?) instance of function(*)" == "true"
#guard xp "fn-transform-XSLT" "transform(?)(map{})" == "FOXT0004"
#guard xp "serialization" "serialize(?) instance of function(*)" == "true"
#guard xp "serialization" "serialize(?)(1)" == "FODC0010"
#guard xp "serialization" "serialize#1 instance of function(*)" == "true"

#guard xp "serialization" "serialize#99" == "XPST0017"
#guard xp "fn-transform-XSLT" "transform#99" == "XPST0017"

-- A disabled function cannot escape through a host hook or a reference.
private def hostEnv : Env :=
  { host := fun _ _ => some (fun _ _ => pure (sStr "host escaped")) }
#guard code (evalString "transform(map{})" (hostEnv.restrictFeatures { transform := false })) == "FOXT0004"
#guard code (evalString "transform#1(map{})" (hostEnv.restrictFeatures { transform := false })) == "FOXT0004"
#guard code (evalString "load-xquery-module#1('urn:none')" (hostEnv.restrictFeatures { loadXQueryModule := false })) == "FOQM0006"
#guard code (eval 100 (hostEnv.restrictFeatures { invisibleXml := false }) (.call { uri := nsFN, loc := "invisible-xml" } [] [])) == "XPST0017"

#guard code (evalString "transform(?)" (hostEnv.restrictFeatures { transform := false })) == "function"
#guard code (evalString "transform(?)(map{})" (hostEnv.restrictFeatures { transform := false })) == "FOXT0004"
#guard code (evalString "serialize(?)" (hostEnv.restrictFeatures { serialization := false })) == "function"
#guard code (evalString "serialize(?)(1)" (hostEnv.restrictFeatures { serialization := false })) == "FODC0010"
#guard code (evalString "serialize#1" (hostEnv.restrictFeatures { serialization := false })) == "function"
#guard code (evalString "serialize#1(1)" (hostEnv.restrictFeatures { serialization := false })) == "FODC0010"

private def xslt2 (src : String) : String :=
  let e := configured "fn-transform-XSLT30"
  let e := { e with host := L4Factoidal.XSLT4.Qt.transformHost e (fun f a => apply 20000 e f a) e.host }
  code (evalString src e)

#guard xslt2 "transform(map { 'delivery-format': 'raw' })" == "FOXT0002"
#guard xslt2 "transform(map { 'xslt-version': 3.0 })" == "FOXT0001"
#guard xslt2 "transform(map { 'static-params': map{} })" == "FOXT0001"
#guard xslt2 "transform(map { 'initial-function': QName('', 'f') })" == "FOXT0001"

#guard xslt2 "transform(map { 'stylesheet-text': '<xsl:stylesheet xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\" version=\"3.0\"/>' })" == "FOXT0001"
#guard xslt2 "transform(map { 'stylesheet-text': '<xsl:stylesheet xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\" version=\"4.0\"/>' })" == "FOXT0001"

#guard xslt2 "exists(transform(map { 'stylesheet-text': '<xsl:stylesheet xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\" version=\"2.0\"><xsl:template name=\"start\"><ok/></xsl:template></xsl:stylesheet>', 'initial-template': QName('', 'start') })?output)" == "true"

#print axioms Env.restrictFeatures_allEnabled
#print axioms eval_allFeaturesEnabled
end L4Factoidal.XPath4.FeatureTests
