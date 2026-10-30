/-
Serialization parameters and assertion options through fn:transform.
F&O fn:transform and Serialization: QName-valued parameters preserve
expanded names and merge with the stylesheet's output declaration.
https://github.com/danbri/factoidal/issues/1161
-/
import L4Factoidal.XSLT4.QtFnTransform
import L4Factoidal.XSLT4.FnTransform

namespace L4Factoidal.XSLT4.Qt.Tests

open L4Factoidal.XPath4

private def answer (src : String) : String :=
  let e : Env := { baseUri := "https://example.org/query.xq" }
  let e := { e with host := transformHost e (fun f a => apply 20000 e f a) e.host }
  match evalString src e with
  | .ok s => showSeq s
  | .error er => er.code

private def cdataSheet : String :=
  "<xsl:stylesheet xmlns:xsl='http://www.w3.org/1999/XSL/Transform' version='3.0'>" ++
  "<xsl:output cdata-section-elements='keep'/>" ++
  "<xsl:template name='main'><out xmlns:n='urn:target' xmlns:o='urn:other'>" ++
  "<keep>base</keep><n:c>target</n:c><c>plain</c><o:c>other</o:c>" ++
  "</out></xsl:template></xsl:stylesheet>"

private def indentSheet : String :=
  "<xsl:stylesheet xmlns:xsl='http://www.w3.org/1999/XSL/Transform' version='3.0'>" ++
  "<xsl:output indent='yes' suppress-indentation='keep'/>" ++
  "<xsl:template name='main'><out xmlns:n='urn:target' xmlns:o='urn:other'>" ++
  "<keep><t>base</t></keep><n:c><t>target</t></n:c>" ++
  "<c><t>plain</t></c><o:c><t>other</t></o:c>" ++
  "</out></xsl:template></xsl:stylesheet>"

private def call (sheet key values : String) : String :=
  "let $s := transform(map { 'stylesheet-text': \"" ++ sheet ++
  "\", 'initial-template': QName('', 'main'), 'delivery-format': 'serialized', " ++
  "'serialization-params': map { 'omit-xml-declaration': true(), '" ++ key ++ "': " ++ values ++
  " } })?output return "

-- Both names have local part c; only the selected namespace and no-namespace
-- names receive CDATA. The stylesheet's keep declaration remains effective.
#guard answer (call cdataSheet "cdata-section-elements"
    "(QName('urn:target', 'c'), QName('', 'c'))" ++
    "contains($s, '<![CDATA[base]]>') and contains($s, '<![CDATA[target]]>') and " ++
    "contains($s, '<![CDATA[plain]]>') and not(contains($s, '<![CDATA[other]]>'))") == "true"

-- Singleton QName conversion was already namespace-aware.
#guard answer (call cdataSheet "cdata-section-elements" "QName('urn:target', 'c')" ++
    "contains($s, '<![CDATA[base]]>') and contains($s, '<![CDATA[target]]>') and " ++
    "not(contains($s, '<![CDATA[plain]]>')) and not(contains($s, '<![CDATA[other]]>'))") == "true"

-- Suppression merges the caller's QName sequence with the output declaration;
-- the unselected namespace still receives indentation inside its c element.
#guard answer (call indentSheet "suppress-indentation"
    "(QName('urn:target', 'c'), QName('', 'c'))" ++
    "contains($s, '><t>base</t><') and contains($s, '><t>target</t><') and " ++
    "contains($s, '><t>plain</t><') and matches($s, '>\\s+<t>other</t>\\s+<')") == "true"

#guard answer (call indentSheet "suppress-indentation" "QName('urn:target', 'c')" ++
    "contains($s, '><t>base</t><') and contains($s, '><t>target</t><') and " ++
    "matches($s, '>\\s+<t>plain</t>\\s+<') and matches($s, '>\\s+<t>other</t>\\s+<')") == "true"


private def assertSheet (test body : String) : String :=
  "<xsl:stylesheet xmlns:xsl='http://www.w3.org/1999/XSL/Transform' version='3.0'>" ++
  "<xsl:template name='main'><out>ok<xsl:assert test='" ++ test ++ "'>" ++ body ++
  "</xsl:assert></out></xsl:template></xsl:stylesheet>"

private def assertCall (test body option : String) : String :=
  "transform(map { 'stylesheet-text': \"" ++ assertSheet test body ++ "\", " ++
  "'initial-template': QName('', 'main')" ++ option ++ " })?output ! string()"

-- Direct XSLT invocation keeps assertions enabled by default.
private def directAnswer (test : String) : String :=
  let result : M TResult := do
    let uri := "https://example.org/assertions.xsl"
    let sheet ← compileStylesheet uri [(uri, assertSheet test "")]
    transform sheet { initialTemplate := some { uri := "", loc := "main" } }
  match result with
  | .ok _ => "ok"
  | .error er => er.code

#guard directAnswer "false()" == "XTMM9001"
#guard directAnswer "true()" == "ok"

-- F&O fn:transform: assertions are disabled unless explicitly enabled.
#guard answer (assertCall "false()" "" "") == "ok"
#guard answer (assertCall "false()" "" ", 'enable-assertions': false()") == "ok"
#guard answer (assertCall "false()" "" ", 'enable-assertions': true()") == "XTMM9001"

-- A disabled assertion evaluates neither its test nor its message body.
#guard answer (assertCall "1 idiv 0 = 1" "" ", 'enable-assertions': false()") == "ok"
#guard answer (assertCall "false()" "<xsl:sequence select='1 idiv 0'/>"
    ", 'enable-assertions': false()") == "ok"
#guard answer (assertCall "1 idiv 0 = 1" "" ", 'enable-assertions': true()") == "FOAR0001"

-- The adapter also used for nested XSLT fn:transform calls follows the same
-- option contract. Its independent entry point must retain the option.
private def nestedAnswer (src : String) : String :=
  let e : Env := { baseUri := "https://example.org/query.xq" }
  let e := { e with host := L4Factoidal.XSLT4.fnTransformHost 10 [] e }
  match evalString src e with
  | .ok s => showSeq s
  | .error er => er.code

#guard nestedAnswer (assertCall "false()" "" "") == "ok"
#guard nestedAnswer (assertCall "1 idiv 0 = 1" "" ", 'enable-assertions': false()") == "ok"
#guard nestedAnswer (assertCall "false()" "" ", 'enable-assertions': true()") == "XTMM9001"


-- An actual transform inside a stylesheet consumes the predecessor host
-- and runner budgets. Adjacent budgets expose exhaustion and success.
private def nestedFuelAnswer (fuel : Nat) : String :=
  let leaf := "<xsl:stylesheet xmlns:xsl='http://www.w3.org/1999/XSL/Transform' version='3.0'>" ++
    "<xsl:template name='main'><xsl:sequence select='7'/></xsl:template></xsl:stylesheet>"
  let outer := "<xsl:stylesheet xmlns:xsl='http://www.w3.org/1999/XSL/Transform' version='3.0'>" ++
    "<xsl:template name='main'><xsl:sequence select=\"transform(map { " ++
    "'stylesheet-location': 'leaf.xsl', 'initial-template': QName('', 'main'), " ++
    "'delivery-format': 'raw' })?output\"/></xsl:template></xsl:stylesheet>"
  let e : Env := { baseUri := "https://example.org/nested/query.xq", resources :=
    [("https://example.org/nested/leaf.xsl", leaf), ("https://example.org/nested/outer.xsl", outer)] }
  let e := { e with host := L4Factoidal.XSLT4.fnTransformHost fuel [] e }
  match evalString "transform(map { 'stylesheet-location': 'outer.xsl', 'initial-template': QName('', 'main'), 'delivery-format': 'raw' })?output" e with
  | .ok s => showSeq s
  | .error er => er.code

#guard nestedFuelAnswer 3 == "FOXT0001"
#guard nestedFuelAnswer 4 == "7"

end L4Factoidal.XSLT4.Qt.Tests
