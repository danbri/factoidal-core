/-
Namespace-sensitive serialization parameters through fn:transform.
F&O fn:transform and Serialization: QName-valued parameters preserve
expanded names and merge with the stylesheet's output declaration.
https://github.com/danbri/factoidal/issues/1161
-/
import L4Factoidal.XSLT4.QtFnTransform

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

end L4Factoidal.XSLT4.Qt.Tests
