/-
L4Factoidal.XSLT4.Streaming.Tests — `#guard` checks of the streamability
analysis (the examples of XSLT Streaming 4.0 §3.9, §12.8.4, §12.8.9,
§12.10, §4.1) and of the streamed selection core. Checked by
`lake build l4xslt4`.
-/
import L4Factoidal.XSLT4.Streaming.Check
import L4Factoidal.XSLT4.Streaming.Select

namespace L4Factoidal.XSLT4.Streaming.Tests

open L4Factoidal.XPath4
open L4Factoidal.XSLT4.Streaming

/-- Posture and sweep of an expression with a striding context item of
    the given U-type. -/
def ps (src : String) (ct : UT := UT.elem) : Option (Posture × Sweep) :=
  match parseXPath src with
  | .ok e => let r := ex 400 { post := .striding, ct } e; some (r.p, r.s)
  | .error _ => none

/-! ### §3.9, the table of postures and sweeps -/
#guard ps "name()" == some (.grounded, .motionless)
#guard ps "string(title)" == some (.grounded, .consuming)
#guard ps "parent::*" == some (.climbing, .motionless)
#guard ps "child::x/ancestor::y" == some (.climbing, .consuming)
#guard ps "@status" == some (.striding, .motionless)
#guard ps "child::*" == some (.striding, .consuming)
#guard ps "descendant::*" == some (.crawling, .consuming)
#guard ps "preceding::*" == some (.roaming, .freeRanging)

/-! ### §12.8.4 and §12.8.9 -/
#guard ps "parent::A | */ancestor::B" == some (.climbing, .consuming)
#guard ps "* | */*" == some (.crawling, .consuming)
#guard ps "child::div | parent::div" == some (.roaming, .freeRanging)
#guard ps "a/@code" == some (.striding, .consuming)
#guard ps "./@code" == some (.striding, .motionless)
#guard ps "a/following::b" == some (.roaming, .freeRanging)
#guard ps "../@status" == some (.striding, .motionless)
#guard ps "copy-of(.)//a/following-sibling::*" == some (.grounded, .consuming)
-- a scanning expression (a motionless pattern) is crawling
#guard ps "//section/head" UT.doc == some (.crawling, .consuming)
-- the note of §12.8.9 says `.//section/head` is not a scanning
-- expression; this analysis scans it as `/descendant::section/head`, as the
-- xslt40-test cases expect (streamable-037: `sum(.//section/page-count)`)
#guard ps ".//section/head" UT.doc == some (.crawling, .consuming)
-- §12.8.2: a quantified expression over streamed nodes is read as a filter
#guard ps "some $t in transaction satisfies xs:decimal($t/@value) lt 0" == some (.grounded, .consuming)
#guard ps "section//head[1]" == some (.roaming, .freeRanging)

/-! ### §3.10 and §12.9 -/
#guard ps "count(.//chapter)" == some (.grounded, .consuming)
#guard ps "sum(.//transaction/@value)" == some (.grounded, .consuming)
#guard ps "head(.//chapter)" == some (.striding, .consuming)
#guard ps "count((.., *))" == some (.roaming, .freeRanging)
#guard ps "(@a, @b)" == some (.striding, .motionless)
#guard ps "if (@x) then @name else name" == some (.striding, .consuming)
#guard ps "reverse(ancestor::*)/name()" == some (.roaming, .freeRanging)
#guard ps "reverse(ancestor::*/name())" == some (.grounded, .motionless)
#guard ps "for $i in 1 to 3 return salary" == some (.roaming, .freeRanging)
#guard ps "for $i in 1 to 3 return name(ancestor::x[$i])" == some (.grounded, .motionless)
#guard ps "outermost(//para)" UT.doc == some (.striding, .consuming)
#guard ps "transaction[position() = last()]" == some (.roaming, .freeRanging)

/-! ### §12.10, motionless patterns -/

def motionless (src : String) : Bool :=
  match (({} : L4Factoidal.XSLT4.SCx).pattern src) with
  | .ok p => patMotionless 400 { post := .striding } p.e
  | .error _ => false

#guard ["/", "*", "/*", "p", "p|q", "p/q", "p[@status='red']", "p[@class or @style]",
  "p[@status]", "p[contains(@class, ':')]", "p[ancestor::*[@xml:lang]]",
  "text()[starts-with(., '$')]", "@price", "//p/text()[. = 'Introduction']"].all motionless
#guard !(["p[b]", "p[. = 'Introduction']", "p[starts-with(., '$')]", "p[1]",
  "p[position() gt 2]", "p[last()]", "$doc//p"].any motionless)

/-! ### §4.1: `xsl:source-document` must not return streamed nodes -/

def sheet (body : String) : String :=
  "<xsl:stylesheet version='3.0' xmlns:xsl='http://www.w3.org/1999/XSL/Transform'>" ++
  "<xsl:template name='main'><xsl:source-document streamable='yes' href='a.xml'>" ++ body ++
  "</xsl:source-document></xsl:template></xsl:stylesheet>"

def code (body : String) : String :=
  match analyzeModules [("file:///t.xsl", sheet body)] with
  | some e => e.code
  | none => "ok"

#guard code "<xsl:copy-of select='//chapter'/>" == "ok"
#guard code "<xsl:sequence select='//chapter'/>" == "XTSE3430"
#guard code "<out><xsl:value-of select='count(.//ITEM)'/></out>" == "ok"
#guard code "<xsl:for-each select='*/emp'><xsl:value-of select='.'/></xsl:for-each>" == "ok"
#guard code "<xsl:for-each select='*/emp'><xsl:sequence select='.'/></xsl:for-each>" == "XTSE3430"
#guard code "<xsl:value-of select='sum(//a)'/><xsl:value-of select='count(//b)'/>" == "XTSE3430"
#guard code "<xsl:fork><xsl:sequence select='count(//a)'/><xsl:sequence select='count(//b)'/></xsl:fork>" == "ok"
#guard code "<xsl:variable name='v' select='//a'/><xsl:value-of select='count($v)'/>" == "XTSE3430"

/-! ### The streamed selection core -/

def doc1 : String := "<a><b><c>1</c><c>2</c></b><b><c>3</c><d><c>no</c></d></b><x/></a>"

def rebuilt : Bool :=
  match L4Factoidal.XML.parseXML doc1 with
  | .ok d => build (docEvents d) == some d.children
  | .error _ => false

#guard rebuilt

def strs (p : List String) : Option (List String) :=
  match L4Factoidal.XML.parseXML doc1 with
  | .ok d => streamStrings p (docEvents d)
  | .error _ => none

#guard strs ["a", "b", "c"] == some ["1", "2", "3"]
#guard strs ["a", "*"] == some ["12", "3no", ""]
#guard strs ["a", "b", "d", "c"] == some ["no"]
#guard strs ["b"] == some []

end L4Factoidal.XSLT4.Streaming.Tests
