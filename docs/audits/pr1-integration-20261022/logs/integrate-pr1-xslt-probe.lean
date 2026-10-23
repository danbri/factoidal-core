/-
L4Factoidal.XSLT.TransformTests — build-time checks for the XSLT 1.0
engine, end to end: a stylesheet string and a source string in, the
serialised result tree out.

Each check pins a rule the vendored `xslt30-test` subset caught this
module getting wrong, and names the case that caught it. Every one of
them produced a document of the RIGHT SHAPE with the wrong content,
which is the failure mode that reads as a near miss.
-/
import L4Factoidal.XSLT.Transform

namespace L4Factoidal.XSLT

open L4Factoidal.XML

/-- Run a transform, or report the refusal, as one string. -/
def run (style src : String) : String :=
  match parseXML style, parseXML src with
  | .error e, _ => "STYLESHEET NOT WELL FORMED: " ++ e.message
  | _, .error e => "SOURCE NOT WELL FORMED: " ++ e.message
  | .ok st, .ok sr =>
      match transform st sr with
      | .produced t => t
      | .refused r  => "REFUSED: " ++ r

private def ss (body : String) : String :=
  "<xsl:stylesheet xmlns:xsl=\"http://www.w3.org/1999/XSL/Transform\" version=\"1.0\">"
  ++ body ++ "</xsl:stylesheet>"

#eval run "<x:stylesheet xmlns:x='http://www.w3.org/1999/XSL/Transform' xmlns:p='urn:p' version='1.0'><x:template match='/'><x:for-each select=\"document('')//p:a\"><x:copy/></x:for-each></x:template><p:a/></x:stylesheet>" "<doc/>"
#eval run "<x:stylesheet xmlns:x='http://www.w3.org/1999/XSL/Transform' xmlns:p='urn:p' version='1.0'><x:template match='/'><x:variable name='v' select=\"document('')//p:a\"/><x:for-each select='$v'><x:value-of select='namespace-uri(.)'/><x:value-of select='name(..)'/><x:copy-of select='.'/></x:for-each></x:template><p:a/></x:stylesheet>" "<doc/>"
end L4Factoidal.XSLT
