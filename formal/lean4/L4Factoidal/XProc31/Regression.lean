import L4Factoidal.XProc31.Runtime
import L4Factoidal.XProc31.Bridge

/-! End-to-end checks independent of the upstream runner and its expected-error
reader. Run with `lake env lean --run L4Factoidal/XProc31/Regression.lean`.
All pipeline evaluation and assertions use the shipping Lean implementations. -/
namespace L4Factoidal.XProc31.Regression

structure Case where
  name : String
  body : String
  assertion : String := "true()"
  expectedError : String := ""

def cases : List Case := [
  { name := "identity preserves content", body := "<p:identity><p:with-input><doc a='v'>text</doc></p:with-input></p:identity>", assertion := "doc/@a='v' and doc/text()='text'" },
  { name := "sequence count", body := "<p:count><p:with-input><a/><b/><c/></p:with-input></p:count>", assertion := "/*='3'" },
  { name := "forward dependency", body := "<p:identity name='consumer'><p:with-input pipe='result@producer'/></p:identity><p:identity name='producer'><p:with-input><forward/></p:with-input></p:identity>", assertion := "exists(/forward)" },
  { name := "cycle rejected", body := "<p:identity name='a'><p:with-input pipe='result@b'/></p:identity><p:identity name='b'><p:with-input pipe='result@a'/></p:identity>", expectedError := "XS0001" },
  { name := "unknown step reference rejected", body := "<p:identity><p:with-input pipe='result@missing'/></p:identity>", expectedError := "XS0022" },
  { name := "AVT uses default readable port", body := "<p:identity><p:with-input><previous>value</previous></p:with-input></p:identity><p:add-attribute attribute-name='a' attribute-value='{string(/previous)}'><p:with-input><different/></p:with-input></p:add-attribute>", assertion := "different/@a='value'" },
  { name := "inline expression", body := "<p:variable name='v' select='21*2'/><p:identity><p:with-input><doc>{$v}</doc></p:with-input></p:identity>", assertion := "doc='42'" },
  { name := "choose branch context", body := "<p:choose><p:with-input><yes/></p:with-input><p:when test='exists(/yes)'><p:with-input><no/></p:with-input><p:identity><p:with-input><wrong/></p:with-input></p:identity></p:when><p:otherwise><p:identity><p:with-input><right/></p:with-input></p:identity></p:otherwise></p:choose>", assertion := "exists(/right)" },
  { name := "for-each positions", body := "<p:for-each><p:with-input><a/><b/></p:with-input><p:identity><p:with-input><item>{p:iteration-position()}</item></p:with-input></p:identity></p:for-each><p:wrap-sequence wrapper='out'/>", assertion := "count(out/item)=2 and out/item[1]='1' and out/item[2]='2'" },
  { name := "viewport replaces topmost elements", body := "<p:viewport match='a'><p:with-input><root><a><a/></a><b/><a/></root></p:with-input><p:identity><p:with-input><replaced/></p:with-input></p:identity></p:viewport>", assertion := "count(root/replaced)=2 and count(root/b)=1 and empty(//a)" },
  { name := "direct try subpipeline", body := "<p:try><p:error code='Q{urn:test}failure'/><p:catch><p:identity><p:with-input><caught/></p:with-input></p:identity></p:catch></p:try>", assertion := "exists(/caught)" },
  { name := "input serialization does not swallow text", body := "<p:identity><p:with-input><p:inline content-type='text/plain' expand-text='false'>literal {braces}</p:inline></p:with-input></p:identity><p:wrap-sequence wrapper='out'/>", assertion := "out='literal {braces}'" },
  { name := "output cardinality", body := "<p:identity><p:with-input><a/><b/></p:with-input></p:identity>", expectedError := "XD0007" },
  { name := "atomic XPath option type", body := "<p:option name='v' as='xs:integer' select='&quot;invalid&quot;'/><p:identity><p:with-input><doc/></p:with-input></p:identity>", expectedError := "XD0036" }
]

def runCase (c : Case) : IO (Except String Unit) := do
  let xml := "<p:declare-step xmlns:p='http://www.w3.org/ns/xproc' xmlns:xs='http://www.w3.org/2001/XMLSchema' version='3.1'><p:output port='result'/>" ++ c.body ++ "</p:declare-step>"
  let .ok parsed := XML.parseXML xml | return .error "regression XML failed to parse"
  match ← runPipeline parsed.root [] "file:///tmp/xproc-regression.xpl" with
  | .error e =>
    if !e.unsupported && e.code == c.expectedError then pure (.ok ())
    else pure (.error s!"unexpected {e.code}: {e.message}")
  | .ok docs =>
    if c.expectedError != "" then return .error s!"expected {c.expectedError}, got success"
    let [d] := docs | return .error s!"expected one output, got {docs.length}"
    match evalBool c.assertion (xpathEnv (some d)) with
    | .ok true => pure (.ok ())
    | .ok false => pure (.error ("assertion false: " ++ c.assertion))
    | .error e => pure (.error s!"assertion error {e.code}: {e.message}")

def run : IO UInt32 := do
  let mut failed := 0
  for c in cases do
    match ← runCase c with
    | .ok () => IO.println ("PASS " ++ c.name)
    | .error msg =>
      failed := failed + 1
      IO.println ("FAIL " ++ c.name ++ ": " ++ msg)
  IO.println s!"REGRESSIONS {cases.length - failed} pass / {failed} fail (out of {cases.length})"
  pure (if failed == 0 then 0 else 1)

end L4Factoidal.XProc31.Regression

def main : IO UInt32 := L4Factoidal.XProc31.Regression.run
