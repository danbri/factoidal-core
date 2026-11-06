import L4Factoidal.XProc31.Runtime
import L4Factoidal.XProc31.Bridge

/-! End-to-end checks independent of the upstream runner and its expected-error
reader. Run with `l4xproc --self-test`.
All pipeline evaluation and assertions use the shipping Lean implementations. -/
namespace L4Factoidal.XProc31.Regression

structure Case where
  name : String
  body : String
  assertion : String := "true()"
  expectedError : String := ""
  expectedUnsupported : Bool := false

def cases : List Case := [
  { name := "declared input default", body := "<p:declare-step type='Q{urn:local}default'><p:input port='source'><default/></p:input><p:output port='result'/><p:identity/></p:declare-step><e:default xmlns:e='urn:local'/>", assertion := "exists(/default)" },
  { name := "availability follows excluded declaration", body := "<p:declare-step type='Q{urn:local}a' use-when='false()'><p:identity/></p:declare-step><p:declare-step type='Q{urn:local}b' use-when='p:step-available(&quot;Q{urn:local}a&quot;)'><p:identity/></p:declare-step><p:identity><p:with-input><result>{p:step-available('Q{urn:local}b')}</result></p:with-input></p:identity>", assertion := "result='false'" },
  { name := "availability cycle", body := "<p:declare-step type='Q{urn:local}a' use-when='p:step-available(&quot;Q{urn:local}b&quot;)'><p:identity/></p:declare-step><p:declare-step type='Q{urn:local}b' use-when='p:step-available(&quot;Q{urn:local}a&quot;)'><p:identity/></p:declare-step><p:identity><p:with-input><doc/></p:with-input></p:identity>", expectedError := "XS0115" },
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
  { name := "atomic XPath option type", body := "<p:option name='v' as='xs:integer' select='&quot;invalid&quot;'/><p:identity><p:with-input><doc/></p:with-input></p:identity>", expectedError := "XD0036" },
  { name := "named compound output", body := "<p:group name='g'><p:output port='result' primary='true'/><p:output port='other'><p:inline><second/></p:inline></p:output><p:identity><p:with-input><first/></p:with-input></p:identity></p:group><p:identity><p:with-input pipe='other@g'/></p:identity>", assertion := "exists(/second)" },
  { name := "split unmatched output", body := "<p:split-sequence name='s' test='exists(/a)'><p:with-input><a/><b/><a/></p:with-input></p:split-sequence><p:identity><p:with-input pipe='not-matched@s'/></p:identity>", assertion := "exists(/b)" },
  { name := "literal use-when is data", body := "<p:identity><p:with-input><doc use-when='false()'/></p:with-input></p:identity>", assertion := "doc/@use-when='false()'" },
  { name := "excluded foreign step", body := "<e:group xmlns:e='urn:foreign' p:use-when='false()'/><p:identity><p:with-input><doc/></p:with-input></p:identity>", assertion := "exists(/doc)" },
  { name := "foreign group is not standard", body := "<e:group xmlns:e='urn:foreign'><p:identity><p:with-input><doc/></p:with-input></p:identity></e:group>", expectedError := "XS0044" },
  { name := "callee defaults do not capture caller variables", body := "<p:declare-step type='e:local' xmlns:e='urn:local'><p:output port='result'/><p:option name='x' select='&quot;inner&quot;'/><p:identity><p:with-input><doc>{$x}</doc></p:with-input></p:identity></p:declare-step><p:variable name='x' select='&quot;outer&quot;'/><e:local xmlns:e='urn:local'/>", assertion := "doc='inner'" },
  { name := "branch default collection", body := "<p:identity><p:with-input><a/><b/></p:with-input></p:identity><p:choose><p:when collection='true' test='count(collection())=2'><p:identity><p:with-input><ok/></p:with-input></p:identity></p:when></p:choose>", assertion := "exists(/ok)" },
  { name := "dynamic pipeline", body := "<p:run><p:with-input><p:inline expand-text='false'><p:declare-step version='3.1'><p:output port='result'/><p:identity><p:with-input><dynamic/></p:with-input></p:identity></p:declare-step></p:inline></p:with-input><p:output port='result'/></p:run>", assertion := "exists(/dynamic)" }

]

def runCase (c : Case) : IO (Except String Unit) := do
  let xml := "<p:declare-step xmlns:p='http://www.w3.org/ns/xproc' xmlns:xs='http://www.w3.org/2001/XMLSchema' version='3.1'><p:output port='result'/>" ++ c.body ++ "</p:declare-step>"
  let .ok parsed := XML.parseXML xml | return .error "regression XML failed to parse"
  match ← runPipeline parsed.root [] "file:///tmp/xproc-regression.xpl" with
  | .error e =>
    if (c.expectedUnsupported && e.unsupported) || (!e.unsupported && e.code == c.expectedError) then pure (.ok ())
    else pure (.error s!"unexpected {e.code}: {e.message}")
  | .ok docs =>
    if c.expectedUnsupported then return .error "expected unsupported feature refusal, got success"
    if c.expectedError != "" then return .error s!"expected {c.expectedError}, got success"
    let [d] := docs | return .error s!"expected one output, got {docs.length}"
    match evalBool c.assertion (xpathEnv (some d)) with
    | .ok true => pure (.ok ())
    | .ok false => pure (.error ("assertion false: " ++ c.assertion))
    | .error e => pure (.error s!"assertion error {e.code}: {e.message}")

def run : IO UInt32 := do
  let mut failed := 0
  if ← fileStepsRegression then IO.println "PASS filesystem effects and confinement"
  else
    IO.println "FAIL filesystem effects and confinement"
    failed := failed + 1
  if ← resourceContextRegression then IO.println "PASS XPath resource loading and refresh"
  else
    IO.println "FAIL XPath resource loading and refresh"
    failed := failed + 1
  if ← utilityStepsRegression then IO.println "PASS UUID generation"
  else
    IO.println "FAIL UUID generation"
    failed := failed + 1
  if ← validationStepsRegression then IO.println "PASS DTD validation and reports"
  else
    IO.println "FAIL DTD validation and reports"
    failed := failed + 1
  if ← compressionStepsRegression then IO.println "PASS gzip byte roundtrip"
  else
    IO.println "FAIL gzip byte roundtrip"
    failed := failed + 1
  if ← archiveStepsRegression then IO.println "PASS ZIP archive update and extraction"
  else
    IO.println "FAIL ZIP archive update and extraction"
    failed := failed + 1
  if ← processStepsRegression then IO.println "PASS process byte streams and errors"
  else
    IO.println "FAIL process byte streams and errors"
    failed := failed + 1
  for c in cases do
    match ← runCase c with
    | .ok () => IO.println ("PASS " ++ c.name)
    | .error msg =>
      failed := failed + 1
      IO.println ("FAIL " ++ c.name ++ ": " ++ msg)
  IO.println s!"REGRESSIONS {cases.length + 7 - failed} pass / {failed} fail (out of {cases.length + 7})"
  pure (if failed == 0 then 0 else 1)

/-- Measure the actual parse/check/execute path at increasing step counts. -/
def scaling : IO UInt32 := do
  let mut failed := false
  for count in [64, 128, 256] do
    let body := "<p:identity><p:with-input><doc>sentinel</doc></p:with-input></p:identity>" ++
      String.join (List.replicate count "<p:identity/>")
    let start ← IO.monoMsNow
    let result ← runCase {name := "identity chain", body, assertion := "/doc='sentinel'"}
    let elapsed := (← IO.monoMsNow) - start
    match result with
    | .ok () => IO.println s!"SCALING steps={count+1} elapsed_ms={elapsed} PASS"
    | .error e =>
      failed := true
      IO.println s!"SCALING steps={count+1} elapsed_ms={elapsed} FAIL {e}"
  pure (if failed then 1 else 0)

end L4Factoidal.XProc31.Regression

