import L4Factoidal.XProc31.Runtime
import L4Factoidal.XProc31.Regression
import L4Factoidal.XProc31.Bridge
import L4Factoidal.XProc31.FileEnvironment
import L4Factoidal.XPath4.Eval

/-! XProc community test-suite runner. Each test executes in a separate process
with a wall-clock deadline. Unsupported runtime or assertion features are separate
from passes; wrong results and wrong error codes are failures. -/
namespace L4Factoidal.XProc31.Runner
open XML
open XPath4

def tag (n : XML.Node) : String := (XPath4.splitName (n.elementTag.getD "")).2
def attr (n : XML.Node) (a : String) : String := (XML.findAttr a n.elementAttrs).getD ""
def kids (n : XML.Node) : List XML.Node := n.allChildElements
def named (n : XML.Node) (a : String) : List XML.Node := (kids n).filter (tag · == a)
def words (s : String) : List String := (s.splitOn " ").filter (· != "")
def namespaces (n : XML.Node) : List (String × String) := n.elementAttrs.filterMap fun a =>
  if a.name == "xmlns" then some ("", a.value)
  else if a.name.startsWith "xmlns:" then some ((a.name.drop 6).toString, a.value) else none

def inheritNs (parent child : XML.Node) : XML.Node :=
  match child with
  | .element name attrs children =>
    let add := parent.elementAttrs.filter fun a =>
      (a.name == "xmlns" || a.name.startsWith "xmlns:") && !attrs.any (·.name == a.name)
    .element name (attrs ++ add) children
  | n => n

def desc : Nat → XML.Node → List XML.Node
  | 0, _ => []
  | fuel + 1, n => n :: (kids n).flatMap (desc fuel)

def dir (p : String) : String := String.intercalate "/" (p.splitOn "/").dropLast
def resolve (base href : String) : String :=
  if href.startsWith "file://" then (href.drop 7).toString
  else if href.startsWith "/" then href else dir base ++ "/" ++ href

def loadXml (path : String) : IO (Except String XML.Node) := do
  try
    let s ← IO.FS.readFile path
    pure <| (XML.parseXML s).mapError reprStr |>.map (·.root)
  catch e => pure (.error s!"{path}: {e}")

inductive Outcome where
  | pass
  | fail (message : String)
  | unsupported (message : String)
deriving Repr

def Outcome.code : Outcome → UInt32
  | .pass => 0 | .fail _ => 1 | .unsupported _ => 2

def Outcome.message : Outcome → String
  | .pass => "pass" | .fail m => "fail: " ++ m | .unsupported m => "unsupported: " ++ m

def evalBool (env : XPath4.Env) (s : String) : Except String Bool :=
  (XPath4.evalString s env >>= XPath4.ebv).mapError (fun e => e.code ++ ": " ++ e.msg)

def oracleError (where_ message : String) : Outcome :=
  if message.startsWith "XPST0017" || message.startsWith "XPST0003" || message.contains "not implemented" then
    .unsupported (where_ ++ ": " ++ message)
  else .fail (where_ ++ ": " ++ message)

def bindings (env : XPath4.Env) (n : XML.Node) : Except String XPath4.Env := do
  let mut env := env
  for b in named n "let" do
    let name := attr b "name"
    if name.contains ':' then throw "namespace-qualified Schematron variable"
    let value ← (XPath4.evalString (attr b "value") env).mapError (fun e => e.code ++ ": " ++ e.msg)
    env := { env with vars := ({ uri := "", loc := name }, value) :: env.vars }
  pure env

/-- Schematron contexts are patterns: a relative path matches at any depth.
The first matching rule of each pattern applies to a node. -/
def contextSelect (s : String) : String :=
  String.intercalate " | " ((s.splitOn "|").map fun part =>
    let part := part.trimAscii.toString
    if part.startsWith "/" then part else "//" ++ part)

def checkSchema (schema : XML.Node) (output : XProc31.Document) : Outcome := Id.run do
  let all := desc 1000 schema
  if all.any (fun n => ["include", "extends", "phase"].contains (tag n) || attr n "abstract" == "true") then
    return .unsupported "Schematron include, abstract pattern, or phase"
  if all.any (fun n => (n.elementTag.getD "").startsWith "xsl:") then
    return .unsupported "Schematron XSLT extension"
  let ns := (all.filter (tag · == "ns")).map (fun n => (attr n "prefix", attr n "uri")) ++ (namespaces schema).filter (·.1 != "")
  let ns := if attr schema "xpath-default-namespace" == "" then ns else ("", attr schema "xpath-default-namespace") :: ns
  let env : XPath4.Env := {
    docs := #[XPath4.Doc.ofNodes (XProc31.documentNodes output) output.baseUri]
    ctx := some [.node { doc := 0, idx := 0 }]
    pos := 1
    size := 1
    ns := ns }
  let env ← match bindings env schema with
    | .ok e => pure e
    | .error m => return oracleError "Schematron schema let" m
  let mut assertions := 0
  for pattern in named schema "pattern" do
    let env ← match bindings env pattern with
      | .ok e => pure e
      | .error m => return oracleError "Schematron pattern let" m
    let mut matched : List Nat := []
    for rule in named pattern "rule" do
      let nodes ← match XPath4.evalString (contextSelect (attr rule "context")) env with
        | .ok ns => pure ns
        | .error e => return oracleError "Schematron context" (e.code ++ ": " ++ e.msg)
      for node in nodes do
        let idx ← match node with
          | .node n => pure n.idx
          | _ => return .unsupported "Schematron non-node context"
        if matched.contains idx then continue
        matched := idx :: matched
        let env := { env with ctx := some [node], pos := 1, size := 1 }
        let env ← match bindings env rule with
          | .ok e => pure e
          | .error m => return oracleError "Schematron rule let" m
        for assertion in kids rule do
          if tag assertion != "assert" && tag assertion != "report" then continue
          assertions := assertions + 1
          match evalBool env (attr assertion "test") with
          | .error m => return oracleError "Schematron assertion" m
          | .ok b =>
            if b != (tag assertion == "assert") then
              return .fail ("Schematron " ++ tag assertion ++ ": " ++ attr assertion "test")
  if assertions == 0 then return .unsupported "no Schematron assertion evaluated"
  return .pass

/-- Load an inline or external suite component, preserving inherited namespaces. -/
def component (base : String) (parent node : XML.Node) : IO (Except String XML.Node) := do
  let src := attr node "src"
  if src != "" then loadXml (resolve base src)
  else pure <| match (kids node).head? with
    | none => .error ("empty " ++ tag node)
    | some n => .ok (inheritNs parent (inheritNs node n))

def expandedCode (scope : List (String × String)) (code : String) : String :=
  if code.startsWith "Q{" then code
  else
    let (p, loc) := XPath4.splitName code
    let uri := if p != "" then (scope.lookup p).getD ("unbound:" ++ p)
      else if loc.startsWith "XS" || loc.startsWith "XD" || loc.startsWith "XC" then
        "http://www.w3.org/ns/xproc-error"
      else if ["FO", "XP", "XQ", "XT", "SE"].any (fun pfx => loc.startsWith pfx) then "http://www.w3.org/2005/xqt-errors"
      else (scope.lookup "").getD ""
    "Q{" ++ uri ++ "}" ++ loc

def expectedCode (root : XML.Node) (actual : String) : Bool :=
  (words (attr root "code")).any fun code => code == "*" ||
    expandedCode (namespaces root) code == expandedCode [] actual

/-- XProc serialization maps permit whitespace-separated lexical QNames for
QName-list parameters; fn:serialize requires xs:QName values. -/
def serializationOptions (env : XPath4.Env) (opts : XPath4.Seq) : XPath4.M XPath4.Seq :=
  opts.mapM fun item => match item with
    | .map entries => do
      let entries ← entries.mapM fun (key, value) => do
        let key := match key.v with
          | .qn q => if q.uri == "" then XPath4.Atomic.ofStr q.loc else key
          | _ => key
        if !["cdata-section-elements", "suppress-indentation", "double-space"].contains key.str then
          pure (key, value)
        else
          let values ← value.mapM fun item => match item with
            | .atom a =>
              if a.isStringLike then
                (words a.str).mapM fun lexical => do
                  if lexical.startsWith "Q{" then
                    let parts := ((lexical.drop 2).toString).splitOn "}"
                    match parts with
                    | [uri, loc] =>
                      if uri.contains '{' || loc.contains ':' then XPath4.err "SEPM0016" "invalid serialization EQName"
                      else
                        let _ ← XPath4.castFromString loc (.b .qname) env.nsResolve
                        pure (.atom (XPath4.Atomic.ofQN ⟨uri,loc,""⟩))
                    | _ => XPath4.err "SEPM0016" "invalid serialization EQName"
                  else pure (.atom (← XPath4.castFromString lexical (.b .qname) env.nsResolve))
              else pure [item]
            | _ => pure [item]
          pure (key, values.flatten)
      pure (.map entries)
    | i => pure i

def runTestIn (path sandbox : String) : IO Outcome := do
  let path := (← IO.FS.realPath path).toString
  let root ← match ← loadXml path with
    | .error m => return .fail ("test XML: " ++ m)
    | .ok n => pure n
  if tag root != "test" then return .unsupported "not a t:test"
  if (words (attr root "features")).contains "lazy-eval" then return .unsupported "lazy evaluation mode (processor uses eager evaluation)"
  let features := words (attr root "features")
  if features.contains "urify-windows" && !System.Platform.isWindows then
    return .unsupported "Windows platform dependency"
  if features.contains "urify-non-windows" && System.Platform.isWindows then
    return .unsupported "non-Windows platform dependency"
  if attr root "src" != "" then return .unsupported "t:test external indirection"
  if attr root "step" != "" then return .unsupported "library entry step selection"
  let requiresFiles := XProc31.needsFileEnvironment 4096 root
  let prepared ← if requiresFiles then XProc31.prepareFileEnvironment path sandbox root else pure (.ok path)
  let path ← match prepared with
    | .ok path => pure path
    | .error e => return .unsupported e.message
  if attr root "when" != "" then
    match evalBool { ns := namespaces root } (attr root "when") with
    | .ok true => pure ()
    | .ok false => return .unsupported "test precondition is false"
    | .error m => return .unsupported ("test precondition: " ++ m)
  let options := (named root "option").map (fun n => (attr n "name", attr n "select"))
  let pipelineSpec ← match (named root "pipeline").head? with
    | none => return .fail "missing t:pipeline"
    | some n => pure n
  let pipeline ← match ← component path root pipelineSpec with
    | .error m => return .fail ("pipeline fixture: " ++ m)
    | .ok n => pure n
  let pipelinePath := if attr pipelineSpec "src" == "" then path else resolve path (attr pipelineSpec "src")
  let mut inputs : List XProc31.Document := []
  for input in named root "input" do
    if attr input "port" != "source" then return .unsupported ("external input port: " ++ attr input "port")
    if attr input "src" != "" then
      let inputPath := resolve path (attr input "src")
      match ← loadXml inputPath with
      | .error m => return .fail m
      | .ok n => inputs := inputs ++ [{ node := n, baseUri := "file://" ++ inputPath }]
    else
      for n in kids input do
        inputs := inputs ++ [{ node := inheritNs root (inheritNs input n), baseUri := "file://" ++ path }]
  let result ← XProc31.runPipeline pipeline inputs ("file://" ++ pipelinePath) options
    (if requiresFiles then some sandbox else none)
  match result with
  | .error e =>
    if e.unsupported then return .unsupported e.message
    if attr root "expected" == "fail" && expectedCode root e.code then return .pass
    return .fail s!"expected {attr root "expected"} {attr root "code"}; got {e.code}: {e.message}"
  | .ok outputs =>
    if attr root "expected" == "fail" then return .fail ("expected error " ++ attr root "code" ++ "; succeeded")
    if attr root "expected" != "pass" then return .fail "unknown test expectation"
    let output ← match outputs with
      | [d] => pure d
      | ds => return .fail s!"expected one result document, got {ds.length}"
    let output ← if attr root "serialized" == "true" then do
      let declaration := (named pipeline "output").find? (fun n => attr n "port" == "result")
      let expression := declaration.map (attr · "serialization") |>.getD ""
      let pipeline := XProc31.inheritNS 4096 [] pipeline
      let mut env := XProc31.xpathEnv (some output) [] ((namespaces pipeline).filter (·.1 != ""))
      for (name, expression) in options do
        match XPath4.evalString expression env with
        | .error e => return oracleError "serialization external option" (e.code ++ ": " ++ e.msg)
        | .ok value => env := { env with vars := (XProc31.qname pipeline name, value) :: env.vars }
      for declaration in named pipeline "option" do
        let qname := XProc31.qname declaration (attr declaration "name")
        if env.vars.any (·.1 == qname) then continue
        if attr declaration "select" == "" then continue
        match XPath4.evalString (attr declaration "select") env with
        | .error e => return oracleError "serialization option" (e.code ++ ": " ++ e.msg)
        | .ok value => env := { env with vars := (qname, value) :: env.vars }
      let opts ← if expression == "" then pure [] else
        match XPath4.evalString expression env with
        | .ok v => pure v
        | .error e => return oracleError "serialization options" (e.code ++ ": " ++ e.msg)
      let serialized := do
        let stored ← serializationOptions env (documentProperty output ⟨"", "serialization", ""⟩)
        let explicit ← serializationOptions env opts
        let opts : XPath4.Seq := match stored, explicit with
          | [.map old], [.map overrides] => [.map (overrides ++ old.filter (fun (entry : XPath4.Atomic × XPath4.Seq) => !overrides.any (fun (replacement : XPath4.Atomic × XPath4.Seq) => replacement.1.str == entry.1.str)))]
          | _, [] => stored
          | _, _ => explicit
        let params ← XPath4.serParamsOf env opts
        env.serializeWith params ((xpathEnv (some output)).ctx.getD [])
      match serialized with
      | .error e => return oracleError "serialization" (e.code ++ ": " ++ e.msg)
      | .ok text => pure { output with node := .element "serialization" [] [.text text] }
    else pure output
    let schemas := named root "schematron"
    if schemas.isEmpty then return .unsupported "missing Schematron oracle"
    for spec in schemas do
      let schema ← match ← component path root spec with
        | .error m => return .fail ("Schematron fixture: " ++ m)
        | .ok n => pure n
      match checkSchema schema output with
      | .pass => pure ()
      | o => return o
    return .pass

structure Counts where
  pass : Nat := 0
  fail : Nat := 0
  unsupported : Nat := 0
  deriving Inhabited

def Counts.add (c : Counts) : Outcome → Counts
  | .pass => { c with pass := c.pass + 1 }
  | .fail _ => { c with fail := c.fail + 1 }
  | .unsupported _ => { c with unsupported := c.unsupported + 1 }
def Counts.show (c : Counts) : String :=
  s!"{c.pass} pass / {c.fail} fail / {c.unsupported} unsupported (out of {c.pass + c.fail + c.unsupported})"

/-- Bounded directory traversal; fixture enumeration is deterministic. -/
def files : Nat → System.FilePath → IO (List String)
  | 0, _ => throw (IO.userError "test directory nesting exceeds 100")
  | fuel + 1, p => do
    if ← p.isDir then
      let mut found := []
      for entry in ← p.readDir do
        found := found ++ (← files fuel entry.path)
      pure found
    else pure (if p.extension == some "xml" then [p.toString] else [])

structure Options where
  root : String := "../../third_party/testing/xproc-test-suite/test-suite/tests"
  filter : String := ""
  timeoutMs : Nat := 5000
  listFails : Bool := false
  listUnsupported : Bool := false

def parseOptions : List String → Options → Except String Options
  | [], o => .ok o
  | "--root" :: v :: rest, o => parseOptions rest { o with root := v }
  | "--filter" :: v :: rest, o => parseOptions rest { o with filter := v }
  | "--timeout-ms" :: v :: rest, o => do
    let n ← match v.toNat? with
      | some n => pure n
      | none => throw "invalid timeout"
    if n == 0 then throw "timeout must be positive"
    parseOptions rest { o with timeoutMs := n }
  | "--list-fails" :: rest, o => parseOptions rest { o with listFails := true }
  | "--list-unsupported" :: rest, o => parseOptions rest { o with listUnsupported := true }
  | a :: _, _ => .error ("unknown argument: " ++ a)

def isolatedIn (exe path sandbox : String) (timeoutMs : Nat) : IO Outcome := do
  let child ← IO.Process.spawn { cmd := exe, args := #["--one-sandbox", path, sandbox], stdout := .piped, stderr := .null }
  let start ← IO.monoMsNow
  let mut code : Option UInt32 := none
  for _ in [:timeoutMs / 5 + 2] do
    code ← child.tryWait
    if code.isSome then break
    if (← IO.monoMsNow) - start ≥ timeoutMs then break
    IO.sleep 5
  if code.isNone then
    child.kill
    let _ ← child.wait
    return .fail s!"timeout after {timeoutMs} ms"
  let message ← child.stdout.readToEnd
  match code with
  | some 0 => pure .pass
  | some 2 => pure (.unsupported message.trimAscii.toString)
  | _ => pure (.fail message.trimAscii.toString)

def runTest (path : String) : IO Outcome := do
  let sandbox ← IO.FS.createTempDir
  try runTestIn path (← IO.FS.realPath sandbox).toString
  finally IO.FS.removeDirAll sandbox

def isolated (exe path : String) (timeoutMs : Nat) : IO Outcome := do
  let sandbox ← IO.FS.createTempDir
  try isolatedIn exe path (← IO.FS.realPath sandbox).toString timeoutMs
  finally IO.FS.removeDirAll sandbox

/-- Infer features from executable step syntax, not test filenames. Inline
input documents and stylesheet/query payloads are not traversed as pipelines. -/
def pipelineFeatures : Nat → XML.Node → List String
  | 0, _ => []
  | fuel+1, node =>
    let (pfx, localName) := XPath4.splitName (node.elementTag.getD "")
    if ((namespaces node).lookup pfx).getD "" != "http://www.w3.org/ns/xproc" then []
    else
      let containers := ["declare-step", "library", "group", "for-each", "viewport", "choose", "when", "otherwise", "if", "try", "catch", "finally"]
      let declarations := ["declare-step", "library", "when", "otherwise", "catch", "finally", "input", "output", "option", "variable", "import", "with-input", "with-option", "documentation", "pipeinfo"]
      let own := if declarations.contains localName then [] else ["p:" ++ localName]
      own ++ if containers.contains localName then (kids node).flatMap (pipelineFeatures fuel) else []

def testFeatures (path : String) (root : XML.Node) : IO (List String) := do
  let given := words (attr root "features")
  if !given.isEmpty then return given.eraseDups
  let some spec := (named root "pipeline").head? | return ["pipeline-unavailable"]
  match ← component path root spec with
  | .error _ => return ["pipeline-unavailable"]
  | .ok pipeline =>
    let fs := (pipelineFeatures 4096 (XProc31.inheritNS 4096 [] pipeline)).eraseDups
    return if fs.isEmpty then ["pipeline-declarations"] else fs

/-- Command-line options carry XPath expressions, as pipeline options do. -/
def pipelineArguments : List String → List (String × String) → Except String (List (String × String))
  | [], options => pure options.reverse
  | "--option" :: assignment :: rest, options =>
    match assignment.splitOn "=" with
    | name :: values =>
      if name == "" || values.isEmpty then .error "--option requires NAME=XPath"
      else pipelineArguments rest ((name, String.intercalate "=" values) :: options)
    | _ => .error "--option requires NAME=XPath"
  | arg :: _, _ => .error ("unknown pipeline argument: " ++ arg)

def runFile (path : String) (options : List (String × String)) (writeRoot : Option String := none) : IO UInt32 := do
  try
    let path := (← IO.FS.realPath path).toString
    let pipeline ← match ← loadXml path with
      | .ok node => pure node
      | .error message => IO.eprintln ("ERROR XML: " ++ message); return 1
    let result ← XProc31.runPipeline pipeline [] ("file://" ++ path) options writeRoot
    match result with
    | .error e =>
      IO.eprintln s!"{if e.unsupported then "UNSUPPORTED" else "ERROR"} {e.code}: {e.message}"
      return if e.unsupported then 2 else 1
    | .ok docs =>
      let mediaType := fun (doc : XProc31.Document) =>
        ((doc.contentType.splitOn ";").headD doc.contentType).trimAscii.toString
      if docs.any (fun doc =>
          let ct := mediaType doc
          !(ct.startsWith "text/") && ct != "application/xml" &&
          !(ct.endsWith "+xml") && ct != "application/json" && !(ct.endsWith "+json")) then
        IO.eprintln "UNSUPPORTED CLI serialization: binary result document"
        return 2
      for doc in docs do
        let ct := mediaType doc
        if ct == "application/json" || ct.endsWith "+json" then
          let env := XProc31.xpathEnv (some doc)
          match env.serializeWith {method := "json"} (env.ctx.getD []) with
          | .ok text => IO.println text
          | .error e => IO.eprintln ("ERROR " ++ e.code ++ ": " ++ e.msg); return 1
        else if ct.startsWith "text/" && ct != "text/xml" && ct != "text/html" then
          IO.println doc.node.textContent
        else
          IO.println (String.join ((XProc31.documentNodes doc).map XML.Node.serialize))
      return 0
  catch e => IO.eprintln s!"ERROR IO: {e}"; return 1

def suite (o : Options) : IO UInt32 := do
  let paths := ((← files 100 o.root).filter (fun p => o.filter == "" || (p.splitOn o.filter).length > 1)).mergeSort (· ≤ ·)
  let exe := (← IO.appPath).toString
  let mut total : Counts := {}
  let mut features : List (String × Counts) := []
  for path in paths do
    let root ← loadXml path
    if let .ok n := root then
      if tag n != "test" then continue
    let result ← isolated exe path o.timeoutMs
    total := total.add result
    let fs ← match root with
      | .ok n => testFeatures path n
      | .error _ => pure ["fixture-xml"]
    for f in fs do
      let c := (features.lookup f).getD {}
      features := (f, c.add result) :: features.filter (·.1 != f)
    match result with
    | .fail m => if o.listFails then IO.println s!"FAIL {path}: {m}"
    | .unsupported m => if o.listUnsupported then IO.println s!"UNSUPPORTED {path}: {m}"
    | .pass => pure ()
  for (f, c) in features.mergeSort (fun a b => a.1 ≤ b.1) do
    IO.println s!"FEATURE {f}: {c.show}"
  IO.println s!"TOTAL {total.show}"
  pure (if total.fail > 0 then 1 else 0)

-- Oracle regressions: a false assertion must fail; a namespace mismatch must
-- fail even when the local error name is identical.
#guard (checkSchema
  (.element "s:schema" [] [.element "s:pattern" [] [
    .element "s:rule" [{name := "context", value := "/"}] [
      .element "s:assert" [{name := "test", value := "false()"}] []]]])
  { node := .element "doc" [] [] }).code == 1
#guard (checkSchema
  (.element "s:schema" [{name := "xmlns", value := "http://www.w3.org/1999/xhtml"}] [.element "s:pattern" [] [
    .element "s:rule" [{name := "context", value := "/"}] [
      .element "s:assert" [{name := "test", value := "count(/doc) = 1"}] []]]])
  { node := .element "doc" [] [] }).code == 0
#guard !expectedCode (.element "t:test"
  [{name := "xmlns:e", value := "urn:expected"}, {name := "code", value := "e:oops"}] [])
  "Q{urn:other}oops"

#guard (checkSchema (.element "s:schema" [] [])
  { node := .element "doc" [] [] }).code == 2
#guard (checkSchema
  (.element "s:schema" [] [.element "s:pattern" [] [
    .element "s:rule" [{name := "context", value := "missing"}] [
      .element "s:assert" [{name := "test", value := "true()"}] []]]])
  { node := .element "doc" [] [] }).code == 2
#guard (checkSchema
  (.element "s:schema" [] [.element "s:pattern" [] [
    .element "s:rule" [{name := "context", value := "/"}] [
      .element "s:assert" [{name := "test", value := "true()"}] [],
      .element "s:assert" [{name := "test", value := "false()"}] []]]])
  { node := .element "doc" [] [] }).code == 1
#guard (checkSchema
  (.element "s:schema" [] [.element "s:pattern" [] [
    .element "s:rule" [{name := "context", value := "/"}] [
      .element "s:report" [{name := "test", value := "true()"}] []]]])
  { node := .element "doc" [] [] }).code == 1
#guard (checkSchema
  (.element "s:schema" [] [.element "s:pattern" [] [
    .element "s:rule" [{name := "context", value := "/"}] [
      .element "s:assert" [{name := "test", value := "count(*) = 2"}] []]]])
  { node := .element "#document" [] [.element "a" [] [], .element "b" [] []] }).code == 0

#guard pipelineFeatures 20 (XProc31.inheritNS 20 []
  (.element "p:declare-step" [{name := "xmlns:p", value := "http://www.w3.org/ns/xproc"}] [
    .element "p:identity" [] [.element "p:with-input" [] [
      .element "p:delete" [] []]]])) == ["p:identity"]
#guard (pipelineArguments ["--option", "x=1=1"] []).toOption == some [("x", "1=1")]
#guard (pipelineArguments ["--option", "=1"] []).toBool == false

end L4Factoidal.XProc31.Runner

open L4Factoidal.XProc31.Runner in
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--scale-test"] => L4Factoidal.XProc31.Regression.scaling
  | ["--self-test"] => L4Factoidal.XProc31.Regression.run
  | ["--help"] =>
    IO.println "l4xproc --self-test | --scale-test"
    IO.println "l4xproc --pipeline FILE [--write-root DIR] [--option NAME=XPath]..."
    IO.println "l4xproc [--root TESTS] [--filter TEXT] [--timeout-ms N] [--list-fails] [--list-unsupported]"
    IO.println "Feature counts overlap when a test exercises several pipeline steps."
    pure 0
  | "--pipeline" :: path :: "--write-root" :: root :: rest =>
    match pipelineArguments rest [] with
    | .error message => IO.eprintln message; pure 2
    | .ok options => runFile path options (some root)
  | "--pipeline" :: path :: rest =>
    match pipelineArguments rest [] with
    | .error message => IO.eprintln message; pure 2
    | .ok options => runFile path options
  | ["--one", path] =>
    let result ← try runTest path catch e => pure (.fail s!"runner exception: {e}")
    IO.println result.message
    pure result.code
  | ["--one-sandbox", path, sandbox] =>
    let result ← try runTestIn path sandbox catch e => pure (.fail s!"runner exception: {e}")
    IO.println result.message
    pure result.code
  | _ =>
    match parseOptions args {} with
    | .error m => IO.eprintln m; pure 2
    | .ok options => suite options
