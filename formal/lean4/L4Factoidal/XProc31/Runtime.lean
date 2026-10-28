import L4Factoidal.XProc31.Core
import L4Factoidal.XProc31.Static
import L4Factoidal.XProc31.Atomic
import L4Factoidal.XProc31.Viewport
import L4Factoidal.XProc31.Sequence
import L4Factoidal.XProc31.Functions
import L4Factoidal.Syntax.IriResolve
import L4Factoidal.RDF.IriSyntax
import L4Factoidal.XML.Encoding

namespace L4Factoidal.XProc31
open XML

abbrev Bindings := List (String × List Document)
structure RunContext where
  values : Bindings := []
  vars : List (XPath4.QN × XPath4.Seq) := []
  baseUri : String := ""
  declarations : List Node := []
  position : Nat := 1
  size : Nat := 1
  inputPorts : Bindings := []

def standardAvailable (q : XPath4.QN) : Bool :=
  q.uri == "http://www.w3.org/ns/xproc" &&
    (supportedAtomic q.loc || ["group", "for-each", "viewport", "choose", "if", "try", "load"].contains q.loc)

def procHost (docs : List Document) (position size : Nat) (q : XPath4.QN) (_arity : Nat) : Option XPath4.HostFn :=
  if q.uri != "http://www.w3.org/ns/xproc" then none else
  match q.loc with
  | "iteration-position" => some (fun _ _ => pure (XPath4.sInt position))
  | "iteration-size" => some (fun _ _ => pure (XPath4.sInt size))
  | "document-properties" => some (fun _ _ => do
      let some d := docs.head? | XPath4.err "XD0001" "document context absent"
      pure [.map [(XPath4.Atomic.ofStr "content-type", XPath4.sStr d.contentType),
        (XPath4.Atomic.ofStr "base-uri", XPath4.sStr d.baseUri)]])
  | "document-property" => some (fun _ args => do
      let some d := docs.head? | XPath4.err "XD0001" "document context absent"
      let key := XPath4.showSeq (args[1]?.getD [])
      pure (if key == "content-type" then XPath4.sStr d.contentType else if key == "base-uri" then XPath4.sStr d.baseUri else []))
  | _ => xprocFunction q _arity standardAvailable

def contextEnv (ctx : RunContext) (step : Node) (docs : List Document) : XPath4.Env :=
  { (xpathEnv docs.head? ctx.vars (ns step) ctx.position ctx.size) with
    baseUri := ctx.baseUri
    host := fun q arity =>
      if q.uri == "http://www.w3.org/ns/xproc" && q.loc == "step-available" then
        xprocFunction q arity (fun name => standardAvailable name || ctx.declarations.any (fun d =>
          let (p,l) := XPath4.splitName (attr d "type")
          l == name.loc && ((ns d).lookup p).getD "" == name.uri && (kids d).any isPipelineStep))
      else procHost docs ctx.position ctx.size q arity }

def qname (n : Node) (name : String) : XPath4.QN :=
  let (p,l) := XPath4.splitName name
  { pfx := p, loc := l, uri := if p == "" then "" else ((ns n).lookup p).getD "" }

def resolvePath (base ref : String) : String :=
  Syntax.resolveIri base ref

def readDocument (uri contentType : String) : IO (Result Document) := do
  if uri.startsWith "http:" || uri.startsWith "https:" then return unsupported "network document loading"
  let path := if uri.startsWith "file://" then (uri.drop 7).toString else uri
  let ct := if contentType != "" then contentType else
    if path.endsWith ".txt" then "text/plain" else if path.endsWith ".json" then "application/json"
    else if path.endsWith ".html" then "text/html" else "application/xml"
  if [".zip", ".gz", ".png", ".jpg", ".pdf"].any (fun ext => path.endsWith ext) then return unsupported "binary document representation"
  try
    let bytes ← IO.FS.readBinFile path
    if (ct.startsWith "text/" && ct != "text/xml" && ct != "text/html") || ct == "application/json" then
      match String.fromUTF8? bytes with
      | none => return error "XD0011" "invalid UTF-8 text document"
      | some text => return .ok ⟨.text text, ct, uri, []⟩
    match XML.parseXMLBytes bytes with
    | .ok d => return .ok ⟨d.root, ct, uri, []⟩
    | .error e => return error "XD0011" (toString e)
  catch e => return error "XD0011" (toString e)

def lookupPipe (ctx : RunContext) (s : String) : Result (List Document) :=
  let parts := s.trimAscii.toString.splitOn "@"
  let key := match parts with | [port, step] => step ++ "/" ++ (if port == "" then "result" else port) | [step] => step ++ "/result" | _ => s
  match ctx.values.lookup key with
  | some ds => pure ds
  | none => unsupported ("unresolved port connection " ++ key)

def expandInline (env : XPath4.Env) : Nat → Bool → Node → Result Node
  | 0, _, _ => unsupported "inline tree depth limit"
  | _+1, enabled, .text t => do
    let t ← if enabled then avt t env else pure t
    pure (.text t)
  | _+1, enabled, .cdata t => do
    let t ← if enabled then avt t env else pure t
    pure (.text t)
  | f+1, enabled, .element name ats cs => do
    let control := (XML.findAttr "p:expand-text" ats).getD ""
    let enabled := if control == "false" then false else if control == "true" then true else enabled
    let ats ← (ats.filter (fun a => a.name != "p:expand-text")).mapM fun a => do
      if a.name == "xmlns" || a.name.startsWith "xmlns:" || !enabled then pure a
      else pure {a with value := ← avt a.value env}
    pure (.element name ats (← cs.mapM (expandInline env f enabled)))
  | _, _, n => pure n

def applyProperties (env : XPath4.Env) (n : Node) (d : Document) : Result Document := do
  let expr := attr n "document-properties" (attr n "p:document-properties")
  if expr == "" then pure d else
  let value ← eval expr env
  let [.map entries] := value | error "XD0070" "document-properties must be a map"
  let mut d := d
  for (key,value) in entries do
    let text := seqString env value
    if key.str == "base-uri" then
      if !RDF.isAbsoluteIri text then return ← error "XD0064" "base-uri must be an absolute URI"
      d := {d with baseUri := text}
    else if key.str == "content-type" then d := {d with contentType := text}
    else return ← unsupported ("document property " ++ key.str)
  pure d

def inlineDoc (ctx : RunContext) (n : Node) (defaultDocs : List Document) : Result Document := do
  let env := contextEnv ctx n defaultDocs
  let ct := attr n "content-type" "application/xml"
  let enabled := attr n "expand-text" "true" != "false"
  if ct.startsWith "text/" && ct != "text/xml" && ct != "text/html" then
    let text ← if enabled then avt n.textContent env else pure n.textContent
    pure ⟨.text text, ct, ctx.baseUri, []⟩
  else if ct == "application/json" then
    let text ← if enabled then avt n.textContent env else pure n.textContent
    let _ ← eval "parse-json($raw)" { env with vars := (⟨"", "raw", ""⟩, XPath4.sStr text) :: env.vars }
    pure ⟨.text text, ct, ctx.baseUri, []⟩
  else
    let cs := (children n).filter fun c => match c with
      | .text s => !s.trimAscii.toString.isEmpty | _ => true
    let cs ← cs.mapM (expandInline env 4096 enabled)
    let root := match cs with | [c] => c | cs => .element "#document" [] cs
    applyProperties env n ⟨root, ct, ctx.baseUri, []⟩

def binding (ctx : RunContext) (n : Node) (defaultDocs : List Document) : IO (Result (List Document)) := do
  let ctx := if attr n "xml:base" == "" then ctx else {ctx with baseUri := resolvePath ctx.baseUri (attr n "xml:base")}
  let env := contextEnv ctx n defaultDocs
  let result ← (do
    if attr n "pipe" != "" then
      return (((((attr n "pipe").replace "\n" " ").replace "\t" " ").replace "\r" " ").splitOn " ").filter (· != "") |>.foldlM (fun out p => do pure (out ++ (← lookupPipe ctx p))) []
    if attr n "href" != "" then
      match avt (attr n "href") env with
      | .error e => return .error e
      | .ok uri => return (← readDocument (resolvePath ctx.baseUri uri) (attr n "content-type")).map List.singleton
    if (kids n).isEmpty then return .ok defaultDocs
    let mut out := []
    for c in kids n do
      let r ← match (if ((ns c).lookup (XPath4.splitName (c.elementTag.getD "")).1).getD "" == "http://www.w3.org/ns/xproc" then tag c else "#literal") with
        | "empty" => pure (.ok [])
        | "pipe" => pure (lookupPipe ctx (attr c "port" "result" ++ "@" ++ attr c "step"))
        | "document" =>
          match avt (attr c "href") env with
          | .error e => pure (.error e)
          | .ok uri => do pure ((← readDocument (resolvePath ctx.baseUri uri) (attr c "content-type")).map List.singleton)
        | "inline" => pure ((inlineDoc ctx c defaultDocs).map List.singleton)
        | _ => pure (do
          let c ← expandInline env 4096 (attr n "expand-text" "true" != "false") c
          let d ← applyProperties env c ⟨c, "application/xml", ctx.baseUri, []⟩
          pure [d])
      match r with
      | .error e => return .error e
      | .ok ds => out := out ++ ds
    return .ok out : IO (Result (List Document)))
  match result with
  | .error e => return .error e
  | .ok docs =>
    if attr n "select" == "" then return .ok docs
    return docs.foldlM (fun out d => do
      let env := contextEnv ctx n [d]
      let seq ← eval (attr n "select") env
      pure (out ++ (← seqDocuments env seq d.baseUri))) []

def stepPorts (ctx : RunContext) (step : Node) (docs : List Document) : IO (Result Bindings) := do
  let mut ports := [("source", docs)]
  for n in named step "with-input" do
    let port := attr n "port" "source"
    match ← binding ctx n (if port == "source" then docs else []) with
    | .error e => return .error e
    | .ok ds => ports := (port, ds) :: ports.filter (fun p => p.1 != port)
  return .ok ports

def typedValue (declaration : Node) (env : XPath4.Env) (value : XPath4.Seq) : Result XPath4.Seq := do
  let ty := attr declaration "as"
  if ty == "" then pure value else
  let ty ← fromXPath (XPath4.parseSeqType ty)
  (fromXPath (env.castSeqF 128 value ty)).mapError (fun e => {e with code := "XD0036"})

def declarationTag (s : String) : Bool :=
  ["input", "output", "option", "import", "declare-step", "documentation", "pipeinfo", "serialization"].contains s

mutual

def runBody : Nat → RunContext → Node → List Document → IO (Result (List Document))
  | 0, _, _, _ => pure (unsupported "pipeline call depth limit")
  | fuel+1, ctx0, pipeline, initial => do
    let mut ctx := if attr pipeline "xml:base" == "" then ctx0 else {ctx0 with baseUri := resolvePath ctx0.baseUri (attr pipeline "xml:base")}
    let mut docs := initial
    let inputDecls := named pipeline "input"
    let primaryInput := (inputDecls.find? (fun n => attr n "primary" == "true")).orElse
      (fun _ => inputDecls.head?)
    for input in inputDecls do
      let port := attr input "port" "source"
      let isPrimary := primaryInput.any (fun n => attr n "port" "source" == port) && attr input "primary" != "false"
      let bound ← match ctx.inputPorts.lookup port with
        | some ds => pure (.ok ds)
        | none => if isPrimary && !initial.isEmpty then pure (.ok initial) else binding ctx input []
      let .ok bound := bound | return bound
      if attr input "sequence" "false" != "true" && bound.length != 1 then
        return error "XD0006" "input requires exactly one document"
      if isPrimary then docs := bound
      let key := attr pipeline "name" ++ "/" ++ port
      ctx := { ctx with values := (key, bound) :: ctx.values }
    ctx := {ctx with inputPorts := []}
    ctx := { ctx with declarations := named pipeline "declare-step" ++ ctx.declarations }
    for opt in named pipeline "option" do
      let q := qname opt (attr opt "name")
      if !(ctx.vars.any (fun p => p.1 == q)) then
        if attr opt "select" == "" then
          if attr opt "required" == "true" then return error "XS0018" "required option missing"
        else
          match eval (attr opt "select") (contextEnv ctx opt docs) with
          | .error e => return .error e
          | .ok v => ctx := { ctx with vars := (q,v) :: ctx.vars }
    for opt in named pipeline "option" do
      let q := qname opt (attr opt "name")
      if let some value := ctx.vars.lookup q then
        match typedValue opt (contextEnv ctx opt docs) value with
        | .error e => return .error e
        | .ok value => ctx := {ctx with vars := (q,value) :: ctx.vars.filter (fun p => p.1 != q)}
    let initial := docs
    let hasVariables := !(named pipeline "variable").isEmpty
    let executable := (kids pipeline).filter isPipelineStep
    let jobs := if hasVariables then (kids pipeline).zipIdx else
      ((orderConnections (pipelineConnections pipeline)).getD (List.range executable.length)).filterMap
        (fun i => (executable[i]?).map (fun n => (n,i)))
    for (step, stepIndex) in jobs do
      if !hasVariables then
        docs := if stepIndex == 0 then initial else
          (ctx.values.lookup ("#auto" ++ toString (stepIndex-1))).getD initial
      let t := tag step
      if declarationTag t then continue
      if t == "variable" then
        let variableDocs ← match ← stepPorts ctx step docs with
          | .error e => return .error e
          | .ok ps => pure ((ps.lookup "source").getD [])
        match eval (attr step "select") (contextEnv ctx step variableDocs) with
        | .error e => return .error e
        | .ok v =>
          match typedValue step (contextEnv ctx step variableDocs) v with
          | .error e => return .error e
          | .ok v => ctx := {ctx with vars := (qname step (attr step "name"),v) :: ctx.vars}
        continue
      let enabled := if attr step "use-when" == "" then .ok true else evalBool (attr step "use-when") (contextEnv ctx step [])
      match enabled with
      | .error e => return .error e
      | .ok false => continue
      | .ok true => pure ()
      match ← runStep fuel ctx step docs with
      | .error e => return .error e
      | .ok result =>
        docs := result
        ctx := {ctx with values := ("#auto" ++ toString stepIndex, docs) :: ctx.values}
        if attr step "name" != "" then
          let outputs := named step "output"
          let primaryName := if let some o := (outputs.find? (fun o => attr o "primary" == "true")).orElse (fun _ => outputs.head?) then attr o "port" "result" else "result"
          ctx := {ctx with values := (attr step "name" ++ "/" ++ primaryName, docs) :: (attr step "name" ++ "/result", docs) :: ctx.values}
    if !hasVariables && !executable.isEmpty then
      docs := (ctx.values.lookup ("#auto" ++ toString (executable.length-1))).getD docs
    let outputs := named pipeline "output"
    if outputs.isEmpty then return .ok docs
    let output := (outputs.find? (fun n => attr n "primary" == "true")).getD outputs.head!
    let result ← if attr output "pipe" != "" || !(kids output).isEmpty then binding ctx output docs
      else pure (.ok docs)
    match result with
    | .error e => return .error e
    | .ok ds =>
      if attr output "sequence" "false" != "true" && ds.length != 1 then
        return error "XD0007" "output requires exactly one document"
      return .ok ds

def runStep : Nat → RunContext → Node → List Document → IO (Result (List Document))
  | 0, _, _, _ => pure (unsupported "compound step depth limit")
  | fuel+1, ctx, step, defaultDocs => do
    let ctx := if attr step "xml:base" == "" then ctx else {ctx with baseUri := resolvePath ctx.baseUri (attr step "xml:base")}
    if !supportedAtomic (tag step) && !(["group", "for-each", "viewport", "if", "choose", "try", "load", "with-input"].contains (tag step)) &&
        !(ctx.declarations.any (fun d => qname d (attr d "type") == qname step (step.elementTag.getD ""))) then
      return unsupported ("step " ++ step.elementTag.getD "")
    let ports ← stepPorts ctx step defaultDocs
    let .ok ports := ports | return ports.map (fun _ => [])
    let docs := (ports.lookup "source").getD []
    let env := contextEnv ctx step (if ["choose", "if", "for-each", "viewport", "group", "try"].contains (tag step) then docs else defaultDocs)
    match tag step with
    | "group" => runBody fuel ctx step docs
    | "viewport" =>
      viewportStepWithFocus step docs env (fun pos size current =>
        runBody fuel {ctx with position := pos, size := size, values := ("/current", [current]) :: (attr step "name" ++ "/current", [current]) :: ctx.values} step [current])
    | "for-each" =>
      forEachIO docs (fun pos size doc =>
        runBody fuel {ctx with position := pos, size := size, values := ("/current", [doc]) :: (attr step "name" ++ "/current", [doc]) :: ctx.values} step [doc])
    | "if" =>
      if docs.length > 1 then return error "XD0001" "XPath context requires one document"
      match evalBool (attr step "test") env with
      | .error e => return .error e
      | .ok true => runBody fuel ctx step docs
      | .ok false => return .ok []
    | "choose" =>
      if docs.length > 1 then return error "XD0001" "XPath context requires one document"
      for branch in kids step do
        if tag branch == "otherwise" then return ← runBody fuel ctx branch docs
        if tag branch == "when" then
          let branchDocs ← match ← stepPorts ctx branch docs with
            | .error e => return .error e
            | .ok ps => pure ((ps.lookup "source").getD [])
          if branchDocs.length > 1 then return error "XD0001" "XPath context requires one document"
          match evalBool (attr branch "test") (contextEnv ctx branch branchDocs) with
          | .error e => return .error e
          | .ok true => return ← runBody fuel ctx branch docs
          | .ok false => pure ()
      return .ok []
    | "try" =>
      let body := .element "p:group" step.elementAttrs ((children step).filter (fun n => !["catch", "finally"].contains (tag n)))
      let result ← runBody fuel ctx body docs
      let result ← match result with
        | .ok ds => pure (.ok ds)
        | .error e =>
          if e.unsupported then pure (.error e)
          else match (named step "catch").find? (fun c => attr c "code" == "" || ((attr c "code").splitOn " ").any (fun s => localName s == e.code)) with
            | none => pure (.error e)
            | some c => runBody fuel ctx c [⟨.element "c:errors" [{name := "xmlns:c", value := "http://www.w3.org/ns/xproc-step"}] [.element "c:error" [{name := "code", value := e.code}] [.text e.message]], "application/xml", ctx.baseUri, []⟩]
      if !(named step "finally").isEmpty then return unsupported "finally output merging"
      return result
    | "load" =>
      match option step "href" env with
      | .error e => return .error e
      | .ok href => return (← readDocument (resolvePath ctx.baseUri href) (attr step "content-type")).map List.singleton
    | "with-input" => return .ok docs
    | _ =>
      match ctx.declarations.find? (fun d => qname d (attr d "type") == qname step (step.elementTag.getD "")) with
      | some declaration =>
        let mut vars := ctx.vars
        for opt in named declaration "option" do
          let name := attr opt "name"
          let q := qname opt name
          if attr step name != "" then
            match avt (attr step name) env with
            | .error e => return .error e
            | .ok text => vars := (q, XPath4.sStr text) :: vars.filter (fun p => p.1 != q)
          else if let some binding := (named step "with-option").find? (fun n => attr n "name" == name) then
            match eval (attr binding "select") env with
            | .error e => return .error e
            | .ok value => vars := (q,value) :: vars.filter (fun p => p.1 != q)
        runBody fuel {ctx with vars, inputPorts := ports} declaration docs
      | none =>
        let (pfx, _) := XPath4.splitName (step.elementTag.getD "")
        if ((ns step).lookup pfx).getD "" != "http://www.w3.org/ns/xproc" then
          return unsupported ("extension step " ++ step.elementTag.getD "")
        atomic step ports env
end

def pruneUseWhen (vars : List (XPath4.QN × XPath4.Seq)) : Nat → Node → Result (Option Node)
  | 0, _ => unsupported "static tree depth limit"
  | fuel+1, node => do
    let env := { (xpathEnv none vars (ns node)) with host := procHost [] 1 1 }
    if attr node "use-when" != "" then
      if !(← evalBool (attr node "use-when") env) then return none
    if tag node == "inline" || tag node == "documentation" || tag node == "pipeinfo" then return some node
    match node with
    | .element name ats cs =>
      let mut out := []
      for c in cs do
        if let some c ← pruneUseWhen vars fuel c then out := c :: out
      pure (some (.element name (ats.filter (fun a => a.name != "use-when")) out.reverse))
    | n => pure (some n)

def loadLibraries : Nat → String → Node → IO (Result (List Node))
  | 0, _, _ => pure (unsupported "library import depth limit")
  | fuel+1, base, pipeline => do
    let mut declarations := []
    for imp in named pipeline "import" do
      let uri := resolvePath base (attr imp "href")
      match ← readDocument uri "application/xml" with
      | .error e => return .error e
      | .ok d =>
        let library := inheritNS 4096 [] d.node
        match ← loadLibraries fuel uri library with
        | .error e => return .error e
        | .ok ds => declarations := declarations ++ ds
        if tag library == "declare-step" then declarations := declarations ++ [library]
        else declarations := declarations ++ named library "declare-step"
    return .ok declarations

def runPipeline (pipeline : Node) (inputs : List Document := []) (baseUri : String := "")
    (options : List (String × String) := []) : IO (Result (List Document)) := do
  let pipeline := inheritNS 4096 [] pipeline
  if attr pipeline "version" == "3.2" then return unsupported "XProc 3.2 pipeline"
  let mut vars := []
  for (name,expr) in options do
    match eval expr (xpathEnv inputs.head? vars (ns pipeline)) with
    | .error e => return .error e
    | .ok v => vars := (qname pipeline name,v) :: vars
  for opt in named pipeline "option" do
    if attr opt "static" == "true" && !(vars.any (fun p => p.1 == qname opt (attr opt "name"))) then
      match eval (attr opt "select" "()") (xpathEnv none vars (ns opt)) with
      | .error e => return .error e
      | .ok v => vars := (qname opt (attr opt "name"),v) :: vars
  let pipeline ← match pruneUseWhen vars 4096 pipeline with
    | .error e => return .error e
    | .ok none => return error "XS0052" "pipeline excluded by use-when"
    | .ok (some n) => pure n
  let issues := staticErrors pipeline
  if let some (code,msg) := issues.head? then return error code msg
  let declarations ← match ← loadLibraries 32 baseUri pipeline with
    | .error e => return .error e
    | .ok ds => pure ds
  runBody 256 {vars, baseUri, declarations} pipeline inputs

end L4Factoidal.XProc31
