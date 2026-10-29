import L4Factoidal.XProc31.Core
import L4Factoidal.XProc31.Static
import L4Factoidal.XProc31.Atomic
import L4Factoidal.XProc31.Viewport
import L4Factoidal.XProc31.Sequence
import L4Factoidal.XProc31.Functions
import L4Factoidal.XProc31.ExtraSteps
import L4Factoidal.XProc31.Loading
import L4Factoidal.XProc31.FileSteps
import L4Factoidal.Syntax.IriResolve
import L4Factoidal.RDF.IriSyntax
import L4Factoidal.XML.Encoding

namespace L4Factoidal.XProc31
open XML

def pTag (node : Node) : String :=
  let (p,l) := XPath4.splitName (node.elementTag.getD "")
  if ((ns node).lookup p).getD "" == "http://www.w3.org/ns/xproc" then l else ""
def pNamed (node : Node) (loc : String) : List Node :=
  (kids node).filter (fun n => pTag n == loc)
def xpAttribute (node : Node) (loc : String) : Option XML.Attribute :=
  node.elementAttrs.find? fun a =>
    let (p,l) := XPath4.splitName a.name
    p != "" && l == loc && ((ns node).lookup p).getD "" == "http://www.w3.org/ns/xproc"

abbrev Bindings := List (String × List Document)
structure StepOutput where
  primary : List Document
  ports : Bindings

def primaryOutput (docs : List Document) : StepOutput := ⟨docs, [("result", docs)]⟩
def withPrimary (action : IO (Result (List Document))) : IO (Result StepOutput) := do
  pure ((← action).map primaryOutput)
def primaryOnly (action : IO (Result StepOutput)) : IO (Result (List Document)) := do
  pure ((← action).map (·.primary))

structure RunContext where
  values : Bindings := []
  vars : List (XPath4.QN × XPath4.Seq) := []
  staticVars : List (XPath4.QN × XPath4.Seq) := []
  baseUri : String := ""
  declarations : List Node := []
  position : Nat := 1
  size : Nat := 1
  inputPorts : Bindings := []
  expandText : Bool := true
  propertyDocs : List (Nat × Document) := []
  writeRoot : Option String := none
  excludedInlinePrefixes : List String := ["http://www.w3.org/ns/xproc"]

/-- Resolve exclusion controls before expansion; the resulting namespace URIs
are applied only after XPath expressions have used the original bindings. -/
def inlineExclusions (ctx : RunContext) (node : Node) : List String :=
  let control := attr node "exclude-inline-prefixes"
    (((xpAttribute node "exclude-inline-prefixes").map (·.value)).getD "")
  let words := (((control.replace "\n" " ").replace "\r" " ").replace "\t" " ").splitOn " "
  (ctx.excludedInlinePrefixes ++ words.filterMap (fun word =>
    if word == "#all" then some "#all"
    else if word == "" then none
    else (ns node).lookup (if word == "#default" then "" else word))).eraseDups

def excludeInlineNamespaces (excluded : List String) : Nat → List (String × String) → Node → Node
  | 0, _, node => node
  | fuel+1, inherited, .element name ats cs =>
    let used := (XPath4.splitName name).1 :: (ats.filterMap fun a =>
      if a.name == "xmlns" || a.name.startsWith "xmlns:" then none
      else let p := (XPath4.splitName a.name).1; if p == "" then none else some p)
    let ats := ats.filter fun a =>
      if a.name == "xmlns" || a.name.startsWith "xmlns:" then
        let p := if a.name == "xmlns" then "" else (a.name.drop 6).toString
        let removed := (excluded.contains "#all" || excluded.contains a.value) && !used.contains p
        !removed && (inherited.lookup p).getD "" != a.value
      else true
    let bindings := ns (.element name ats []) ++ inherited
    .element name ats (cs.map (excludeInlineNamespaces excluded fuel bindings))
  | _, _, node => node

#guard (excludeInlineNamespaces ["#all"] 8 []
  (.element "a:root" [{name := "xmlns:a", value := "urn:a"}, {name := "xmlns:b", value := "urn:b"}]
    [.element "b:child" [{name := "xmlns:a", value := "urn:a"}, {name := "xmlns:b", value := "urn:b"}] []])).serialize ==
  "<a:root xmlns:a=\"urn:a\"><b:child xmlns:b=\"urn:b\"/></a:root>"
#guard (excludeInlineNamespaces ["urn:default"] 8 []
  (.element "root" [{name := "xmlns", value := "urn:default"}] [])).elementAttrs.length == 1

def pipelineError (e : ProcError) : ProcError :=
  if e.unsupported || e.code.startsWith "XS" || e.code.startsWith "XD" || e.code.startsWith "XC" || e.code.startsWith "Q{" then e
  else if e.code.startsWith "XPST" || e.code.startsWith "XQST" then {e with code := "XS0107"}
  else if e.code.startsWith "FO" || e.code.startsWith "XP" || e.code.startsWith "XQ" then {e with code := "XD0030"}
  else e

/-- Retained variable documents have stable identities for document-property lookup. -/
def retainVariable (env : XPath4.Env) (id : Nat) : Nat → XPath4.Seq → XPath4.Seq
  | 0, values => values
  | fuel+1, values => values.map fun item => match item with
    | .node n => if n.rt.isSome then item else .node {n with doc := id, rt := some (env.doc n)}
    | .map entries => .map (entries.map (fun (k,v) => (k,retainVariable env id fuel v)))
    | .arr members => .arr (members.map (retainVariable env id fuel))
    | _ => item

def standardAvailable (q : XPath4.QN) : Bool :=
  q.uri == "http://www.w3.org/ns/xproc" &&
    (supportedAtomic q.loc || supportsExtra q.loc || supportsFile q.loc || ["group", "for-each", "viewport", "choose", "if", "try", "load", "run", "split-sequence"].contains q.loc)

def procHost (docs : List Document) (position size : Nat) (q : XPath4.QN) (_arity : Nat) : Option XPath4.HostFn :=
  if q.uri != "http://www.w3.org/ns/xproc" then none else
  match q.loc with
  | "iteration-position" => some (fun _ _ => pure (XPath4.sInt position))
  | "iteration-size" => some (fun _ _ => pure (XPath4.sInt size))
  | "document-properties" => some (fun _ args => do
      match args[0]?.getD [] with
      | [.atom _] => pure [.map []]
      | _ =>
        let some d := docs.head? | return [.map []]
        pure [.map (documentProperties d)])
  | "document-property" => some (fun c args => do
      let some d := docs.head? | XPath4.err "XD0001" "document context absent"
      let key ← functionQName {c with ns := c.ns.filter (fun p => p.1 != "")} (args[1]?.getD [])
      pure (documentProperty d key))
  | _ => xprocFunction q _arity standardAvailable

def qname (n : Node) (name : String) : XPath4.QN :=
  if name.startsWith "Q{" then
    match (name.drop 2).toString.splitOn "}" with
    | [uri,loc] => {uri, loc, pfx := ""}
    | _ => {uri := "", loc := name, pfx := ""}
  else
    let (p,l) := XPath4.splitName name
    { pfx := p, loc := l, uri := if p == "" then "" else ((ns n).lookup p).getD "" }

def contextEnv (ctx : RunContext) (step : Node) (docs : List Document) : XPath4.Env :=
  { (xpathEnv (if docs.length == 1 then docs.head? else none) ctx.vars (ns step) ctx.position ctx.size) with
    baseUri := ctx.baseUri
    host := fun q arity =>
      if q.uri == nsXProc && ["document-properties", "document-property"].contains q.loc then
        some (fun c args => do
          let saved := match args[0]?.getD [] with
            | [.node n] => if n.rt.isSome then ctx.propertyDocs.lookup n.doc else docs.head?
            | [.map _] | [.arr _] => docs.head?
            | [.atom _] => docs.head?.filter (fun d => d.value.isSome)
            | _ => none
          if q.loc == "document-properties" then return [.map (saved.map documentProperties |>.getD [])]
          let key ← functionQName {c with ns := c.ns.filter (fun p => p.1 != "")} (args[1]?.getD [])
          return saved.map (fun d => documentProperty d key) |>.getD [])
      else if q.uri == "http://www.w3.org/ns/xproc" && q.loc == "step-available" then
        xprocFunction q arity (fun name => standardAvailable name || ctx.declarations.any (fun d =>
          qname d (attr d "type") == name && (kids d).any isPipelineStep))
      else procHost docs ctx.position ctx.size q arity }

def resolvePath (base ref : String) : String :=
  Syntax.resolveIri base ref

def readDocument (uri contentType : String) : IO (Result Document) := loadDocument uri contentType

def loadWithProperties (uri : String) (step : Node) (env : XPath4.Env) : IO (Result Document) := do
  if !RDF.isAbsoluteIri uri then return error "XD0064" "invalid document URI"
  let properties := typedOption step "document-properties" env "map{}"
  let .ok properties := properties | return properties.map (fun _ => default)
  let .ok entries := normalizedProperties env properties | return error "XD0070" "invalid document properties"
  let media := entries.find? (fun p => propertyName p.1 == some ⟨"", "content-type", ""⟩)
  let ct ← match media with
    | none => pure (option step "content-type" env)
    | some (_, [.atom a]) => pure (.ok a.str)
    | _ => pure (error "XD0079" "content-type must be one media type")
  let .ok ct := ct | return ct.map (fun _ => default)
  if attr step "content-type" != "" && media.isSome && attr step "content-type" != ct then
    return error "XD0062" "content-type property conflicts with explicit content-type"
  if ct != "" then
    if let .error e := parseMediaType ct then return .error e
  let params := typedOption step "parameters" env "map{}"
  let .ok params := params | return params.map (fun _ => default)
  let validateDtd := match params with
    | [.map entries] => entries.any (fun (k,v) => k.str == "dtd-validate" && v.any (fun i => match i with | .atom a => a.str == "true" | _ => false))
    | _ => false
  match ← loadDocument uri ct validateDtd with
  | .error e => return .error e
  | .ok d => return updateProperties env d properties

def lookupPipe (ctx : RunContext) (s : String) : Result (List Document) :=
  let parts := s.trimAscii.toString.splitOn "@"
  let key := match parts with | [port, step] => step ++ "/" ++ (if port == "" then "#primary" else port) | [port] => if ctx.values.any (fun p => p.1 == "/" ++ port) then "/" ++ port else "#last/" ++ port | _ => s
  match ctx.values.lookup key with
  | some ds => pure ds
  | none => unsupported ("unresolved port connection " ++ key)

def inlineItems (env : XPath4.Env) (items : XPath4.Seq) : Result (List XML.Attribute × List Node) := do
  let mut ats := []
  let mut nodes := []
  let mut atomic := false
  for item in items do
    match item with
    | .atom a =>
      nodes := nodes ++ [.text ((if atomic then " " else "") ++ a.str)]
      atomic := true
    | .node ref =>
      let record := env.nrec ref
      if record.kind == .attribute then
        ats := ats ++ [{name := record.name.show, value := record.value}]
      else
        let node ← nodeFromRef env 4096 ref
        nodes := nodes ++ (if node.elementTag == some "#document" then children node else [node])
      atomic := false
    | _ => return ← error "XD0051" "text template contains a map, array or function"
  pure (ats,nodes)

def inlineTemplate (env : XPath4.Env) : Nat → List Char → List Char → List XML.Attribute → List Node → Result Node
  | 0, _, _, _, _ => unsupported "text template scanning limit"
  | _+1, [], text, ats, nodes => pure (.element "#document" ats (nodes ++ if text.isEmpty then [] else [.text (String.ofList text.reverse)]))
  | f+1, '{'::'{'::cs, text, ats, nodes => inlineTemplate env f cs ('{'::text) ats nodes
  | f+1, '}'::'}'::cs, text, ats, nodes => inlineTemplate env f cs ('}'::text) ats nodes
  | f+1, '{'::cs, text, ats, nodes => do
    let (expr,rest) ← scanAvtExpression (f+1) cs 0 none 0 []
    let values ← eval expr env
    let (moreAts,moreNodes) ← inlineItems env values
    inlineTemplate env f rest [] (ats ++ moreAts)
      (nodes ++ (if text.isEmpty then [] else [.text (String.ofList text.reverse)]) ++ moreNodes)
  | _+1, '}'::_, _, _, _ => error "XS0107" "unescaped closing brace in text template"
  | f+1, c::cs, text, ats, nodes => inlineTemplate env f cs (c::text) ats nodes

def expandInline (env : XPath4.Env) : Nat → Bool → Node → Result Node
  | 0, _, _ => unsupported "inline tree depth limit"
  | _+1, enabled, .text t => do
    if enabled then inlineTemplate env (t.length+1) t.toList [] [] [] else pure (.text t)
  | _+1, enabled, .cdata t => do
    if enabled then inlineTemplate env (t.length+1) t.toList [] [] [] else pure (.text t)
  | f+1, enabled, .element name ats cs => do
    let node := .element name ats cs
    let controlName := if pTag node != "" then "inline-expand-text"
      else ((xpAttribute node "inline-expand-text").map (·.name)).getD ""
    let control := (XML.findAttr controlName ats).getD ""
    let enabled := if control == "false" then false else if control == "true" then true else enabled
    let ats ← (ats.filter (fun a => a.name != controlName)).mapM fun a => do
      if a.name == "xmlns" || a.name.startsWith "xmlns:" || !enabled then pure a
      else pure {a with value := ← avt a.value env}
    let expanded ← cs.mapM (expandInline env f enabled)
    let addedAts := expanded.flatMap fun n => if n.elementTag == some "#document" then n.elementAttrs else []
    let content := expanded.flatMap fun n => if n.elementTag == some "#document" then children n else [n]
    pure (.element name (ats ++ addedAts) content)
  | _, _, n => pure n

def applyProperties (env : XPath4.Env) (n : Node) (d : Document) : Result Document := do
  let expr := attr n "document-properties" (attr n "p:document-properties")
  if expr == "" then pure d else
  updateProperties env d (← eval expr env)

def inlineDoc (ctx : RunContext) (n : Node) (defaultDocs : List Document) : Result Document := do
  let ctx := if attr n "xml:base" == "" then ctx else {ctx with baseUri := resolvePath ctx.baseUri (attr n "xml:base")}
  let env := contextEnv ctx n defaultDocs
  let ct := attr n "content-type" "application/xml"
  let media ← parseMediaType ct
  let encoding := attr n "encoding"
  if encoding != "" && encoding != "base64" then error "XS0069" "unknown inline encoding" else pure ()
  if encoding != "" && (media.kind == .xml || media.kind == .html) then
    error "XD0054" "XML and HTML inline content cannot have an encoding" else pure ()
  if encoding == "" && (media.parameters.lookup "charset").isSome then
    error "XD0055" "unencoded inline content cannot declare a charset" else pure ()
  if encoding != "" && !(kids n).isEmpty then error "XD0056" "encoded inline content contains markup" else pure ()
  let enabled := attr n "expand-text" (if ctx.expandText then "true" else "false") != "false"
  if media.kind == .text || media.kind == .json || media.kind == .binary then
    let text ← if encoding == "base64" then do
        let some bytes := XSD.parseBase64Lex n.textContent | error "XD0040" "invalid base64 inline content"
        if media.kind == .binary then unsupported "binary inline documents" else pure ()
        (decodeDocumentText ⟨(bytes.map UInt8.ofNat).toArray⟩ (media.parameters.lookup "charset")).mapError
          (fun e => {e with code := if e.code == "XD0060" then "XD0039" else "XD0040"})
      else if enabled then do
        let expanded ← inlineTemplate env (n.textContent.length+1) n.textContent.toList [] [] []
        if !expanded.elementAttrs.isEmpty then error "XD0084" "attribute in text inline document"
        else pure expanded.textContent
      else pure n.textContent
    if media.kind == .binary then unsupported "binary inline documents" else pure ()
    if media.kind == .json then
      let value ← (eval "parse-json($raw)" { env with vars := (⟨"", "raw", ""⟩, XPath4.sStr text) :: env.vars }).mapError
        (fun e => {e with code := "XD0057"})
      applyProperties env n {node := .text text, contentType := ct, baseUri := ctx.baseUri, value := some value}
    else applyProperties env n {node := .text text, contentType := ct, baseUri := ctx.baseUri}
  else
    let cs := (children n).filter fun c => match c with
      | .text s => !s.trimAscii.toString.isEmpty | _ => true
    let cs ← cs.mapM (expandInline env 4096 enabled)
    let cs := cs.flatMap fun c => if c.elementTag == some "#document" then children c else [c]
    let root := match cs with | [c] => c | cs => .element "#document" [] cs
    let root := excludeInlineNamespaces (inlineExclusions ctx n) 4096 [] root
    applyProperties env n ⟨root, ct, ctx.baseUri, [], none⟩

def binding (ctx : RunContext) (n : Node) (defaultDocs : List Document) : IO (Result (List Document)) := do
  let ctx := if attr n "xml:base" == "" then ctx else {ctx with baseUri := resolvePath ctx.baseUri (attr n "xml:base")}
  let ctx := {ctx with expandText := attr n "expand-text" (if ctx.expandText then "true" else "false") != "false"}
  let ctx := {ctx with excludedInlinePrefixes := inlineExclusions ctx n}
  let env := contextEnv ctx n defaultDocs
  let result ← (do
    if attr n "pipe" != "" then
      return (((((attr n "pipe").replace "\n" " ").replace "\t" " ").replace "\r" " ").splitOn " ").filter (· != "") |>.foldlM (fun out p => do pure (out ++ (← lookupPipe ctx p))) []
    if attr n "href" != "" then
      match avt (attr n "href") env with
      | .error e => return .error (pipelineError e)
      | .ok uri => return (← readDocument (resolvePath ctx.baseUri uri) (attr n "content-type")).map List.singleton
    let sourceKids := (kids n).filter (fun c => !["documentation", "pipeinfo"].contains (pTag c))
    if sourceKids.isEmpty then return .ok defaultDocs
    let mut out := []
    for c in sourceKids do
      let r ← match (if ((ns c).lookup (XPath4.splitName (c.elementTag.getD "")).1).getD "" == "http://www.w3.org/ns/xproc" then tag c else "#literal") with
        | "empty" => pure (.ok [])
        | "pipe" => pure (lookupPipe ctx (attr c "port" "result" ++ "@" ++ attr c "step"))
        | "document" =>
          match avt (attr c "href") env with
          | .error e => pure (.error e)
          | .ok uri => do pure ((← loadWithProperties (resolvePath ctx.baseUri uri) c env).map List.singleton)
        | "inline" => pure (((inlineDoc ctx c defaultDocs).mapError (fun e =>
            if defaultDocs.length > 1 && e.code == "XD0001" then {e with code := "XD0065"} else e)).map List.singleton)
        | _ => pure (do
          let excluded := inlineExclusions ctx c
          let c ← expandInline env 4096 ctx.expandText c
          let d ← applyProperties env c ⟨c, "application/xml", ctx.baseUri, [], none⟩
          pure [{d with node := excludeInlineNamespaces excluded 4096 [] d.node}])
      match r with
      | .error e => return .error (pipelineError e)
      | .ok ds => out := out ++ ds
    return .ok out : IO (Result (List Document)))
  match result with
  | .error e => return .error (pipelineError e)
  | .ok docs =>
    if attr n "select" == "" then return .ok docs
    return docs.foldlM (fun out d => do
      let env := contextEnv ctx n [d]
      let seq ← eval (attr n "select") env
      pure (out ++ ((← seqDocuments env seq d.baseUri).map (fun x => {x with properties := d.properties})))) []

def selectionContext (ctx : RunContext) (node : Node) (docs : List Document) : IO (Result (List Document)) :=
  let n := match node with
    | .element t ats cs => .element t (ats.filter (fun a => a.name != "select")) cs
    | n => n
  binding ctx n docs

/-- Bind each option's XPath context before invoking a step. Retain the typed
value under a private QName; Atomic.option then reads it without reevaluation. -/
def prepareOptions (ctx : RunContext) (step : Node) (docs : List Document)
    (env : XPath4.Env) : IO (Result (Node × XPath4.Env)) := do
  let mut env := env
  let mut out := []
  for (child, i) in (children step).zipIdx do
    if pTag child != "with-option" then
      out := child :: out
      continue
    let focused ← selectionContext ctx child docs
    let .ok focused := focused | return focused.map (fun _ => (step,env))
    let optionEnv := contextEnv ctx child focused
    match eval (attr child "select") optionEnv with
    | .error e => return .error (pipelineError e)
    | .ok value =>
      let q : XPath4.QN := ⟨"urn:factoidal:xproc:option", "o" ++ toString i, ""⟩
      env := {env with vars := (q, retainItems optionEnv 256 value) :: env.vars}
      let updated := match child with
        | .element t ats cs => .element t ({name := "select", value := "$" ++ q.eqn} :: ats.filter (fun a => a.name != "select")) cs
        | n => n
      out := updated :: out
  let step := match step with | .element t ats _ => .element t ats out.reverse | n => n
  return .ok (step,env)

def stepPorts (ctx : RunContext) (step : Node) (docs : List Document) : IO (Result Bindings) := do
  let mut ports := [("source", docs)]
  for n in pNamed step "with-input" do
    let port := attr n "port" "source"
    match ← binding ctx n (if port == "source" then docs else []) with
    | .error e => return .error (pipelineError e)
    | .ok ds => ports := (port, ds) :: ports.filter (fun p => p.1 != port)
  return .ok ports

def typedValue (declaration : Node) (env : XPath4.Env) (value : XPath4.Seq) : Result XPath4.Seq := do
  let ty := attr declaration "as"
  if ty == "" then pure value else
  let ty ← fromXPath (XPath4.parseSeqType ty)
  (fromXPath (env.coerce ty value "XProc option/variable")).mapError (fun e => {e with code := "XD0036"})

def condition (expr : String) (env : XPath4.Env) (docs : List Document) : Result Bool := do
  let ast ← fromXPath (XPath4.parseXPath expr env.ns)
  if docs.length > 1 && expressionNeedsFocus (expr.length+1) ast then
    error "XD0001" "XPath context requires one document"
  else evalBool expr env

def declarationTag (s : String) : Bool :=
  ["input", "output", "option", "import", "declare-step", "documentation", "pipeinfo", "serialization"].contains s

def staticAvailable (vars : List (XPath4.QN × XPath4.Seq)) (declarations : List Node) :
    Nat → List XPath4.QN → XPath4.QN → Result Bool
  | 0, _, _ => unsupported "static availability depth limit"
  | fuel+1, visiting, q => do
    if standardAvailable q then return true
    let some d := declarations.find? (fun d => qname d (attr d "type") == q) | return false
    if visiting.contains q then return ← error "XS0115" "cyclic step availability dependency"
    if !((kids d).any isPipelineStep) then return false
    if attr d "use-when" == "" then return true
    let env := { (xpathEnv none vars (ns d)) with
      host := fun name arity =>
        if name.uri == nsXProc && name.loc == "step-available" && arity == 1 then
          some (fun c args => do
            let requested ← functionQName c (args[0]?.getD [])
            match staticAvailable vars declarations fuel (q :: visiting) requested with
            | .ok b => pure (XPath4.sBool b)
            | .error e => XPath4.err e.code e.message)
        else procHost [] 1 1 name arity }
    evalBool (attr d "use-when") env

def pruneUseWhen (vars : List (XPath4.QN × XPath4.Seq)) (declarations : List Node)
    (literalRoot : Bool := false) : Nat → Node → Result (Option Node)
  | 0, _ => unsupported "static tree depth limit"
  | fuel+1, node => do
    let env := { (xpathEnv none vars (ns node)) with
      host := fun q arity =>
        if q.uri == nsXProc && q.loc == "step-available" && arity == 1 then
          some (fun c args => do
            let requested ← functionQName c (args[0]?.getD [])
            match staticAvailable vars declarations 256 [] requested with
            | .ok b => pure (XPath4.sBool b)
            | .error e => XPath4.err e.code e.message)
        else procHost [] 1 1 q arity }
    let control := if pTag node != "" then XML.findAttr "use-when" node.elementAttrs
      else (xpAttribute node "use-when").map (·.value)
    if let some expr := control then
      if !(← evalBool expr env) then return none
    let removed := if pTag node != "" then "use-when"
      else ((xpAttribute node "use-when").map (·.name)).getD ""
    match node with
    | .element name ats cs =>
      let ats := ats.filter (fun a => a.name != removed)
      if ["documentation", "pipeinfo"].contains (pTag node) then
        return some (.element name ats cs)
      let parentBinding := ["with-input", "input", "with-option", "variable", "output", "run-input"].contains (pTag node)
      let mut out := []
      for c in cs do
        let literal := parentBinding && !["inline", "document", "pipe", "empty"].contains (pTag c)
        if let some c ← pruneUseWhen vars declarations literal fuel c then out := c :: out
      pure (some (.element name ats out.reverse))
    | n => pure (some n)

def loadLibraries (fuel : Nat) (base : String) (pipeline : Node) : IO (Result (List Node)) := do
  -- Entries carry source identity through re-exports, so diamond and cyclic
  -- imports are idempotent without hiding conflicts between distinct files.
  let exports (uri : String) (source : Node) (scope : List Node) : List (String × Node) :=
    let identity (kind : String) (node : Node) :=
      let q := qname node (attr node (if kind == "step" then "type" else "name"))
      uri ++ "#" ++ kind ++ ":Q{" ++ q.uri ++ "}" ++ q.loc
    let close (node : Node) := if scope.isEmpty then node else match node with
      | .element name ats cs => .element name ats
          (.element "p:pipeinfo" [{name := "xmlns:p", value := nsXProc}]
            [.element "#xproc-scope" [{name := "base-uri", value := uri}] scope] :: cs)
      | other => other
    if pTag source == "declare-step" then [(identity "step" source, close source)] else
    let localSteps := pNamed source "declare-step"
    let privateSteps := localSteps.filter (fun n => attr n "visibility" == "private")
    (kids source).filterMap fun n =>
      if pTag n == "declare-step" && attr n "visibility" != "private" then
        let n := match n with
          | .element name ats cs => .element name ats (privateSteps ++ cs)
          | other => other
        some (identity "step" n, close n)
      else if pTag n == "option" && attr n "visibility" != "private" then
        some (identity "option" n, n)
      else none
  let unique (entries : List (String × Node)) := entries.foldl (fun acc entry =>
    if acc.any (fun p => p.1 == entry.1) then acc else acc ++ [entry]) []
  let rec load (remaining : Nat) (uri : String) (source : Node) (importedSource : Bool)
      (cache : List (String × List (String × Node))) :
      IO (Result (List (String × Node) × List (String × List (String × Node)))) := do
    match remaining with
    | 0 => return unsupported "library import depth limit"
    | remaining+1 =>
      let mut cache := cache
      if importedSource then cache := (uri, exports uri source []) :: cache
      let mut imported := []
      let mut vars := []
      -- Evaluate available local static defaults for conditional imports.
      -- Defaults needing imported options are evaluated after those imports.
      for opt in pNamed source "option" do
        if attr opt "static" == "true" then
          if let .ok value := eval (attr opt "select" "()") (xpathEnv none vars (ns opt)) then
            vars := (qname opt (attr opt "name"), value) :: vars
      for imp in pNamed source "import" do
        let active := pruneUseWhen vars (pNamed source "declare-step" ++ imported.map (·.2)) false 4096 imp
        let imp ← match active with
          | .error e => return .error (pipelineError e)
          | .ok none => continue
          | .ok (some imp) => pure imp
        let target := resolvePath uri (attr imp "href")
        let file := if target.startsWith "file://" then (target.drop 7).toString else target
        let key ← try pure ((← IO.FS.realPath file).toString) catch _ => pure target
        let entries ← match cache.lookup key with
          | some entries => pure entries
          | none =>
            match ← readDocument target "application/xml" with
            | .error e => return .error (if e.unsupported then e else {e with code := "XS0052"})
            | .ok document =>
              let library := inheritNS 4096 [] document.node
              match ← load remaining key library true cache with
              | .error e => return .error (pipelineError e)
              | .ok (entries, updated) =>
                cache := updated
                pure entries
        imported := unique (imported ++ entries)
        for (_, opt) in entries do
          if pTag opt == "option" && attr opt "static" == "true" &&
              !(vars.any (fun v => v.1 == qname opt (attr opt "name"))) then
            match eval (attr opt "select" "()") (xpathEnv none vars (ns opt)) with
            | .error e => return .error (pipelineError e)
            | .ok value => vars := (qname opt (attr opt "name"), value) :: vars
      if !importedSource then return .ok (imported, cache)
      -- A cyclic path may re-export this source's own provisional signatures.
      -- They are one declaration, not a second declaration with the same QName.
      let ownIds := (exports uri source []).map (·.1)
      imported := imported.filter (fun e => !ownIds.contains e.1)
      for opt in pNamed source "option" do
        if attr opt "static" == "true" then
          match eval (attr opt "select" "()") (xpathEnv none vars (ns opt)) with
          | .error e => return .error (pipelineError e)
          | .ok value => vars := (qname opt (attr opt "name"), value) :: vars.filter (fun v => v.1 != qname opt (attr opt "name"))
      let source ← match pruneUseWhen vars (pNamed source "declare-step" ++ imported.map (·.2)) false 4096 source with
        | .error e => return .error (pipelineError e)
        | .ok none => return .ok ([], (uri, []) :: cache.filter (fun e => e.1 != uri))
        | .ok (some source) => pure source
      if let some (code, msg) := (staticErrors source (imported.map (·.2))).head? then return error code msg
      if let some (code, msg) := (importScopeErrors source (imported.map (·.2)) true).head? then return error code msg
      let localSteps := if pTag source == "declare-step" then [source] else pNamed source "declare-step"
      let scope := localSteps ++ (imported.map (·.2)).filter (fun n => pTag n == "declare-step") ++
        (imported.map (·.2)).filter (fun n => pTag n == "option" && attr n "static" == "true") ++
        (pNamed source "option").filter (fun n => attr n "static" == "true")
      let result := unique (exports uri source scope ++ imported)
      return .ok (result, (uri, result) :: cache.filter (fun e => e.1 != uri))
  match ← load fuel base pipeline false [] with
  | .error e => return .error e
  | .ok (entries, cache) =>
    -- Replace provisional signatures from cyclic imports with their final,
    -- pruned definitions once all sources have been checked.
    let all := cache.flatMap (·.2)
    return .ok (entries.map (fun entry => ((all.find? (fun e => e.1 == entry.1)).getD entry).2))


mutual

def runBody : Nat → RunContext → Node → List Document → IO (Result StepOutput)
  | 0, _, _, _ => pure (unsupported "pipeline call depth limit")
  | fuel+1, ctx0, pipeline, initial => do
    let mut ctx := if attr pipeline "xml:base" == "" then ctx0 else {ctx0 with baseUri := resolvePath ctx0.baseUri (attr pipeline "xml:base")}
    let mut docs := initial
    ctx := {ctx with expandText := attr pipeline "expand-text" (if ctx.expandText then "true" else "false") != "false"}
    ctx := {ctx with excludedInlinePrefixes := inlineExclusions ctx pipeline}
    let inputDecls := pNamed pipeline "input"
    let primaryInput := (inputDecls.find? (fun n => attr n "primary" == "true")).orElse
      (fun _ => inputDecls.head?)
    for input in inputDecls do
      let port := attr input "port" "source"
      let isPrimary := primaryInput.any (fun n => attr n "port" "source" == port) && attr input "primary" != "false"
      let bound ← match ctx.inputPorts.lookup port with
        | some ds => pure (.ok ds)
        | none => if isPrimary && !initial.isEmpty then pure (.ok initial) else binding ctx input []
      let .ok bound := bound | return bound.map primaryOutput
      if attr input "sequence" "false" != "true" && bound.length != 1 then
        return error "XD0006" "input requires exactly one document"
      match checkPortContentTypes input bound with
      | .error e => return .error (pipelineError e)
      | .ok _ => pure ()
      if isPrimary then
        docs := bound
        ctx := {ctx with values := (attr pipeline "name" ++ "/#primary", bound) :: ctx.values}
      let key := attr pipeline "name" ++ "/" ++ port
      ctx := { ctx with values := (key, bound) :: ctx.values }
    ctx := {ctx with inputPorts := []}
    ctx := { ctx with declarations := pNamed pipeline "declare-step" ++ ctx.declarations }
    for opt in pNamed pipeline "option" do
      let q := qname opt (attr opt "name")
      if !(ctx.vars.any (fun p => p.1 == q)) then
        if attr opt "select" == "" then
          if attr opt "required" == "true" then return error "XS0018" "required option missing"
          else ctx := {ctx with vars := (q,[]) :: ctx.vars}
        else
          match eval (attr opt "select") (contextEnv ctx opt docs) with
          | .error e => return .error (pipelineError e)
          | .ok v => ctx := { ctx with vars := (q,v) :: ctx.vars }
    for opt in pNamed pipeline "option" do
      let q := qname opt (attr opt "name")
      if let some value := ctx.vars.lookup q then
        match typedValue opt (contextEnv ctx opt docs) value with
        | .error e => return .error (pipelineError e)
        | .ok value => ctx := {ctx with vars := (q,value) :: ctx.vars.filter (fun p => p.1 != q)}
    let initial := docs
    let hasVariables := !(pNamed pipeline "variable").isEmpty
    let executable := (kids pipeline).filter isPipelineStep
    let jobs := if hasVariables then (kids pipeline).zipIdx else
      ((orderConnections (pipelineConnections pipeline)).getD (List.range executable.length)).filterMap
        (fun i => (executable[i]?).map (fun n => (n,i)))
    for (step, stepIndex) in jobs do
      if !hasVariables then
        docs := if stepIndex == 0 then initial else
          (ctx.values.lookup ("#auto" ++ toString (stepIndex-1))).getD initial
      let t := pTag step
      if declarationTag t then continue
      if t == "variable" then
        let variableDocs ← match ← selectionContext ctx step docs with
          | .error e => return .error (pipelineError e)
          | .ok ds => pure ds
        if variableDocs.length > 1 && attr step "collection" != "true" &&
            (XPath4.parseXPath (attr step "select") (ns step)).toOption.any (expressionNeedsFocus ((attr step "select").length+1)) then
          return error "XD0001" "variable context requires one document"
        match eval (attr step "select") (contextEnv ctx step variableDocs) with
        | .error e => return .error (pipelineError e)
        | .ok v =>
          match typedValue step (contextEnv ctx step variableDocs) v with
          | .error e => return .error (pipelineError e)
          | .ok v =>
            let id := ctx.propertyDocs.length + 1
            let value := retainVariable (contextEnv ctx step variableDocs) id 256 v
            ctx := {ctx with
              vars := (qname step (attr step "name"),value) :: ctx.vars
              propertyDocs := (variableDocs.head?.map (fun d => [(id,d)]) |>.getD []) ++ ctx.propertyDocs}
        continue
      let enabled := if attr step "use-when" == "" then .ok true else evalBool (attr step "use-when") (contextEnv ctx step [])
      match enabled with
      | .error e => return .error (pipelineError e)
      | .ok false => continue
      | .ok true => pure ()
      ctx := {ctx with values := ("#last/result", docs) :: ctx.values.filter (fun p => p.1 != "#last/result")}
      match ← runStep fuel ctx step docs with
      | .error e => return .error (pipelineError e)
      | .ok result =>
        docs := result.primary
        ctx := {ctx with values := ("#auto" ++ toString stepIndex, docs) :: ctx.values}
        for (port, batch) in result.ports do
          ctx := {ctx with values := ("#last/" ++ port, batch) :: ctx.values}
          if attr step "name" != "" then
            ctx := {ctx with values := (attr step "name" ++ "/" ++ port, batch) :: ctx.values}
        if attr step "name" != "" then
          ctx := {ctx with values := (attr step "name" ++ "/#primary", docs) :: ctx.values}
    if !hasVariables && !executable.isEmpty then
      docs := (ctx.values.lookup ("#auto" ++ toString (executable.length-1))).getD docs
    let outputs := pNamed pipeline "output"
    if outputs.isEmpty then return .ok (primaryOutput docs)
    let selected := (outputs.find? (fun n => attr n "primary" == "true")).orElse
      (fun _ => if outputs.length == 1 && attr outputs.head! "primary" != "false" then outputs.head? else none)
    let mut boundOutputs := []
    for output in outputs do
      let result ← if attr output "pipe" != "" || !(kids output).isEmpty then binding ctx output docs
        else pure (.ok docs)
      match result with
      | .error e => return .error (pipelineError e)
      | .ok ds =>
        if attr output "sequence" "false" != "true" && ds.length != 1 then
          return error "XD0007" "output requires exactly one document"
        match checkPortContentTypes output ds with
        | .error e => return .error (pipelineError e)
        | .ok ds => boundOutputs := boundOutputs ++ [(attr output "port", ds)]
    return .ok ⟨(selected.bind (fun n => boundOutputs.lookup (attr n "port"))).getD [], boundOutputs⟩

def runStep : Nat → RunContext → Node → List Document → IO (Result StepOutput)
  | 0, _, _, _ => pure (unsupported "compound step depth limit")
  | fuel+1, ctx, step, defaultDocs => do
    let ctx := if attr step "xml:base" == "" then ctx else {ctx with baseUri := resolvePath ctx.baseUri (attr step "xml:base")}
    let ctx := {ctx with expandText := attr step "expand-text" (if ctx.expandText then "true" else "false") != "false"}
    if !supportedAtomic (tag step) && !supportsExtra (tag step) && !supportsFile (tag step) && !(["group", "for-each", "viewport", "if", "choose", "try", "load", "run", "split-sequence", "with-input"].contains (tag step)) &&
        !(ctx.declarations.any (fun d => qname d (attr d "type") == qname step (step.elementTag.getD ""))) then
      return unsupported ("step " ++ step.elementTag.getD "")
    let ports ← stepPorts ctx step defaultDocs
    let .ok ports := ports | return ports.map (fun _ => primaryOutput [])
    let docs := (ports.lookup "source").getD []
    let env := contextEnv ctx step (if ["choose", "if", "for-each", "viewport", "group", "try"].contains (tag step) then docs else defaultDocs)
    let prepared ← prepareOptions ctx step defaultDocs env
    let .ok (step,env) := prepared | return prepared.map (fun _ => primaryOutput [])
    if (qname step (step.elementTag.getD "")).uri != "http://www.w3.org/ns/xproc" then
      match ctx.declarations.find? (fun d => qname d (attr d "type") == qname step (step.elementTag.getD "")) with
      | none => return unsupported ("extension step " ++ step.elementTag.getD "")
      | some declaration => return ← runDeclared fuel ctx step declaration docs ports env
    match tag step with
    | "group" => runBody fuel ctx step docs
    | "viewport" =>
      withPrimary (viewportStepWithFocus step docs env (fun pos size current =>
        primaryOnly (runBody fuel {ctx with position := pos, size := size, values := ("/current", [current]) :: (attr step "name" ++ "/#primary", [current]) :: (attr step "name" ++ "/current", [current]) :: ctx.values} step [current])))
    | "for-each" =>
      withPrimary (forEachIO docs (fun pos size doc =>
        primaryOnly (runBody fuel {ctx with position := pos, size := size, values := ("/current", [doc]) :: (attr step "name" ++ "/#primary", [doc]) :: (attr step "name" ++ "/current", [doc]) :: ctx.values} step [doc])))
    | "if" =>
      let collection := attr step "collection" == "true"
      let env := if collection then { (collectionEnv env docs true) with ctx := none, docs := (docs.map (fun d => XPath4.Doc.ofNodes (documentNodes d) d.baseUri)).toArray } else env
      match condition (attr step "test") env (if collection then [] else docs) with
      | .error e => return .error (pipelineError e)
      | .ok true => runBody fuel ctx step defaultDocs
      | .ok false => return .ok (primaryOutput defaultDocs)
    | "choose" =>
      for branch in kids step do
        if tag branch == "otherwise" then return ← runBody fuel ctx branch defaultDocs
        if tag branch == "when" then
          let branchDocs ← match ← stepPorts ctx branch docs with
            | .error e => return .error (pipelineError e)
            | .ok ps => pure ((ps.lookup "source").getD [])
          let collection := attr branch "collection" (attr step "collection" "false") == "true"
          let branchEnv := contextEnv ctx branch branchDocs
          let branchEnv := if collection then { (collectionEnv branchEnv branchDocs true) with ctx := none, docs := (branchDocs.map (fun d => XPath4.Doc.ofNodes (documentNodes d) d.baseUri)).toArray } else branchEnv
          match condition (attr branch "test") branchEnv (if collection then [] else branchDocs) with
          | .error e => return .error (pipelineError e)
          | .ok true => return ← runBody fuel ctx branch defaultDocs
          | .ok false => pure ()
      let declarations := ((pNamed step "when").head?.map (fun n => pNamed n "output")).getD []
      if declarations.isEmpty then return .ok (primaryOutput defaultDocs)
      let selected := (declarations.find? (fun n => attr n "primary" == "true")).orElse
        (fun _ => if declarations.length == 1 && attr declarations.head! "primary" != "false" then declarations.head? else none)
      let ports := declarations.map (fun n => (attr n "port", if selected.any (fun o => attr o "port" == attr n "port") then defaultDocs else []))
      return .ok ⟨if selected.isSome then defaultDocs else [], ports⟩
    | "try" =>
      let body := .element "p:group" step.elementAttrs ((children step).filter (fun n => !["catch", "finally"].contains (tag n)))
      let initial ← runBody fuel ctx body docs
      let errors := match initial with
        | .ok _ => []
        | .error e =>
          let code := e.errorName.map (fun q => if q.pfx == "" then q.loc else q.pfx ++ ":" ++ q.loc) |>.getD e.code
          let namespaces := e.errorName.map (fun q => if q.pfx == "" then [] else [{name := "xmlns:" ++ q.pfx, value := q.uri}]) |>.getD []
          [{ node := .element "c:errors" [{name := "xmlns:c", value := "http://www.w3.org/ns/xproc-step"}] [.element "c:error" ({name := "code", value := code} :: namespaces) ([.text e.message] ++ e.details)], baseUri := ctx.baseUri }]
      let result ← match initial with
        | .ok output => pure (.ok output)
        | .error e =>
          if e.unsupported then pure (.error e)
          else match (pNamed step "catch").find? (fun c => attr c "code" == "" || ((attr c "code").splitOn " ").any (fun s =>
            (parseQName c s).toOption.any (fun q => q.eqn == (if e.code.startsWith "Q{" then e.code else "Q{http://www.w3.org/ns/xproc-error}" ++ e.code)))) with
            | none => pure (.error e)
            | some c => runBody fuel {ctx with values := ("/error", errors) :: (attr c "name" ++ "/error", errors) :: ctx.values} c errors
      if let some finalStep := (pNamed step "finally").head? then
        match ← runBody fuel {ctx with values := ("/error", errors) :: (attr finalStep "name" ++ "/error", errors) :: ctx.values} finalStep errors with
        | .error e => return .error (pipelineError e)
        | .ok finalOutput =>
          return result.map (fun output => {output with ports := output.ports ++ finalOutput.ports})
      return result
    | "split-sequence" =>
      let test ← match option step "test" env with
        | .error e => return .error (pipelineError e)
        | .ok text => pure text
      let initialOnly ← match option step "initial-only" env "false" with
        | .error e => return .error (pipelineError e)
        | .ok text => pure (text == "true")
      let mut matched := []
      let mut unmatched := []
      let mut stopped := false
      for (d,i) in docs.zipIdx do
        if initialOnly && stopped then unmatched := d :: unmatched else
          let focus := { (contextEnv ctx step [d]) with pos := i+1, size := docs.length }
          match evalBool test focus with
          | .error e => return .error (pipelineError e)
          | .ok true => matched := d :: matched
          | .ok false =>
            unmatched := d :: unmatched
            stopped := true
      let matching := matched.reverse
      return .ok ⟨matching, [("matched",matching),("not-matched",unmatched.reverse)]⟩
    | "run" =>
      if (pNamed step "with-input").isEmpty then return error "XS0003" "run pipeline input must be explicitly connected"
      if (pNamed step "with-input").any (fun n => attr n "port" != "") then
        return error "XS0114" "run pipeline input is anonymous"
      let [pipelineDoc] := docs | return error "XD0006" "run requires one pipeline document"
      let pipeline := inheritNS 4096 [] pipelineDoc.node
      if pTag pipeline != "declare-step" then return error "XC0200" "run input is not a pipeline"
      let runInputs := pNamed step "run-input"
      if (runInputs.map (fun n => attr n "port")).eraseDups.length != runInputs.length then
        return error "XS0086" "duplicate run-input"
      let runOptions := pNamed step "run-option"
      if (runOptions.map (fun n => attr n "name")).eraseDups.length != runOptions.length then
        return error "XS0080" "duplicate run-option"
      let mut vars := []
      for opt in runOptions do
        let q := qname opt (attr opt "name")
        if let some declaration := (pNamed pipeline "option").find? (fun d => qname d (attr d "name") == q) then
          match eval (attr opt "select") env with
          | .error e => return .error (pipelineError e)
          | .ok value =>
            let convertedValue : Result XPath4.Seq := if (attr declaration "as").replace " " "" |>.startsWith "map(xs:QName," then do
                match value with
                | [.map entries] =>
                  let converted := entries.mapM fun (key,v) => do
                    let key ← if propertyName key |>.isSome then pure key
                      else fromXPath (XPath4.castFromString key.str (.b .qname) env.nsResolve)
                    pure (key,v)
                  pure [.map (← converted)]
                | _ => pure value
              else pure value
            let value ← match convertedValue with
              | .error e => return .error {e with code := "XC0200"}
              | .ok v => pure v
            vars := (q, retainItems env 256 value) :: vars
      for opt in pNamed pipeline "option" do
        let q := qname opt (attr opt "name")
        let optionEnv := xpathEnv none vars (ns opt)
        let value ← match vars.lookup q with
          | some v => pure v
          | none =>
            if attr opt "required" == "true" then return error "XS0018" "required dynamic pipeline option missing"
            match eval (attr opt "select" "()") optionEnv with
            | .error e => return .error {e with code := "XC0200"}
            | .ok v => pure v
        match typedValue opt optionEnv value with
        | .error e => return .error {e with code := if attr opt "static" == "true" then "XC0200" else "XD0036"}
        | .ok v => vars := (q, retainItems optionEnv 4096 v) :: vars.filter (fun p => p.1 != q)
      let staticVars := vars.filter fun (q,_) => (pNamed pipeline "option").any
        (fun opt => attr opt "static" == "true" && qname opt (attr opt "name") == q)
      let pipeline ← match pruneUseWhen staticVars (pNamed pipeline "declare-step") false 4096 pipeline with
        | .error e => return .error {e with code := "XC0200"}
        | .ok none => return error "XC0200" "dynamic pipeline excluded"
        | .ok (some n) => pure n
      if let some (_,msg) := (staticErrors pipeline).head? then return error "XC0200" msg
      let isPrimary := fun (all : List Node) (n : Node) =>
        attr n "primary" == "true" || (attr n "primary" == "" && all.length == 1)
      let inputDecls := pNamed pipeline "input"
      for supplied in runInputs do
        if isPrimary runInputs supplied && !(inputDecls.any (fun d => attr d "port" == attr supplied "port" && isPrimary inputDecls d)) then
          return error "XC0206" "dynamic primary input is not declared"
      let mut inputPorts := []
      for d in inputDecls do
        let port := attr d "port"
        if let some bindingNode := runInputs.find? (fun n => attr n "port" == port) then
          if isPrimary inputDecls d != isPrimary runInputs bindingNode then
            return error "XC0206" "dynamic input primary designation differs"
          match ← binding ctx bindingNode (if isPrimary runInputs bindingNode then defaultDocs else []) with
          | .error e => return .error (pipelineError e)
          | .ok batch =>
            if batch.isEmpty && !(kids d).isEmpty then pure ()
            else inputPorts := (port,batch) :: inputPorts
        else if (kids d).isEmpty then inputPorts := (port,[]) :: inputPorts
      let declaredOutputs := pNamed pipeline "output"
      let requestedOutputs := pNamed step "output"
      for o in requestedOutputs do
        if isPrimary requestedOutputs o && !(declaredOutputs.any (fun d => attr d "port" == attr o "port" && isPrimary declaredOutputs d)) then
          return error "XC0207" "dynamic primary output is not declared"
        if let some d := declaredOutputs.find? (fun n => attr n "port" == attr o "port") then
          if isPrimary declaredOutputs d != isPrimary requestedOutputs o then
            return error "XC0207" "dynamic output primary designation differs"
      let declarations ← match ← loadLibraries 32 pipelineDoc.baseUri pipeline with
        | .error e => return .error {e with code := "XC0200"}
        | .ok ds => pure ds
      let output ← runBody fuel {baseUri := pipelineDoc.baseUri, vars, staticVars, inputPorts, declarations} pipeline []
      let .ok output := output | return output
      let mut resultPorts := []
      let mut primary := []
      for o in requestedOutputs do
        let port := attr o "port"
        let batch := (output.ports.lookup port).getD []
        if attr o "sequence" "false" != "true" && batch.length != 1 then
          return error "XD0007" "dynamic output requires one document"
        match checkPortContentTypes o batch with
        | .error e => return .error (pipelineError e)
        | .ok _ => pure ()
        resultPorts := resultPorts ++ [(port,batch)]
        if isPrimary requestedOutputs o then primary := batch
      return .ok ⟨primary,resultPorts⟩
    | "load" =>
      match option step "href" env with
      | .error e => return .error (pipelineError e)
      | .ok href => return (← loadWithProperties (resolvePath ctx.baseUri href) step env).map (fun d => primaryOutput [d])
    | "with-input" => return .ok (primaryOutput docs)
    | _ =>
      if supportsFile (tag step) then return (← fileStep step ports env ctx.writeRoot).map primaryOutput
      withPrimary (if supportsExtra (tag step) then extraAtomic step ports env else atomic step ports env)

def runDeclared : Nat → RunContext → Node → Node → List Document → Bindings → XPath4.Env → IO (Result StepOutput)
  | 0, _, _, _, _, _, _ => pure (unsupported "user step depth limit")
  | fuel+1, ctx, step, declaration, docs, ports, env => do
    let scope := (pNamed declaration "pipeinfo").findSome? (fun info =>
      (kids info).find? (fun n => n.elementTag == some "#xproc-scope"))
    let mut ctx := ctx
    if let some scope := scope then
      let mut statics := []
      for opt in pNamed scope "option" do
        let q := qname opt (attr opt "name")
        let supplied := if attr opt "visibility" != "private" then ctx.staticVars.lookup q else none
        let value := match supplied with
          | some v => .ok v
          | none => eval (attr opt "select" "()") (xpathEnv none statics (ns opt))
        let .ok value := value | return value.map (fun _ => primaryOutput [])
        statics := (q,value) :: statics
      ctx := {ctx with
        declarations := pNamed scope "declare-step"
        staticVars := statics
        baseUri := attr scope "base-uri" ctx.baseUri}
    let mut vars := ctx.staticVars
    for opt in pNamed declaration "option" do
      let name := attr opt "name"
      let q := qname opt name
      if attr step name != "" then
        let ty := attr opt "as"
        let value := if ty.startsWith "map(" || ty.startsWith "array(" then eval (attr step name) env
          else (avt (attr step name) env).map (fun text => [XPath4.Item.atom (XPath4.Atomic.untypedOf text)])
        match value with
        | .error e => return .error (pipelineError e)
        | .ok value => vars := (q, value) :: vars
      else if let some binding := (pNamed step "with-option").find? (fun n => attr n "name" == name) then
        match eval (attr binding "select") env with
        | .error e => return .error (pipelineError e)
        | .ok value => vars := (q,value) :: vars
    let ports := ports.filter (fun pair =>
      !(pair.1 == "source" && pair.2.isEmpty &&
        !(pNamed step "with-input").any (fun n => attr n "port" "source" == "source") &&
        (pNamed declaration "input").any (fun n => attr n "port" == "source" && !(kids n).isEmpty)))
    runBody fuel {ctx with vars, inputPorts := ports} declaration docs

end

def runPipeline (pipeline : Node) (inputs : List Document := []) (baseUri : String := "")
    (options : List (String × String) := []) (writeRoot : Option String := none) : IO (Result (List Document)) := do
  let pipeline := inheritNS 4096 [] pipeline
  if attr pipeline "version" == "3.2" then return unsupported "XProc 3.2 pipeline"
  let libraryResult ← loadLibraries 32 baseUri pipeline
  let imported := libraryResult.toOption.getD []
  let mut vars := []
  for (name,expr) in options do
    match eval expr (xpathEnv inputs.head? vars (ns pipeline)) with
    | .error e => return .error (pipelineError e)
    | .ok v => vars := (qname pipeline name,v) :: vars
  for opt in imported.filter (fun n => pTag n == "option") ++ pNamed pipeline "option" do
    if attr opt "static" == "true" && !(vars.any (fun p => p.1 == qname opt (attr opt "name"))) then
      match eval (attr opt "select" "()") (xpathEnv none vars (ns opt)) with
      | .error e => return .error (pipelineError e)
      | .ok v => vars := (qname opt (attr opt "name"),v) :: vars
  let staticNames := (imported.filter (fun n => pTag n == "option") ++ pNamed pipeline "option").filterMap
    (fun opt => if attr opt "static" == "true" then some (qname opt (attr opt "name")) else none)
  let staticVars := vars.filter (fun v => staticNames.contains v.1)
  let pipeline ← match pruneUseWhen staticVars (pNamed pipeline "declare-step" ++ imported) false 4096 pipeline with
    | .error e => return .error (pipelineError e)
    | .ok none => return error "XS0052" "pipeline excluded by use-when"
    | .ok (some n) => pure n
  let issues := staticErrors pipeline imported
  if let some (code,msg) := issues.head? then return error code msg
  let declarations ← match ← loadLibraries 32 baseUri pipeline with
    | .error e => return .error (pipelineError e)
    | .ok ds => pure ds
  if let some (code,msg) := (importScopeErrors pipeline declarations).head? then return error code msg
  let result ← runBody 256 {vars, staticVars, baseUri, declarations, writeRoot} pipeline inputs
  return result.map (fun output => (output.ports.lookup "result").getD output.primary)

end L4Factoidal.XProc31
