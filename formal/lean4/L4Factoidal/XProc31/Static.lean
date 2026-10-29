import L4Factoidal.XML.Document
import L4Factoidal.XPath4.Parser
import L4Factoidal.XPath4.Catalog
import L4Factoidal.XProc31.MediaTypes

/-! XProc connection cycles. Source order is not a topological order: an
acyclic forward reference is legal. The Kahn elimination below accepts it.
The XML reader collects dependencies of compound steps on their enclosing
scope. Inline documents are data, not pipeline declarations. -/
namespace L4Factoidal.XProc31

/-- Dependencies are indices in the original declaration order. -/
abbrev Connections := List (List Nat)

/-- Remove a ready node at each iteration. Out-of-range dependencies must
be diagnosed by port resolution; they are not reported as cycles. -/
def orderConnectionsAux (edges : Connections) : Nat → List Nat → List Nat → Option (List Nat)
  | 0, [], done => some done.reverse
  | 0, _ :: _, _ => none
  | fuel + 1, pending, done =>
      if pending.isEmpty then some done.reverse else
      match pending.find? (fun i => ((edges[i]?).getD []).all (fun j => !pending.contains j)) with
      | none => none
      | some i => orderConnectionsAux edges fuel (pending.erase i) (i :: done)

/-- Topological order, or none for a cycle. -/
def orderConnections (edges : Connections) : Option (List Nat) :=
  orderConnectionsAux edges edges.length (List.range edges.length) []

def connectionCycle (edges : Connections) : Bool := (orderConnections edges).isNone

#guard orderConnections [[], [0], [1]] == some [0, 1, 2]
#guard orderConnections [[1], []] == some [1, 0]
#guard connectionCycle [[1], [0]]
#guard connectionCycle [[0]]
#guard !connectionCycle [[], [0], [0]]

def nodeDepth : XML.Node → Nat
  | .element _ _ children => 1 + (children.map nodeDepth).foldl max 0
  | _ => 1

private def inheritNamespaces : Nat → List XML.Attribute → XML.Node → XML.Node
  | 0, _, n => n
  | f+1, inherited, .element t attrs cs =>
    let attrs := attrs ++ inherited.filter (fun a => !attrs.any (fun b => a.name == b.name))
    let ns := attrs.filter (fun a => a.name == "xmlns" || a.name.startsWith "xmlns:")
    .element t attrs (cs.map (inheritNamespaces f ns))
  | _, _, n => n

private def dependencyAttr (node : XML.Node) : Option String :=
  let (pfx, _) := XPath4.splitName (node.elementTag.getD "")
  if ((ns node).lookup pfx).getD "" == "http://www.w3.org/ns/xproc" then
    XML.findAttr "depends" node.elementAttrs
  else (node.elementAttrs.find? (fun a =>
    let (p,l) := XPath4.splitName a.name
    p != "" && l == "depends" && ((ns node).lookup p).getD "" == "http://www.w3.org/ns/xproc")).map (·.value)

private def staticAttr (node : XML.Node) (name : String) : String :=
  (if name == "depends" then dependencyAttr node else XML.findAttr name node.elementAttrs).getD ""

private def staticLocalName (node : XML.Node) : String :=
  let (pfx, loc) := XPath4.splitName (node.elementTag.getD "")
  if ((ns node).lookup pfx).getD "" == "http://www.w3.org/ns/xproc" then loc else "#extension"

private def words (s : String) : List String :=
  (((s.replace "\t" " ").replace "\n" " ").replace "\r" " " |>.splitOn " ").filter (! ·.isEmpty)

/-- Metadata and bindings are not executable sibling steps. -/
def isPipelineStep (node : XML.Node) : Bool :=
  node.elementTag.isSome && !(["input", "output", "option", "variable", "import", "declare-step",
    "with-input", "with-option", "documentation", "pipeinfo", "serialization", "log",
    "when", "otherwise", "catch", "finally", "run-option", "run-input", "run-output", "import-functions"].contains
    (staticLocalName node))

private def sourceName (pipe : String) : String :=
  ((pipe.splitOn "@").drop 1).headD ""

/-- Descendant references contribute to the enclosing compound step.
Do not enter a literal document or a separately declared pipeline. -/
def referencedStepsAux : Nat → XML.Node → List String
  | 0, _ => []
  | fuel + 1, node => Id.run do
    let own := words (staticAttr node "depends") ++
      ((words (staticAttr node "pipe")).filter (fun p => !p.startsWith "current@" && !p.startsWith "error@")).map sourceName ++
      (if staticLocalName node == "pipe" && staticAttr node "port" != "current" && staticAttr node "port" != "error" then [staticAttr node "step"] else [])
    if ["inline", "document", "declare-step", "documentation", "pipeinfo"].contains (staticLocalName node) then
      return own.filter (! ·.isEmpty)
    let children := node.allChildElements.filter fun c =>
      -- A binding's literal children are documents, not executable markup.
      if ["with-input", "input", "output", "variable", "with-option", "run-input"].contains (staticLocalName node) then
        ["pipe", "empty", "document"].contains (staticLocalName c)
      else true
    return (own ++ children.flatMap (referencedStepsAux fuel)).filter (! ·.isEmpty)

def referencedSteps (node : XML.Node) : List String :=
  referencedStepsAux (nodeDepth node) (inheritNamespaces (nodeDepth node) [] node)

/-- Context dependence of the supported XPath expression constructors.
The right side of a path/filter/simple-map obtains its own focus. -/
def expressionNeedsFocus : Nat → XPath4.Expr → Bool
  | 0, _ => false
  | f + 1, e =>
    let need := expressionNeedsFocus f
    match e with
    | .ctx | .root | .step .. | .dstep .. | .ulookup .. => true
    | .slash a _ | .filter a _ | .smap a _ => need a
    | .seq es | .arrS es | .tmpl es => es.any need
    | .arrC a | .neg a | .plus a | .instOf a _ | .treat a _ | .cast a _ _ | .castable a _ _ => need a
    | .bin _ a b | .pipe a b | .forE _ _ _ _ _ a b | .letE _ _ a b | .quant _ _ _ a b => need a || need b
    | .ifE a b c => need a || need b || need c
    | .lookup a b => need a || b.any need
    | .mapC es => es.any (fun (a,b) => need a || need b)
    | .call q args kw =>
      (args.isEmpty && ["position", "last", "string", "number", "name", "local-name", "namespace-uri",
        "base-uri", "document-uri", "normalize-space", "string-length", "root", "data"].contains q.loc) ||
      args.any (fun a => a.any need) || kw.any (fun a => a.2.any need)
    | .dyn a args | .mapArrow a _ args => need a || args.any (fun a => a.any need)
    | .inline _ _ body focus => !focus && need body
    | .ext _ es _ _ _ => es.any need
    | _ => false

private def templateFocusAux : Nat → List Char → Bool
  | 0, _ => false
  | _, [] => false
  | f+1, '{' :: '{' :: cs => templateFocusAux f cs
  | f+1, '}' :: '}' :: cs => templateFocusAux f cs
  | f+1, '{' :: cs =>
    let expr := cs.takeWhile (· != '}')
    let depends := match XPath4.parseXPath (String.ofList expr) with
      | .ok e => expressionNeedsFocus (expr.length + 1) e
      | .error _ => false
    depends || templateFocusAux f ((cs.drop expr.length).drop 1)
  | f+1, _ :: cs => templateFocusAux f cs

private def templateNeedsFocus (text : String) : Bool := templateFocusAux (text.length+1) text.toList

private def inlineNeedsFocus : Nat → Bool → XML.Node → Bool
  | 0, _, _ => false
  | f+1, expand, node =>
    let expand := match XML.findAttr "expand-text" node.elementAttrs with
      | some "false" => false | some "true" => true | _ => expand
    let attrs := node.elementAttrs.any (fun a => a.name != "expand-text" && templateNeedsFocus a.value)
    match node with
    | .text t | .cdata t => expand && templateNeedsFocus t
    | .element _ _ cs => attrs || cs.any (inlineNeedsFocus f expand)
    | _ => false

def pipelineConnections (root : XML.Node) : Connections := Id.run do
  let root := inheritNamespaces (nodeDepth root) [] root
  let steps := root.allChildElements.filter isPipelineStep
  let names := steps.map (fun n => staticAttr n "name")
  return steps.zipIdx |>.map fun (step, i) =>
    let explicit := (referencedSteps step).filterMap fun n => names.idxOf? n
    let contextInline := step.allChildElements.any (fun n => staticLocalName n == "with-input" &&
      inlineNeedsFocus (nodeDepth n) true n)
    let hasSource := !contextInline && step.allChildElements.any (fun n => staticLocalName n == "with-input" &&
      (staticAttr n "port" == "" || staticAttr n "port" == "source") &&
      (XML.hasAttr "pipe" n.elementAttrs || XML.hasAttr "href" n.elementAttrs ||
       n.allChildElements.any (fun c => !["documentation", "pipeinfo"].contains (staticLocalName c)))) || staticAttr step "href" != ""
    let sourceFree := ["load", "directory-list", "error"].contains (staticLocalName step)
    let implicit := if i > 0 && !hasSource && !sourceFree then [i - 1] else []
    (explicit ++ implicit).eraseDups

private def ncName (s : String) : Bool := XML.isName s && !(s.contains ":")

private def eqName (s : String) : Bool :=
  if s.startsWith "Q{" then
    let parts := s.splitOn "}"
    parts.length == 2 && ncName (parts[1]?.getD "")
  else match s.splitOn ":" with
    | [a] => ncName a
    | [a,b] => ncName a && ncName b
    | _ => false

private def typePrefixesBound (node : XML.Node) (text : String) : Bool :=
  let (_, tokens) := text.toList.foldl (fun (state : Bool × String) c =>
    if c == '{' then (true, state.2 ++ " ")
    else if c == '}' then (false, state.2 ++ " ")
    else if state.1 then state
    else (false, state.2.push (if c.isAlphanum || [':', '_', '-', '.'].contains c then c else ' '))) (false, "")
  (words tokens).all fun token => match token.splitOn ":" with
    | [pfx, loc] => !ncName pfx || !ncName loc || ((ns node).lookup pfx).isSome || pfx == "xml"
    | _ => true

private def isBranch (n : XML.Node) : Bool :=
  ["when", "otherwise", "catch", "finally"].contains (staticLocalName n)

private def structuralChildren (n : XML.Node) : List XML.Node :=
  if ["inline", "document", "documentation", "pipeinfo"].contains (staticLocalName n) then []
  else if ["with-input", "input", "output", "variable", "with-option", "run-input"].contains (staticLocalName n) then
    n.allChildElements.filter (fun c => ["inline", "document", "pipe", "empty"].contains (staticLocalName c))
  else n.allChildElements

private def nodeNamespaces (n : XML.Node) : List (String × String) :=
  n.elementAttrs.filterMap fun a =>
    if a.name == "xmlns" then some ("", a.value)
    else if a.name.startsWith "xmlns:" then some ((a.name.drop 6).toString, a.value) else none

private def nameKey (n : XML.Node) (lex : String) : String × String :=
  match XPath4.parseXPath ("$" ++ lex) (nodeNamespaces n) with
  | .ok (.var q) => (q.uri, q.loc)
  | _ => ("", lex)

private def supportedVersion (s : String) : Bool :=
  let s := s.trimAscii.toString
  let s := if s.startsWith "+" then (s.drop 1).toString else s
  match s.splitOn "." with
  | [i] => i.toNat? == some 3
  | [i, frac] => i.toNat? == some 3 &&
    (frac.toList.all (· == '0') || (frac.startsWith "1" && (frac.drop 1).toString.toList.all (· == '0')))
  | _ => false

private def primaryOutput : Nat → List XML.Node → XML.Node → Option (Option String)
  | 0, _, _ => none
  | f+1, declarations, node =>
    let outputs := node.allChildElements.filter (fun c => staticLocalName c == "output")
    if !outputs.isEmpty then
      some ((outputs.find? (fun o => staticAttr o "primary" == "true" ||
        (outputs.length == 1 && staticAttr o "primary" != "false"))).map (fun o => staticAttr o "port"))
    else if staticLocalName node == "sink" then some none
    else if ["when", "otherwise", "group", "for-each", "viewport", "if", "catch", "finally", "declare-step"].contains (staticLocalName node) then
      match (node.allChildElements.filter isPipelineStep).getLast? with
      | some last => primaryOutput f declarations last
      | none => some none
    else match declarations.find? (fun d => nameKey d (staticAttr d "type") == nameKey node (node.elementTag.getD "")) with
      | some d => primaryOutput f declarations d
      | none =>
        if staticLocalName node != "#extension" then some (some "result") else none

/-- A connection child may be literal XML. Metadata alone is not a binding.
An empty pipe attribute explicitly requests the default readable port. -/
private def hasExplicitConnection (node : XML.Node) : Bool :=
  staticAttr node "pipe" != "" || XML.hasAttr "href" node.elementAttrs ||
  node.allChildElements.any (fun c => !["documentation", "pipeinfo"].contains (staticLocalName c))

private def localSyntaxErrors (root : XML.Node) (declarations : List XML.Node) : List (String × String) := Id.run do
  let kind := staticLocalName root
  let has := fun a => if a == "depends" then (dependencyAttr root).isSome else XML.hasAttr a root.elementAttrs
  let cs := root.allChildElements.filter (fun n => !["documentation", "pipeinfo"].contains (staticLocalName n))
  let mut errors := []
  if ["input", "with-input", "run-input"].contains kind then
    let literals := cs.filter (fun c => staticLocalName c == "#extension")
    let connections := cs.filter (fun c => ["inline", "document", "pipe", "empty"].contains (staticLocalName c))
    if cs.any (fun c => staticLocalName c == "empty") && cs.length > 1 then
      errors := errors ++ [("XS0089", "Empty must be the only connection child")]
    if cs.any (fun c => staticLocalName c != "#extension" &&
        !["inline", "document", "pipe", "empty"].contains (staticLocalName c)) ||
        (!literals.isEmpty && !connections.isEmpty) then
      errors := errors ++ [("XS0100", "Invalid or mixed binding child forms")]
    if !literals.isEmpty && (children root).any (fun c => match c with
        | .comment _ | .pi .. => true
        | .text t | .cdata t => !t.trimAscii.toString.isEmpty
        | _ => false) then
      errors := errors ++ [("XS0079", "Implicit inline siblings may only be elements or whitespace")]
  if kind == "run-input" && !has "port" then
    errors := errors ++ [("XS0038", "Run input requires a port name")]
  if kind == "run-option" && (!has "name" || !has "select") then
    errors := errors ++ [("XS0038", "Run option requires name and select")]
  if kind == "run" then
    let pipelineInput := cs.find? (fun c => staticLocalName c == "with-input")
    if pipelineInput.isNone then errors := errors ++ [("XS0003", "Run requires an explicit pipeline input")]
    let runPorts := (cs.filter (fun c => staticLocalName c == "run-input")).map (staticAttr · "port")
    if runPorts.eraseDups.length != runPorts.length then
      errors := errors ++ [("XS0086", "Run input port is bound more than once")]
  if ["load", "directory-list"].contains kind && cs.any (fun c => staticLocalName c == "with-input") then
    errors := errors ++ [("XS0065", "This step has no primary input port")]
  if ["input", "output", "with-input", "run-input"].contains kind && has "content-types" then
    match validateDeclaredContentTypes (staticAttr root "content-types") with
    | .error e => errors := errors ++ [(e.code, e.message)]
    | .ok _ => pure ()
  if ["declare-step", "library"].contains kind && has "version" && !supportedVersion (staticAttr root "version") then
    let v := (staticAttr root "version").trimAscii.toString
    let v := if v.startsWith "+" || v.startsWith "-" then (v.drop 1).toString else v
    let parts := v.splitOn "."
    let decimal := parts.length <= 2 && v.toList.any Char.isDigit &&
      parts.all (fun part => part.toList.all Char.isDigit)
    errors := errors ++ [(if decimal then "XS0060" else "XS0063", "Invalid or unsupported XProc version")]
  if (kind == "input" && !has "port") || (["if", "when"].contains kind && !has "test") then
    errors := errors ++ [("XS0038", "Required port or test attribute is missing")]
  if ["option", "variable", "with-option", "run-option"].contains kind then
    if !has "name" || (kind != "option" && !has "select") then
      errors := errors ++ [("XS0038", "Required declaration attribute is missing")]
    if ["option", "variable"].contains kind && has "name" && eqName (staticAttr root "name") then
      match XPath4.parseXPath ("$" ++ staticAttr root "name") (nodeNamespaces root) with
      | .ok (.var q) =>
        if q.uri == "http://www.w3.org/ns/xproc" then
          errors := errors ++ [("XS0028", "Option or variable name is in the XProc namespace")]
      | .error e =>
        if e.code == "XPST0081" then errors := errors ++ [("XS0087", "Undeclared name prefix")]
      | _ => pure ()
    if has "as" && (!typePrefixesBound root (staticAttr root "as") ||
        (XPath4.parseXPath ("() instance of " ++ staticAttr root "as") (nodeNamespaces root)).toOption.isNone) then
      errors := errors ++ [("XS0096", "Invalid sequence type")]
    if has "select" && (XPath4.parseXPath (staticAttr root "select") (nodeNamespaces root)).toOption.isNone then
      errors := errors ++ [("XS0107", "Invalid XPath expression")]
  if kind == "option" && staticAttr root "required" == "true" then
    if has "select" then errors := errors ++ [("XS0017", "Required option cannot have a default")]
    if staticAttr root "static" == "true" then errors := errors ++ [("XS0095", "Static option cannot be required")]
  if kind == "declare-step" && has "type" && eqName (staticAttr root "type") then
    let (uri, _) := nameKey root (staticAttr root "type")
    if uri == "" || uri == "http://www.w3.org/ns/xproc" then
      errors := errors ++ [("XS0025", "Step type must be in a non-XProc namespace")]
  let optNames := (cs.filter (fun n => staticLocalName n == "option")).map (fun n => nameKey n (staticAttr n "name"))
  if optNames.eraseDups.length != optNames.length then errors := errors ++ [(if kind == "library" then "XS0071" else "XS0004", "Duplicate option name")]
  if kind != "#extension" && root.elementAttrs.any (fun a =>
      let (p,l) := XPath4.splitName a.name
      p != "" && l == "depends" && ((ns root).lookup p).getD "" == "http://www.w3.org/ns/xproc") then
    errors := errors ++ [("XS0097", "XProc steps use unprefixed depends")]
  if kind == "with-option" && staticAttr root "name" == "p:depends" then
    errors := errors ++ [("XS0031", "depends is not a step option")]
  let globalAttrs := ["name", "depends", "use-when", "expand-text", "exclude-inline-prefixes", "version", "psvi-required", "xpath-version"]
  let globalAttrs := if kind == "#extension" then globalAttrs.filter (· != "depends") else globalAttrs
  if kind == "input" || kind == "variable" then
    let allowed := globalAttrs ++ (if kind == "input" then
      ["port", "primary", "sequence", "content-types", "href", "select", "document-properties", "pipe"] else
      ["select", "as", "collection", "href", "pipe", "document-properties", "content-type"])
    if root.elementAttrs.any (fun a => !(a.name.contains ":") && a.name != "xmlns" && !allowed.contains a.name) then
      errors := errors ++ [("XS0008", "Unknown declaration attribute")]
  let supplied := (cs.filter (fun n => staticLocalName n == "with-option")).map (fun n => nameKey n (staticAttr n "name"))
  let shortcutNames := root.elementAttrs.filterMap fun a =>
    if a.name.contains ":" || a.name == "xmlns" || globalAttrs.contains a.name then none
    else some (nameKey root a.name)
  if supplied.any (shortcutNames.contains ·) then errors := errors ++ [("XS0080", "Option has both shorthand and explicit binding")]
  if ["identity", "sink"].contains kind && (root.elementTag.getD "").startsWith "p:" &&
      (!supplied.isEmpty || !shortcutNames.isEmpty) then
    errors := errors ++ [("XS0031", "This step has no declared options")]
  if let some declaration := declarations.find? (fun d => staticAttr d "type" != "" &&
      nameKey d (staticAttr d "type") == nameKey root (root.elementTag.getD "")) then
    let opts := declaration.allChildElements.filter (fun n => staticLocalName n == "option")
    let known := opts.map (fun n => nameKey n (staticAttr n "name"))
    let fixed := (opts.filter (fun n => staticAttr n "static" == "true")).map (fun n => nameKey n (staticAttr n "name"))
    if (supplied ++ shortcutNames).any (fixed.contains ·) then
      errors := errors ++ [("XS0092", "Static option cannot be changed at invocation")]
    if (supplied ++ shortcutNames).any (fun n => !known.contains n) then
      errors := errors ++ [("XS0031", "Unknown option on declared step")]
    let declaredInputs := declaration.allChildElements.filter (fun n => staticLocalName n == "input")
    for input in declaredInputs do
      let primary := staticAttr input "primary" == "true" ||
        (declaredInputs.length == 1 && staticAttr input "primary" != "false")
      let binding := cs.find? (fun n => staticLocalName n == "with-input" && staticAttr n "port" == staticAttr input "port")
      if !primary && !hasExplicitConnection input &&
          !(binding.any (fun n => hasExplicitConnection n || XML.hasAttr "pipe" n.elementAttrs)) then
        errors := errors ++ [("XS0032", "Secondary input has neither a connection nor a default")]
  let boolAttrs := if ["input", "output", "option", "variable", "with-option", "when", "if"].contains kind then
    ["primary", "sequence", "static", "required", "collection"] else []
  if boolAttrs.any (fun a => has a && !["true", "false"].contains (staticAttr root a)) then
    errors := errors ++ [("XS0077", "Invalid static boolean attribute")]
  if has "depends" && ((words (staticAttr root "depends")).isEmpty || !(words (staticAttr root "depends")).all ncName) then
    errors := errors ++ [("XS0077", "depends requires a nonempty list of NCNames")]
  if has "port" && ["input", "output", "with-input", "run-input", "pipe"].contains kind && !ncName (staticAttr root "port") then
    errors := errors ++ [("XS0077", "Invalid port NCName")]
  if has "name" && ["option", "variable", "declare-step"].contains kind && !eqName (staticAttr root "name") then
    errors := errors ++ [("XS0077", "Invalid name")]
  if has "type" && kind == "declare-step" && !eqName (staticAttr root "type") then
    errors := errors ++ [("XS0077", "Invalid step type EQName")]
  if kind == "option" && has "visibility" && !["public", "private"].contains (staticAttr root "visibility") then
    errors := errors ++ [("XS0077", "Invalid option visibility")]
  if isBranch root && has "depends" then errors := errors ++ [("XS0008", "depends is not allowed on branches")]
  if kind == "input" && has "pipe" then errors := errors ++ [("XS0008", "pipe is not allowed on input declarations")]
  if ["input", "with-input", "run-input", "variable", "with-option"].contains kind then
    if has "href" && has "pipe" then errors := errors ++ [("XS0085", "href and pipe cannot occur together")]
    if has "href" && !cs.isEmpty then errors := errors ++ [("XS0081", "href cannot accompany a connection child")]
    if has "pipe" && !cs.isEmpty then errors := errors ++ [("XS0082", "pipe cannot accompany a connection child")]
  if kind == "input" && cs.any (fun n => staticLocalName n == "pipe") then
    errors := errors ++ [("XS0100", "Input default cannot contain a pipe")]
  let ins := cs.filter (fun n => staticLocalName n == "input")
  let outs := cs.filter (fun n => staticLocalName n == "output")
  let ports := (ins ++ outs).map (fun n => staticAttr n "port")
  if ports.eraseDups.length != ports.length then errors := errors ++ [("XS0011", "Duplicate port name")]
  if (ins.filter (fun n => staticAttr n "primary" == "true")).length > 1 then
    errors := errors ++ [("XS0030", "More than one primary input")]
  if (outs.filter (fun n => staticAttr n "primary" == "true")).length > 1 then
    errors := errors ++ [("XS0014", "More than one primary output")]
  if ["declare-step", "group", "for-each", "viewport", "if", "when", "otherwise", "try", "catch", "finally"].contains kind then
    if let some last := (cs.filter isPipelineStep).getLast? then
      if primaryOutput (nodeDepth root + 1) declarations last == some none &&
          (outs.any (fun out => !hasExplicitConnection out) || (kind == "viewport" && outs.isEmpty)) &&
          staticLocalName last != "if" then
        errors := errors ++ [("XS0006", "Output has no default readable port")]
  if kind == "insert" then
    let insertion := cs.find? (fun c => staticLocalName c == "with-input" && staticAttr c "port" == "insertion")
    if !(insertion.any (fun n => hasExplicitConnection n || XML.hasAttr "pipe" n.elementAttrs)) then
      errors := errors ++ [("XS0032", "Required insertion input is not connected")]
  if kind == "if" && primaryOutput (nodeDepth root + 1) declarations root == some none then
    errors := errors ++ [("XS0108", "If must have a primary output port")]
  if !["inline", "documentation", "pipeinfo"].contains kind && (children root).any (fun c => match c with
      | .text t | .cdata t => !t.trimAscii.toString.isEmpty | _ => false) then
    errors := errors ++ [("XS0037", "Non-whitespace text is not allowed in pipeline structure")]
  if ["when", "choose", "if", "for-each", "viewport", "run"].contains kind && cs.any (fun c => staticLocalName c == "with-input" && XML.hasAttr "port" c.elementAttrs) then
    errors := errors ++ [("XS0043", "The context input port is anonymous")]
  if ["identity", "sink"].contains kind && cs.any (fun c => staticLocalName c == "with-input" &&
      XML.hasAttr "port" c.elementAttrs && staticAttr c "port" != "source") then
    errors := errors ++ [("XS0114", "Input port is not declared")]
  if kind == "declare-step" || kind == "library" then
    let mut seenPort := false
    for child in cs do
      if ["input", "output"].contains (staticLocalName child) then seenPort := true
      if seenPort && staticLocalName child == "import" then
        errors := errors ++ [("XS0100", "Imports must precede port declarations")]
  let bindings := cs.filter (fun n => staticLocalName n == "with-input" && staticAttr n "use-when" == "")
  let boundPorts := bindings.map (fun n => if staticAttr n "port" == "" then "source" else staticAttr n "port")
  let options := (cs.filter (fun n => ["with-option", "run-option"].contains (staticLocalName n))).map (fun n => nameKey n (staticAttr n "name"))
  if boundPorts.eraseDups.length != boundPorts.length then
    errors := errors ++ [("XS0086", "Input port is bound more than once")]
  if options.eraseDups.length != options.length then
    errors := errors ++ [("XS0080", "Option is bound more than once")]
  if ["group", "for-each", "viewport", "if", "when", "otherwise", "catch", "finally"].contains kind &&
      (cs.filter isPipelineStep).isEmpty then
    errors := errors ++ [("XS0015", "Compound subpipeline is empty")]
  if kind == "try" then
    let catches := cs.filter (fun c => staticLocalName c == "catch")
    let finals := cs.filter (fun c => staticLocalName c == "finally")
    if (cs.filter isPipelineStep).isEmpty || (catches.isEmpty && finals.isEmpty) || finals.length > 1 then
      errors := errors ++ [("XS0075", "Invalid try body or handler structure")]
    if catches.dropLast.any (fun c => !XML.hasAttr "code" c.elementAttrs) then
      errors := errors ++ [("XS0064", "Catch-all must be the last handler")]
    let codes := catches.flatMap (fun c => (words (staticAttr c "code")).map (nameKey c))
    if codes.eraseDups.length != codes.length then
      errors := errors ++ [("XS0064", "Duplicate catch error code")]
    let regularPorts := outs.map (fun o => staticAttr o "port") ++ catches.flatMap (fun c =>
      (c.allChildElements.filter (fun n => staticLocalName n == "output")).map (fun n => staticAttr n "port"))
    for final in finals do
      if (primaryOutput (nodeDepth final+1) declarations final).join.isSome then
        errors := errors ++ [("XS0112", "Finally cannot have a primary output")]
      let finalPorts := (final.allChildElements.filter (fun n => staticLocalName n == "output")).map (fun n => staticAttr n "port")
      if finalPorts.any (regularPorts.contains ·) then
        errors := errors ++ [("XS0072", "Finally output collides with a try or catch output")]
  if kind == "catch" && has "code" then
    let codes := words (staticAttr root "code")
    if codes.isEmpty || codes.any (fun c => !eqName c ||
        (XPath4.parseXPath ("$" ++ c) (nodeNamespaces root)).toOption.isNone) then
      errors := errors ++ [("XS0083", "Catch code must be a list of bound EQNames")]
  if kind == "choose" then
    let branches := cs.filter (fun n => ["when", "otherwise"].contains (staticLocalName n))
    if branches.isEmpty then errors := errors ++ [("XS0074", "Choose has no branches")]
    if branches.any (fun b => (b.allChildElements.filter isPipelineStep).isEmpty) then
      errors := errors ++ [("XS0015", "Compound subpipeline is empty")]
    let ports := branches.filterMap (primaryOutput (nodeDepth root + 1) declarations)
    if ports.eraseDups.length > 1 then errors := errors ++ [("XS0102", "Branch primary output ports differ")]
  return errors

private def syntaxErrorsAux : Nat → List String → List XML.Node → XML.Node → List (String × String)
  | 0, _, _, _ => []
  | f+1, inherited, decls, root => Id.run do
    let localDecls := root.allChildElements.filter (fun n => staticLocalName n == "declare-step")
    let declaredTypes := localDecls.map (fun d => nameKey d (staticAttr d "type"))
    let inheritedTypes := (decls.map (fun d => nameKey d (staticAttr d "type"))) ++
      (if staticAttr root "type" != "" then [nameKey root (staticAttr root "type")] else [])
    let duplicateTypes := declaredTypes.eraseDups.length != declaredTypes.length || declaredTypes.any (inheritedTypes.contains ·)
    let decls := localDecls ++ decls
    let cs := structuralChildren root
    let namedSteps := cs.filter (fun n => isPipelineStep n || isBranch n)
    let names := (namedSteps.map (fun n => staticAttr n "name")).filter (! ·.isEmpty)
    let outer := if staticAttr root "name" != "" && (isPipelineStep root || isBranch root || staticLocalName root == "declare-step") then
      staticAttr root "name" :: inherited else inherited
    let duplicate := names.eraseDups.length != names.length || names.any (outer.contains ·)
    let own := (if duplicateTypes then [("XS0036", "Step type is already declared in scope")] else []) ++
      localSyntaxErrors root decls ++
      (if duplicate then [("XS0002", "Step name is already in scope")] else [])
    return own ++ cs.flatMap (fun child =>
      syntaxErrorsAux f (if staticLocalName child == "declare-step" then [] else outer ++ names) decls child)

def syntaxErrors (root : XML.Node) : List (String × String) := syntaxErrorsAux (nodeDepth root) [] [] root

/-- Lexical step visibility. Branches of choose/try are separate scopes;
references to their current/error input are handled by their enclosing step. -/
private def scopeErrorsAux : Nat → List String → List String → XML.Node → List (String × String)
  | 0, _, _, _ => []
  | f+1, visible, inputs, root => Id.run do
    let name := staticAttr root "name"
    let ownVisible := visible.filter (· != name)
    let deps := words (staticAttr root "depends")
    let mut own := if deps.any (fun d => !ownVisible.contains d) then
      [("XS0073", "depends names a step outside its scope")] else []
    let pipeNames := (words (staticAttr root "pipe")).map sourceName ++
      (if staticLocalName root == "pipe" then [staticAttr root "step"] else [])
    if pipeNames.any (fun n => n != "" && !visible.contains n && !inputs.contains n) then
      own := own ++ [("XS0022", "Pipe names a step outside its scope")]
    let steps := root.allChildElements.filter isPipelineStep
    let childNames := (steps.map (fun n => staticAttr n "name")).filter (! ·.isEmpty)
    let compound := ["declare-step", "group", "for-each", "viewport", "choose", "when", "otherwise", "if", "try", "catch", "finally"].contains (staticLocalName root)
    let innerVisible := if compound then ownVisible ++ childNames else visible
    let innerInputs := if compound && name != "" then name :: inputs else inputs
    return own ++ (structuralChildren root).flatMap (fun child =>
      if staticLocalName child == "declare-step" then scopeErrorsAux f [] [] child
      else scopeErrorsAux f innerVisible innerInputs child)

private abbrev NameKey := String × String

private def knownFunction (q : XPath4.QN) : Bool :=
  q.uri != "http://www.w3.org/2005/xpath-functions" ||
    XPath4.catalogRaw.any (fun row => row.1 == "fn" && row.2.1 == q.loc)

/-- Check variable binding and unknown functions in the standard function
namespace. Imported/custom functions are checked by their host registry. -/
private def expressionNamesValid : Nat → List NameKey → XPath4.Expr → Bool
  | 0, _, _ => true
  | f+1, bound, e =>
    let valid := expressionNamesValid f bound
    match e with
    | .var q => bound.contains (q.uri, q.loc)
    | .seq es | .arrS es | .tmpl es => es.all valid
    | .step _ _ ps => ps.all valid
    | .dstep _ e ps => valid e && ps.all valid
    | .slash a b | .filter a b | .smap a b | .pipe a b | .bin _ a b => valid a && valid b
    | .arrC a | .neg a | .plus a | .instOf a _ | .treat a _ | .cast a _ _ | .castable a _ _ => valid a
    | .lookup a k => valid a && k.all valid
    | .ulookup k => k.all valid
    | .ifE a b c => valid a && valid b && valid c
    | .mapC es => es.all (fun (a,b) => valid a && valid b)
    | .call q args kw => knownFunction q && args.all (fun a => a.all valid) && kw.all (fun a => a.2.all valid)
    | .dyn a args => valid a && args.all (fun a => a.all valid)
    | .mapArrow a fn args => valid a && valid fn && args.all (fun a => a.all valid)
    | .fref q _ => knownFunction q
    | .forE _ q q2 pos _ src body => valid src && expressionNamesValid f
        ((q.uri, q.loc) :: ((q2.toList ++ pos.toList).map (fun n => (n.uri, n.loc))) ++ bound) body
    | .letE q _ src body | .quant _ q _ src body =>
        valid src && expressionNamesValid f ((q.uri, q.loc) :: bound) body
    | .inline ps _ body _ => expressionNamesValid f ((ps.map (fun p => (p.1.uri, p.1.loc))) ++ bound) body
    | .ext _ es _ _ _ => es.all valid
    | _ => true

private def variableErrorsAux : Nat → List NameKey → List NameKey → XML.Node → List (String × String)
  | 0, _, _, _ => []
  | f+1, inheritedVars, inheritedStatic, root => Id.run do
    let mut vars := inheritedVars
    let mut statics := inheritedStatic
    let mut errors := []
    for child in structuralChildren root do
      let kind := staticLocalName child
      let isDecl := kind == "option" || kind == "variable"
      let key := nameKey child (staticAttr child "name")
      if isDecl && statics.contains key then
        errors := errors ++ [(if kind == "option" then "XS0088" else "XS0091", "Static option cannot be shadowed")]
      if isDecl && XML.hasAttr "select" child.elementAttrs then
        let text := staticAttr child "select"
        match XPath4.parseXPath text (nodeNamespaces child) with
        | .ok expr =>
          let env := if kind == "option" && staticAttr child "static" == "true" then statics else vars
          if !expressionNamesValid (text.length+1) env expr then
            errors := errors ++ [("XS0107", "Unbound variable or unknown function in declaration")]
        | .error _ => pure () -- The lexical diagnostic is emitted by localSyntaxErrors.
      errors := errors ++ variableErrorsAux f
        (if kind == "declare-step" then statics else vars) statics child
      if isDecl then
        vars := key :: vars
        if kind == "option" && staticAttr child "static" == "true" then statics := key :: statics
    return errors

/-- Track whether a default readable port exists, not whether its runtime
sequence is empty. Unknown extension signatures remain unknown/available so
this conservative check cannot reject them merely for lacking a catalog entry. -/
private def inputConnectionErrors : Nat → List XML.Node → Bool → XML.Node → List (String × String)
  | 0, _, _, _ => []
  | fuel+1, declarations, incoming, root => Id.run do
    let kind := staticLocalName root
    let cs := structuralChildren root
    let declarations := cs.filter (fun c => staticLocalName c == "declare-step") ++ declarations
    let inputs := cs.filter (fun c => staticLocalName c == "input")
    let mut available := if kind == "declare-step" then
      inputs.any (fun c => staticAttr c "primary" == "true" ||
        (inputs.length == 1 && staticAttr c "primary" != "false"))
      else if kind == "catch" then true else incoming
    let mut errors := []
    for c in cs.filter (fun c => staticLocalName c == "declare-step") do
      errors := errors ++ inputConnectionErrors fuel declarations false c
    for step in cs do
      let stepKind := staticLocalName step
      let bindings := if stepKind == "variable" then [step] else
        step.allChildElements.filter (fun c => ["with-input", "with-option"].contains (staticLocalName c))
      for binding in bindings do
        if XML.hasAttr "pipe" binding.elementAttrs && (words (staticAttr binding "pipe")).isEmpty && !available then
          errors := errors ++ [("XS0067", "Explicit default connection has no readable port")]
        let targets := ((words (staticAttr binding "pipe")).filter (·.startsWith "@")).map (fun p => (p.drop 1).toString) ++
          (binding.allChildElements.filter (fun p => staticLocalName p == "pipe" && !XML.hasAttr "port" p.elementAttrs)).map (staticAttr · "step")
        for target in targets do
          if target != "" then
            if let some producer := cs.find? (fun n => isPipelineStep n && staticAttr n "name" == target) then
              if primaryOutput (nodeDepth producer+1) declarations producer == some none then
                errors := errors ++ [("XS0068", "Referenced step has no primary output port")]
      if !isPipelineStep step then continue
      let source := step.allChildElements.find? (fun c => staticLocalName c == "with-input" &&
        (staticAttr c "port" == "" || staticAttr c "port" == "source"))
      let connected := source.any hasExplicitConnection || available
      if stepKind == "identity" && !connected then
        errors := errors ++ [(if source.any (fun c => XML.hasAttr "pipe" c.elementAttrs) then "XS0067" else "XS0032",
          "Primary input has no connection or default readable port")]
      if ["group", "for-each", "viewport", "if", "try"].contains stepKind then
        errors := errors ++ inputConnectionErrors fuel declarations
          (if ["for-each", "viewport"].contains stepKind then connected else available) step
      if stepKind == "choose" || stepKind == "try" then
        for branch in step.allChildElements.filter isBranch do
          errors := errors ++ inputConnectionErrors fuel declarations available branch
      available := (primaryOutput (nodeDepth step + 1) declarations step).map Option.isSome |>.getD true
    return errors

/-- Cycle diagnostics in each subpipeline, after lexical and scope checks. -/
def staticErrorsAux : Nat → XML.Node → List (String × String)
  | 0, _ => []
  | fuel + 1, root => Id.run do
    let selfRefs := (root.allChildElements.filter isPipelineStep).filter (fun step =>
      staticAttr step "name" != "" && (referencedSteps step).contains (staticAttr step "name"))
    let own := if !selfRefs.isEmpty then [("XS0022", "A step output is not visible to itself")]
      else if connectionCycle (pipelineConnections root) then
      [("XS0001", "Cycle in pipeline connections")] else []
    let nested := root.allChildElements.filter fun n =>
      ["group", "for-each", "viewport", "choose", "when", "otherwise", "if", "try", "catch", "finally",
        "declare-step"].contains (staticLocalName n)
    return own ++ nested.flatMap (staticErrorsAux fuel)

/-- Inline controls are checked inside literal content without treating that
content as pipeline structure. Only attributes in the XProc namespace act as
controls on literal or extension elements. -/
private def controlErrors : Nat → Bool → XML.Node → List (String × String)
  | 0, _, _ => []
  | fuel+1, literal, node => Id.run do
    let kind := staticLocalName node
    if !literal && ["documentation", "pipeinfo"].contains kind then return []
    let mut errors := []
    for a in node.elementAttrs do
      let (pfx, loc) := XPath4.splitName a.name
      let qualified := pfx != "" && ((ns node).lookup pfx).getD "" == "http://www.w3.org/ns/xproc"
      let standard := !literal && kind != "#extension" && pfx == ""
      if !literal && kind != "inline" && loc == "inline-expand-text" && (standard || qualified) then
        errors := errors ++ [(if standard then "XS0008" else "XS0031", "Inline expansion control is outside inline content")]

      if (standard && loc == "expand-text") || (qualified && ["expand-text", "inline-expand-text"].contains loc) then
        if !["true", "false"].contains a.value then
          errors := errors ++ [("XS0113", "Text expansion control must be a static boolean")]
      if (standard || qualified) && loc == "exclude-inline-prefixes" then
        let prefixes := words a.value
        if prefixes.any (fun p => p != "#all" && p != "#default" &&
            (p != "xml" && ((ns node).lookup p).isNone)) then
          errors := errors ++ [("XS0057", "Excluded namespace prefix is not bound")]
        if prefixes.contains "#default" && ((ns node).lookup "").getD "" == "" then
          errors := errors ++ [("XS0058", "No default namespace is bound")]
    for child in node.allChildElements do
      let childLiteral := literal || kind == "inline" ||
        (["input", "output", "with-input", "run-input", "variable", "with-option"].contains kind && staticLocalName child == "#extension")
      errors := errors ++ controlErrors fuel childLiteral child
    return errors

def staticErrors (root : XML.Node) (imports : List XML.Node := []) : List (String × String) :=
  let root := inheritNamespaces (nodeDepth root) [] root
  let version := if ["declare-step", "library"].contains (staticLocalName root) && !XML.hasAttr "version" root.elementAttrs then
    [("XS0062", "The outer pipeline must declare its version")] else []
  let outer := if !["declare-step", "library"].contains (staticLocalName root) then
    [("XS0059", "Pipeline root must be declare-step or library")] else []
  let importedOptions := (imports.filter (fun n => staticLocalName n == "option" && staticAttr n "static" == "true")).map (fun n => nameKey n (staticAttr n "name"))
  let diagnostics := syntaxErrors root
  -- Reject malformed structure before deriving port signatures from it.
  let structural := fun e : String × String =>
    ["XS0008", "XS0015", "XS0038", "XS0074", "XS0075", "XS0077", "XS0087", "XS0096"].contains e.1
  outer ++ version ++ controlErrors (nodeDepth root) false root ++
    diagnostics.filter structural ++ diagnostics.filter (fun e => !structural e) ++ variableErrorsAux (nodeDepth root) importedOptions importedOptions root ++ scopeErrorsAux (nodeDepth root) [] [] root ++ inputConnectionErrors (nodeDepth root) [] false root ++ staticErrorsAux (nodeDepth root) root

/-- Validate extension calls within one source's lexical scope. Imported
bodies are checked separately in their own source, never in the importing
pipeline's enlarged scope. Nested imports require their own loader check. -/
private def importScopeErrorsAux : Nat → List NameKey → Bool → XML.Node → List (String × String)
  | 0, _, _, _ => []
  | fuel+1, visible, unresolvedImports, node => Id.run do
    let cs := structuralChildren node
    let locals := cs.filter (fun c => staticLocalName c == "declare-step" && staticAttr c "type" != "")
    let localNames := locals.map (fun c => nameKey c (staticAttr c "type"))
    let known := localNames ++ visible
    let mut errors := []
    if localNames.eraseDups.length != localNames.length || localNames.any visible.contains then
      errors := errors ++ [("XS0036", "Declared and imported step types overlap")]
    if !unresolvedImports && isPipelineStep node && staticLocalName node == "#extension" &&
        !known.contains (nameKey node (node.elementTag.getD "")) then
      errors := errors ++ [("XS0044", "Step type is not visible in this source")]
    for child in cs do
      let childImports := (structuralChildren child).any (fun n => staticLocalName n == "import")
      errors := errors ++ importScopeErrorsAux fuel known (unresolvedImports || childImports) child
    return errors

/-- Check one source after its direct imports are resolved. The caller must
remove repeated imports by source identity, not by step QName. Distinct source
files exporting the same type are conflicting declarations. Stand-alone
imported pipelines require a type, even though a principal pipeline need not.
Private declarations remain visible within their own library; the loader
selects exports before passing them as another source's imports. -/
def importScopeErrors (root : XML.Node) (imports : List XML.Node)
    (importedSource : Bool := false) : List (String × String) := Id.run do
  let root := inheritNamespaces (nodeDepth root) [] root
  let importedNames := imports.filterMap fun d =>
    if staticAttr d "type" == "" then none else some (nameKey d (staticAttr d "type"))
  let ownType := if staticAttr root "type" == "" then [] else [nameKey root (staticAttr root "type")]
  let names := ownType ++ importedNames
  let mut errors := []
  let importedOptions := (imports.filter (fun n => staticLocalName n == "option")).map (fun n => nameKey n (staticAttr n "name"))
  if importedOptions.eraseDups.length != importedOptions.length then
    errors := errors ++ [("XS0109", "Imported libraries export the same option name")]
  if (root.allChildElements.filter (fun n => staticLocalName n == "option")).any
      (fun n => importedOptions.contains (nameKey n (staticAttr n "name"))) then
    errors := errors ++ [("XS0088", "Imported static option cannot be shadowed")]

  if importedSource && staticLocalName root == "declare-step" && staticAttr root "type" == "" then
    errors := errors ++ [("XS0044", "Imported pipeline has no step type")]
  if names.eraseDups.length != names.length then
    errors := errors ++ [("XS0036", "Imported step types overlap")]
  return errors ++ importScopeErrorsAux (nodeDepth root) names false root

private def testElement (name : String) (attrs : List XML.Attribute) (children : List XML.Node) : XML.Node :=
  .element name (⟨"xmlns:p", "http://www.w3.org/ns/xproc"⟩ :: attrs) children

-- Regression cases: lexical validation, forward DAGs, and inline focus.
#guard templateNeedsFocus "prefix{ . }suffix"
#guard !templateNeedsFocus "{{.}}"
#guard !templateNeedsFocus "{42}"
#guard templateNeedsFocus "{string()}"
#guard (staticErrors (testElement "p:declare-step" []
  [testElement "p:input" [⟨"port", "source"⟩, ⟨"primary", "yes"⟩] []])).any (fun e => e.1 == "XS0077")
#guard (staticErrors (testElement "p:declare-step" []
  [testElement "p:identity" [⟨"name", "same"⟩] [],
   testElement "p:identity" [⟨"name", "same"⟩] []])).any (fun e => e.1 == "XS0002")
#guard (staticErrors (testElement "p:declare-step" [⟨"version", "3.0"⟩]
  [testElement "p:output" [⟨"port", "result"⟩]
    [.element "otherwise" [] []], testElement "p:identity" []
      [testElement "p:with-input" [] [.element "doc" [] []]]])).isEmpty

#guard (localSyntaxErrors (testElement "p:try" []
  [testElement "p:catch" [] [testElement "p:identity" [] []]]) []).any (fun e => e.1 == "XS0075")
#guard (localSyntaxErrors (testElement "p:try" []
  [testElement "p:identity" [] [],
   testElement "p:catch" [⟨"code", "a"⟩] [testElement "p:identity" [] []],
   testElement "p:catch" [⟨"code", "Q{}a"⟩] [testElement "p:identity" [] []]]) []).any (fun e => e.1 == "XS0064")
#guard (localSyntaxErrors (testElement "p:try" []
  [testElement "p:identity" [] [], testElement "p:finally" [] [testElement "p:sink" [] []]]) []).isEmpty

-- Literal bindings must never become pipeline references, even when their
-- element names and attributes resemble XProc syntax. Namespace inheritance
-- applies to aliases; an explicit default namespace reset remains literal.
private def namespaceRegression (literal : XML.Node) : XML.Node :=
  .element "x:declare-step" [⟨"xmlns:x", "http://www.w3.org/ns/xproc"⟩, ⟨"version", "3.0"⟩]
    [.element "x:output" [⟨"port", "result"⟩] [],
     .element "x:identity" [⟨"name", "producer"⟩]
       [.element "x:with-input" [] [literal]]]

#guard (staticErrors (namespaceRegression (.element "pipe"
  [⟨"step", "missing"⟩, ⟨"port", "x"⟩] []))).isEmpty
#guard (staticErrors (namespaceRegression (.element "e:pipe"
  [⟨"xmlns:e", "urn:literal"⟩, ⟨"step", "producer"⟩] []))).isEmpty
#guard (staticErrors (namespaceRegression (.element "x:pipe"
  [⟨"step", "missing"⟩, ⟨"port", "x"⟩] []))).any (fun e => e.1 == "XS0022")
#guard (staticErrors (namespaceRegression (.element "x:inline" []
  [.element "x:pipe" [⟨"step", "missing"⟩] []]))).isEmpty
#guard (staticErrors (.element "declare-step"
  [⟨"xmlns", "http://www.w3.org/ns/xproc"⟩, ⟨"version", "3.0"⟩]
  [.element "identity" [] [.element "with-input" []
    [.element "pipe" [⟨"xmlns", ""⟩, ⟨"step", "missing"⟩] []]]])).isEmpty
#guard isPipelineStep (.element "e:output" [⟨"xmlns:e", "urn:extension"⟩] [])

-- Connection availability is distinct from runtime sequence cardinality.
private def portRegression (body : List XML.Node) : XML.Node :=
  testElement "p:declare-step" [⟨"version", "3.0"⟩]
    (testElement "p:output" [⟨"port", "result"⟩] [] :: body)

#guard (staticErrors (portRegression [testElement "p:identity" [] []])).any (fun e => e.1 == "XS0032")
#guard (staticErrors (portRegression [testElement "p:identity" []
  [testElement "p:with-input" [⟨"pipe", ""⟩] []]])).any (fun e => e.1 == "XS0067")
#guard (staticErrors (portRegression [testElement "p:identity" []
  [testElement "p:with-input" [] [testElement "p:empty" [] []]]])).isEmpty
#guard (staticErrors (portRegression [testElement "p:identity" []
  [testElement "p:with-input" [] [.element "doc" [] []]],
  testElement "p:sink" [] []])).any (fun e => e.1 == "XS0006")
#guard (staticErrors (portRegression [testElement "p:insert" []
  [testElement "p:with-input" [] [.element "doc" [] []]]])).any (fun e => e.1 == "XS0032")
#guard (staticErrors (portRegression [testElement "p:insert" []
  [testElement "p:with-input" [] [.element "doc" [] []],
   testElement "p:with-input" [⟨"port", "insertion"⟩] [testElement "p:empty" [] []]]])).isEmpty

private def secondaryRegression (fallback : List XML.Node) : XML.Node :=
  portRegression
    [testElement "p:declare-step" [⟨"type", "e:test"⟩, ⟨"xmlns:e", "urn:test"⟩]
      [testElement "p:input" [⟨"port", "source"⟩, ⟨"primary", "true"⟩] [],
       testElement "p:input" [⟨"port", "secondary"⟩] fallback,
       testElement "p:output" [⟨"port", "result"⟩] [], testElement "p:identity" [] []],
     .element "e:test" [⟨"xmlns:e", "urn:test"⟩]
       [testElement "p:with-input" [] [.element "doc" [] []]]]

#guard (staticErrors (secondaryRegression [])).any (fun e => e.1 == "XS0032")
#guard (staticErrors (secondaryRegression [testElement "p:empty" [] []])).isEmpty

private def bindingRegression (nodes : List XML.Node) : XML.Node :=
  portRegression [testElement "p:identity" [] [testElement "p:with-input" [] nodes]]

#guard (staticErrors (bindingRegression [testElement "p:empty" [] [], .element "doc" [] []])).any (fun e => e.1 == "XS0089")
#guard (staticErrors (bindingRegression [testElement "p:inline" [] [.element "doc" [] []],
  .element "other" [] []])).any (fun e => e.1 == "XS0100")
#guard (staticErrors (bindingRegression [testElement "p:declare-step" [] []])).any (fun e => e.1 == "XS0100")
#guard (staticErrors (bindingRegression [.comment "not allowed", .element "doc" [] []])).any (fun e => e.1 == "XS0079")
#guard (staticErrors (bindingRegression [.element "doc" [] [.comment "inside is allowed"]])).isEmpty
#guard (staticErrors (bindingRegression [testElement "p:inline" [] [testElement "p:declare-step" [] []]])).isEmpty
#guard (localSyntaxErrors (testElement "p:run" []
  [testElement "p:with-input" [] [], testElement "p:run-input" [⟨"port", "source"⟩] [],
   testElement "p:run-input" [⟨"port", "source"⟩] []]) []).any (fun e => e.1 == "XS0086")
#guard (localSyntaxErrors (testElement "p:run-input" [] []) []).any (fun e => e.1 == "XS0038")
#guard (localSyntaxErrors (testElement "p:run" [] []) []).any (fun e => e.1 == "XS0003")
#guard (localSyntaxErrors (testElement "p:run" []
  [testElement "p:with-input" [] [],
   testElement "p:run-option" [⟨"name", "a:x"⟩, ⟨"xmlns:a", "urn:option"⟩, ⟨"select", "1"⟩] [],
   testElement "p:run-option" [⟨"name", "b:x"⟩, ⟨"xmlns:b", "urn:option"⟩, ⟨"select", "2"⟩] []]) []).any (fun e => e.1 == "XS0080")

-- Pipeline structure and inline controls have different namespace rules.
#guard (staticErrors (portRegression [.text "illegal", testElement "p:identity" []
  [testElement "p:with-input" [] [.element "doc" [] []]]])).any (fun e => e.1 == "XS0037")
#guard (staticErrors (bindingRegression [.element "doc" [] [.text "ordinary data"]])).isEmpty
#guard (staticErrors (bindingRegression [.element "doc" [⟨"expand-text", "no"⟩] []])).isEmpty
#guard (staticErrors (bindingRegression [.element "doc"
  [⟨"xmlns:x", "http://www.w3.org/ns/xproc"⟩, ⟨"x:inline-expand-text", "no"⟩] []])).any (fun e => e.1 == "XS0113")
#guard (staticErrors (portRegression [testElement "p:identity" [⟨"expand-text", "{true()}"⟩]
  [testElement "p:with-input" [] [.element "doc" [] []]]])).any (fun e => e.1 == "XS0113")
#guard (localSyntaxErrors (testElement "p:declare-step" []
  [testElement "p:output" [⟨"port", "result"⟩] [], testElement "p:import" [⟨"href", "lib.xpl"⟩] []]) []).any (fun e => e.1 == "XS0100")
#guard (controlErrors 4 false (testElement "p:with-input" [⟨"exclude-inline-prefixes", "missing"⟩] [])).any (fun e => e.1 == "XS0057")
#guard (controlErrors 4 false (testElement "p:with-input" [⟨"exclude-inline-prefixes", "#default"⟩] [])).any (fun e => e.1 == "XS0058")
#guard (controlErrors 4 false (testElement "p:with-input"
  [⟨"exclude-inline-prefixes", "#default p xml"⟩, ⟨"xmlns", "urn:default"⟩] [])).isEmpty
#guard (staticErrors (testElement "p:boxing-day" [] [])).any (fun e => e.1 == "XS0059")

private def importRegressionDecl (pfx : String) : XML.Node :=
  testElement "p:declare-step" [⟨"type", pfx ++ ":step"⟩, ⟨"xmlns:" ++ pfx, "urn:import"⟩] []

#guard (importScopeErrors (testElement "p:declare-step" [] []) [] true).any (fun e => e.1 == "XS0044")
#guard (importScopeErrors (testElement "p:declare-step" [] []) [] false).isEmpty
#guard (importScopeErrors (importRegressionDecl "a") [importRegressionDecl "b"]).any (fun e => e.1 == "XS0036")
#guard (importScopeErrors (testElement "p:declare-step" [] [importRegressionDecl "a"])
  [importRegressionDecl "b"]).any (fun e => e.1 == "XS0036")
#guard (importScopeErrors (testElement "p:declare-step" []
  [.element "b:step" [⟨"xmlns:b", "urn:import"⟩] []]) [importRegressionDecl "a"]).isEmpty
#guard (importScopeErrors (testElement "p:declare-step" []
  [.element "b:step" [⟨"xmlns:b", "urn:import"⟩] []]) []).any (fun e => e.1 == "XS0044")
#guard (importScopeErrors (bindingRegression [.element "unknown:literal" [] []]) []).isEmpty

#guard !(typePrefixesBound (testElement "p:option" [] []) "xs:boolean")
#guard typePrefixesBound (testElement "p:option" [⟨"xmlns:xs", "http://www.w3.org/2001/XMLSchema"⟩] []) "xs:boolean"
#guard typePrefixesBound (testElement "p:option" [] []) "Q{http://www.w3.org/2001/XMLSchema}boolean"
#guard (importScopeErrors (testElement "p:declare-step" [] [])
  [testElement "p:option" [⟨"name", "x"⟩, ⟨"static", "true"⟩] [],
   testElement "p:option" [⟨"name", "x"⟩, ⟨"static", "true"⟩] []]).any (fun e => e.1 == "XS0109")
#guard (importScopeErrors (testElement "p:declare-step" []
  [testElement "p:option" [⟨"name", "x"⟩] []])
  [testElement "p:option" [⟨"name", "x"⟩, ⟨"static", "true"⟩] []]).any (fun e => e.1 == "XS0088")

private def missingPrimaryRegression (connection : XML.Node) : XML.Node :=
  portRegression [testElement "p:identity" [⟨"name", "producer"⟩]
    [testElement "p:with-input" [] [.element "doc" [] []]],
    testElement "p:sink" [⟨"name", "stop"⟩] [], connection,
    testElement "p:identity" [] [testElement "p:with-input" [] [.element "result" [] []]]]

#guard (staticErrors (missingPrimaryRegression (testElement "p:variable"
  [⟨"name", "v"⟩, ⟨"select", "42"⟩, ⟨"pipe", ""⟩] []))).any (fun e => e.1 == "XS0067")
#guard (staticErrors (missingPrimaryRegression (testElement "p:variable"
  [⟨"name", "v"⟩, ⟨"select", "42"⟩, ⟨"pipe", "@stop"⟩] []))).any (fun e => e.1 == "XS0068")
#guard (staticErrors (missingPrimaryRegression (testElement "p:variable"
  [⟨"name", "v"⟩, ⟨"select", "42"⟩] [testElement "p:pipe" [⟨"step", "stop"⟩] []]))).any (fun e => e.1 == "XS0068")
#guard (staticErrors (missingPrimaryRegression (testElement "p:variable"
  [⟨"name", "v"⟩, ⟨"select", "42"⟩, ⟨"pipe", "@producer"⟩] []))).isEmpty
#guard (localSyntaxErrors (testElement "p:input" [] []) []).any (fun e => e.1 == "XS0038")
#guard (localSyntaxErrors (testElement "p:if" [] []) []).any (fun e => e.1 == "XS0038")
#guard (localSyntaxErrors (testElement "p:library" [⟨"version", "C"⟩] []) []).any (fun e => e.1 == "XS0063")

end L4Factoidal.XProc31
