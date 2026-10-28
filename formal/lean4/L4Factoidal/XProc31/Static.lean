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

private def staticAttr (node : XML.Node) (name : String) : String :=
  ((XML.findAttr name node.elementAttrs).orElse fun _ =>
    if name == "depends" && !(node.elementTag.getD "").startsWith "p:" then
      XML.findAttr "p:depends" node.elementAttrs else none).getD ""

private def staticLocalName (node : XML.Node) : String :=
  ((node.elementTag.getD "").splitOn ":").getLast!

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
      if staticLocalName node == "with-input" then
        ["pipe", "empty", "document"].contains (staticLocalName c)
      else true
    return (own ++ children.flatMap (referencedStepsAux fuel)).filter (! ·.isEmpty)

def referencedSteps (node : XML.Node) : List String := referencedStepsAux (nodeDepth node) node

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

private def inheritNamespaces : Nat → List XML.Attribute → XML.Node → XML.Node
  | 0, _, n => n
  | f+1, inherited, .element t attrs cs =>
    let attrs := attrs ++ inherited.filter (fun a => !attrs.any (fun b => a.name == b.name))
    let ns := attrs.filter (fun a => a.name == "xmlns" || a.name.startsWith "xmlns:")
    .element t attrs (cs.map (inheritNamespaces f ns))
  | _, _, n => n

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
    else match declarations.find? (fun d => staticAttr d "type" == node.elementTag.getD "") with
      | some d => primaryOutput f declarations d
      | none =>
        if (node.elementTag.getD "").startsWith "p:" then some (some "result") else none

private def localSyntaxErrors (root : XML.Node) (declarations : List XML.Node) : List (String × String) := Id.run do
  let kind := staticLocalName root
  let has := fun a => XML.hasAttr a root.elementAttrs ||
    (a == "depends" && !(root.elementTag.getD "").startsWith "p:" && XML.hasAttr "p:depends" root.elementAttrs)
  let cs := root.allChildElements.filter (fun n => !["documentation", "pipeinfo"].contains (staticLocalName n))
  let mut errors := []
  if ["input", "output", "with-input", "run-input"].contains kind && has "content-types" then
    match validateDeclaredContentTypes (staticAttr root "content-types") with
    | .error e => errors := errors ++ [(e.code, e.message)]
    | .ok _ => pure ()
  if ["declare-step", "library"].contains kind && has "version" && !supportedVersion (staticAttr root "version") then
    errors := errors ++ [("XS0060", "Unsupported XProc version")]
  if ["option", "variable"].contains kind then
    if !has "name" || (kind == "variable" && !has "select") then
      errors := errors ++ [("XS0038", "Required declaration attribute is missing")]
    if has "name" && eqName (staticAttr root "name") then
      match XPath4.parseXPath ("$" ++ staticAttr root "name") (nodeNamespaces root) with
      | .ok (.var q) =>
        if q.uri == "http://www.w3.org/ns/xproc" then
          errors := errors ++ [("XS0028", "Option or variable name is in the XProc namespace")]
      | .error e =>
        if e.code == "XPST0081" then errors := errors ++ [("XS0087", "Undeclared name prefix")]
      | _ => pure ()
    if has "as" && (XPath4.parseXPath ("() instance of " ++ staticAttr root "as") (nodeNamespaces root)).toOption.isNone then
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
  if optNames.eraseDups.length != optNames.length then errors := errors ++ [("XS0004", "Duplicate option name")]
  if (root.elementTag.getD "").startsWith "p:" && XML.hasAttr "p:depends" root.elementAttrs then
    errors := errors ++ [("XS0097", "XProc steps use unprefixed depends")]
  if kind == "with-option" && staticAttr root "name" == "p:depends" then
    errors := errors ++ [("XS0031", "depends is not a step option")]
  let globalAttrs := ["name", "depends", "use-when", "expand-text", "exclude-inline-prefixes", "version", "psvi-required", "xpath-version"]
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
  let boolAttrs := if ["input", "output", "option", "variable", "with-option", "when", "if"].contains kind then
    ["primary", "sequence", "static", "required", "collection"] else []
  if boolAttrs.any (fun a => has a && !["true", "false"].contains (staticAttr root a)) then
    errors := errors ++ [("XS0077", "Invalid static boolean attribute")]
  if has "depends" && ((words (staticAttr root "depends")).isEmpty || !(words (staticAttr root "depends")).all ncName) then
    errors := errors ++ [("XS0077", "depends requires a nonempty list of NCNames")]
  if has "port" && ["input", "output", "with-input", "pipe"].contains kind && !ncName (staticAttr root "port") then
    errors := errors ++ [("XS0077", "Invalid port NCName")]
  if has "name" && ["option", "variable", "declare-step"].contains kind && !eqName (staticAttr root "name") then
    errors := errors ++ [("XS0077", "Invalid name")]
  if has "type" && kind == "declare-step" && !eqName (staticAttr root "type") then
    errors := errors ++ [("XS0077", "Invalid step type EQName")]
  if kind == "option" && has "visibility" && !["public", "private"].contains (staticAttr root "visibility") then
    errors := errors ++ [("XS0077", "Invalid option visibility")]
  if isBranch root && has "depends" then errors := errors ++ [("XS0008", "depends is not allowed on branches")]
  if kind == "input" && has "pipe" then errors := errors ++ [("XS0008", "pipe is not allowed on input declarations")]
  if ["input", "with-input", "variable", "with-option"].contains kind then
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
  let bindings := cs.filter (fun n => staticLocalName n == "with-input" && staticAttr n "use-when" == "")
  let boundPorts := bindings.map (fun n => if staticAttr n "port" == "" then "source" else staticAttr n "port")
  let options := (cs.filter (fun n => ["with-option", "run-option"].contains (staticLocalName n))).map (fun n => staticAttr n "name")
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

def staticErrors (root : XML.Node) : List (String × String) :=
  let root := inheritNamespaces (nodeDepth root) [] root
  let version := if ["declare-step", "library"].contains (staticLocalName root) && !XML.hasAttr "version" root.elementAttrs then
    [("XS0062", "The outer pipeline must declare its version")] else []
  version ++ syntaxErrors root ++ variableErrorsAux (nodeDepth root) [] [] root ++ scopeErrorsAux (nodeDepth root) [] [] root ++ staticErrorsAux (nodeDepth root) root

-- Regression cases: lexical validation, forward DAGs, and inline focus.
#guard templateNeedsFocus "prefix{ . }suffix"
#guard !templateNeedsFocus "{{.}}"
#guard !templateNeedsFocus "{42}"
#guard templateNeedsFocus "{string()}"
#guard (staticErrors (.element "p:declare-step" []
  [.element "p:input" [⟨"port", "source"⟩, ⟨"primary", "yes"⟩] []])).any (fun e => e.1 == "XS0077")
#guard (staticErrors (.element "p:declare-step" []
  [.element "p:identity" [⟨"name", "same"⟩] [],
   .element "p:identity" [⟨"name", "same"⟩] []])).any (fun e => e.1 == "XS0002")
#guard (staticErrors (.element "p:declare-step" [⟨"version", "3.0"⟩]
  [.element "p:output" [⟨"port", "result"⟩]
    [.element "otherwise" [] []], .element "p:identity" [] []])).isEmpty

#guard (localSyntaxErrors (.element "p:try" []
  [.element "p:catch" [] [.element "p:identity" [] []]]) []).any (fun e => e.1 == "XS0075")
#guard (localSyntaxErrors (.element "p:try" []
  [.element "p:identity" [] [],
   .element "p:catch" [⟨"code", "a"⟩] [.element "p:identity" [] []],
   .element "p:catch" [⟨"code", "Q{}a"⟩] [.element "p:identity" [] []]]) []).any (fun e => e.1 == "XS0064")
#guard (localSyntaxErrors (.element "p:try" []
  [.element "p:identity" [] [], .element "p:finally" [] [.element "p:sink" [] []]]) []).isEmpty

end L4Factoidal.XProc31
