import L4Factoidal.XML.Encoding
import L4Factoidal.XProc31.Properties
import L4Factoidal.XProc31.Core
import L4Factoidal.XML.Theorems
import L4Factoidal.XSLT4.Package
import L4Factoidal.XSLT4.Transform
import L4Factoidal.XQuery4.Module
import L4Factoidal.XSD11.Load

namespace L4Factoidal.XProc31
open XML

def evalXslt (sheet : XSLT4.Sheet) (opts : XSLT4.TOpts) : XPath4.M XSLT4.TResult :=
  XSLT4.transform sheet opts

def evalXquery (query : String) (env : XPath4.Env) : XPath4.M XPath4.Seq :=
  XQuery4.evalQuery query env

def oneSource (docs : List Document) : Result Document :=
  match docs with
  | [d] => pure d
  | _ => error "XD0006" "port requires exactly one document"

def resultDoc (s : String) : Document :=
  ⟨.element "c:result" [⟨"xmlns:c", "http://www.w3.org/ns/xproc-step"⟩] [.text s], "application/xml", "", [], none⟩

def qnameOption (step : Node) (name : String) (env : XPath4.Env) : Result String := do
  match (named step "with-option").find? (fun n => attr n "name" == name) with
  | none => option step name env ""
  | some n =>
    let value ← eval (attr n "select") env
    match value with
    | [.atom a] => match a.v with
      | .qn q => pure q.eqn
      | _ => pure (seqString env value)
    | _ => pure (seqString env value)

def qualify (step : Node) (lex pfx uri : String) : Result (String × List XML.Attribute) := do
  let expanded := if lex.startsWith "Q{" then ((lex.drop 2).toString.splitOn "}") else []
  let (p,l) := if expanded.length == 2 then ("", expanded[1]!) else XPath4.splitName lex
  let u := if expanded.length == 2 then expanded[0]! else if uri != "" then uri
    else if p == "xml" then "http://www.w3.org/XML/1998/namespace" else ((ns step).lookup p).getD ""
  let p := if pfx != "" then pfx else if p == "" && u != "" then (if u == "http://www.w3.org/XML/1998/namespace" then "xml" else "ns1") else p
  if l == "" || !XML.isName l then error "XD0015" "invalid QName"
  else if p != "" && u == "" then error "XD0015" "unbound QName prefix"
  else pure ((if p == "" then l else p ++ ":" ++ l),
    if u == "" then [] else [⟨if p == "" then "xmlns" else "xmlns:" ++ p, u⟩])

def qualifyOption (step : Node) (name : String) (env : XPath4.Env) (pfx uri : String := "") : Result (String × List XML.Attribute) := do
  match (named step "with-option").find? (fun n => attr n "name" == name) with
  | some n =>
    let v ← eval (attr n "select") env
    match v with
    | [.atom a] => match a.v with
      | .qn q => qualify step q.eqn (if pfx == "" then q.pfx else pfx) (if uri == "" then q.uri else uri)
      | _ => qualify step (seqString env v) pfx uri
    | _ => qualify step (seqString env v) pfx uri
  | none => qualify step (← option step name env) pfx uri

def namespaceOf (decls : List XML.Attribute) : String := (decls.head?.map (·.value)).getD ""

def runSheet (sheet : Node) (source : Document) (params : List (XPath4.QN × XPath4.Seq) := []) : Result (List Document) := do
  let uri := "urn:factoidal:xproc:stylesheet"
  let compiled ← fromXPath (XSLT4.compileStylesheet uri [(uri, sheet.serialize)])
  let env := xpathEnv (some source)
  let r ← fromXPath (evalXslt compiled { env, globalCtx := some (.node ⟨0,0,none⟩), params })
  if !r.secondary.isEmpty then unsupported "secondary XSLT results" else
  let docs ← seqDocuments env r.raw source.baseUri
  let nodes := (docs.flatMap documentNodes).filter (fun n => match n with | .text "" | .cdata "" => false | _ => true)
  let node := match nodes with | [n] => n | _ => .element "#document" [] nodes
  let isText := !nodes.isEmpty && nodes.all (fun n => match n with | .text _ | .cdata _ => true | _ => false)
  let properties := if isText then source.properties.filter (fun (k,_) => propertyName k != some ⟨"", "serialization", ""⟩) else source.properties
  pure [{ source with node, properties, value := none, contentType := if isText then "text/plain" else "application/xml" }]

def xsl (name : String) (as : List XML.Attribute := []) (cs : List Node := []) : Node := .element ("xsl:" ++ name) as cs

def editSheet (step : Node) (matchPattern : String) (body : List Node) : Node :=
  xsl "stylesheet" ([⟨"xmlns:xsl", "http://www.w3.org/1999/XSL/Transform"⟩, ⟨"version", "3.0"⟩] ++
    step.elementAttrs.filter (fun a => (a.name == "xmlns" || a.name.startsWith "xmlns:") && a.name != "xmlns:xsl"))
    [xsl "param" [⟨"name", "replacement"⟩], xsl "template" [⟨"match", "@*|node()"⟩]
      [xsl "copy" [] [xsl "apply-templates" [⟨"select", "@*|node()"⟩]]],
     xsl "template" [⟨"match", matchPattern⟩, ⟨"priority", "10"⟩] body]

def textLines (s : String) : List String :=
  if s == "" then [] else
    let s := (s.replace "\r\n" "\n").replace "\r" "\n"
    let ls := s.splitOn "\n"
    if s.endsWith "\n" then ls.dropLast else ls

def textDocument (s : String) (d : Document) : Document := { d with value := none, node := .text s, contentType := "text/plain" }

def typedOption (step : Node) (name : String) (env : XPath4.Env) (fallback : String := "()") : Result XPath4.Seq :=
  match (named step "with-option").find? (fun n => attr n "name" == name) with
  | some n => eval (attr n "select" fallback) env
  | none => eval (attr step name fallback) env

def parseQName (step : Node) (s : String) : Result XPath4.QN := do
  let (name, decls) ← qualify step s "" ""
  let (p,l) := XPath4.splitName name
  pure ⟨namespaceOf decls, l, p⟩

def freezeNodes (env : XPath4.Env) (values : XPath4.Seq) : XPath4.Seq :=
  values.map fun v => match v with
  | .node n => .node { n with rt := some (env.doc n) }
  | _ => v

def mapParameters (step : Node) (env : XPath4.Env) : Result (List (XPath4.QN × XPath4.Seq)) := do
  let value ← typedOption step "parameters" env "map{}"
  match value with
  | [.map entries] => entries.mapM fun (key, value) => do
    let q ← match key.v with | .qn q => pure q | _ => parseQName step key.str
    pure (q, freezeNodes env value)
  | _ => error "XD0036" "parameters must be a map"

def xsltFailure (e : XPath4.Err) : ProcError :=
  ⟨if e.code == "XTMM9000" then "XC0096"
   else if e.code == "XTDE0040" then "XC0056"
   else if e.code == "XTDE0045" then "XC0008"
   else "XC0095", e.msg, false, [], none⟩

/-- XQuery and raw XSLT atomic results are JSON documents; text nodes are
text documents. The two cases have different XProc content types. -/
def queryDocuments (env : XPath4.Env) (values : XPath4.Seq) (uri : String) : Result (List Document) :=
  values.mapM fun item => match item with
    | .atom _ => do
      let text ← fromXPath (env.serializeWith { method := "json" } [item])
      pure ⟨.text text, "application/json", uri, [], none⟩
    | .node n => do
      let node ← nodeFromRef env 4096 n
      let ds := documentNodes ⟨node, "", uri, [], none⟩
      let text := !ds.isEmpty && ds.all (fun n => match n with | .text _ | .cdata _ => true | _ => false)
      pure ⟨node, if text then "text/plain" else "application/xml", uri, [], none⟩
    | _ => do
      let docs ← seqDocuments env [item] uri
      oneSource docs

/-- XProc supplies the source sequence as the default collection. Named
collections stay with the enclosing host; absent defaults raise FODC0002. -/
def collectionEnv (env : XPath4.Env) (source : List Document) (enabled : Bool) : XPath4.Env :=
  let values := source.zipIdx |>.flatMap fun (d,i) =>
    if d.contentType == "application/json" then ((xpathEnv (some d)).ctx).getD []
    else [XPath4.Item.node ⟨i,0,none⟩]
  { env with
    docUris := (source.zipIdx.filterMap fun (d,i) => if d.baseUri == "" then none else some (d.baseUri,i)) ++ env.docUris
    host := fun q arity =>
      if q.uri == XPath4.nsFN && (q.loc == "collection" || q.loc == "uri-collection") && arity ≤ 1 then
        some (fun _ args =>
          if args.isEmpty || (args.head!.isEmpty) || seqString env args.head! == "" then
            if !enabled then XPath4.err "FODC0002" "default collection is not defined"
            else if q.loc == "collection" then pure values
            else pure (source.map (fun d => .atom (XPath4.Atomic.ofStr d.baseUri)))
          else match env.host q arity with
            | some f => f {} args
            | none => XPath4.err "FODC0002" "named collection is not defined")
      else env.host q arity }

def xsltStep (step : Node) (ports : List (String × List Document)) (env : XPath4.Env) : Result (List Document) := do
  let source := (ports.lookup "source").getD []
  let sheet ← oneSource ((ports.lookup "stylesheet").getD [])
  let version ← option step "version" env (attr sheet.node "version" "3.0")
  if !["1.0", "2.0", "3.0", "4.0"].contains version then error "XC0038" "unsupported XSLT version" else
  if version == "1.0" && (source.length != 1 || source.any (fun d => d.contentType != "application/xml" && d.contentType != "text/xml")) then error "XC0039" "XSLT 1.0 requires one XML source document" else
  if version == "2.0" && source.any (fun d => d.contentType == "application/json") then error "XC0094" "XSLT 2.0 source must be a document" else
  let params ← mapParameters step env
  if version != "3.0" && version != "4.0" && params.any (fun (_,v) => v.any (fun i => match i with | .map _ | .arr _ => true | _ => false)) then
    error (if version == "1.0" then "XC0105" else "XC0007") "XSLT version does not accept maps or arrays" else
  let uri := if sheet.baseUri == "" then "urn:factoidal:xproc:stylesheet" else sheet.baseUri
  let compiled ← (XSLT4.compileStylesheet uri [(uri, sheet.node.serialize)]).mapError (fun e => ⟨"XC0093", e.msg, false, [], none⟩)
  let docs := source.map (fun d => XPath4.Doc.ofNodes (documentNodes d) d.baseUri) |>.toArray
  let selection := source.zipIdx |>.flatMap fun (d,i) =>
    if d.contentType == "application/json" then ((xpathEnv (some d)).ctx).getD [] else [.node ⟨i,0,none⟩]
  let populate ← option step "populate-default-collection" env "true"
  let e := collectionEnv { env with docs := docs } source (populate != "false")
  let hasGlobal := attr step "global-context-item" != "" || (named step "with-option").any (fun n => attr n "name" == "global-context-item")
  let global ← if hasGlobal then typedOption step "global-context-item" env else pure (selection.take 1)
  if global.length > 1 then error "XD0036" "global context item must be singleton" else
  let tmpl ← qnameOption step "template-name" env
  let mode ← qnameOption step "initial-mode" env
  let initialTemplate ← if tmpl == "" then pure none else some <$> parseQName step tmpl
  let initialMode ← if mode == "" then pure none else (fun q => some q.eqn) <$> parseQName step mode
  let opts : XSLT4.TOpts :=
    { env := e
      params := params
      globalCtx := (freezeNodes (if hasGlobal then env else e) global).head?
      initialSelect := if tmpl == "" then some selection else none
      initialTemplate := initialTemplate
      initialMode := initialMode
      outUri := ← option step "output-base-uri" env env.baseUri }
  let r ← (evalXslt compiled opts).mapError xsltFailure
  if !r.secondary.isEmpty then unsupported "secondary XSLT result ports" else
  let props := r.principalFormat.2 ++ ((compiled.outputs.lookup r.principalFormat.1).getD [])
  let method := (props.lookup "method").getD (XSLT4.defaultMethod e r.raw)
  let buildTree := (props.lookup "build-tree").getD (if ["json", "adaptive"].contains method then "no" else "yes")
  if buildTree == "no" then queryDocuments e r.raw opts.outUri else
  let tree ← fromXPath (XSLT4.materialize e 9000000 (.doc (XSLT4.Out.ofSeq r.raw) opts.outUri))
  let docs ← queryDocuments e [tree] opts.outUri
  let ct := (props.lookup "media-type").getD (if method == "html" then "text/html" else if method == "xhtml" then "application/xhtml+xml" else if method == "text" then "text/plain" else "")
  pure (docs.map (fun d => if ct == "" then d else {d with contentType := ct}))

def deleteNamespaces (uris : List String) : Nat → List (String × String) → Node → Result Node
  | 0, _, _ => unsupported "namespace-delete depth limit"
  | f+1, scope, .element name ats cs => do
    let scope := ns (.element name ats cs) ++ scope
    let stripName := fun (name : String) (isAttr : Bool) =>
      let (p,l) := XPath4.splitName name
      if (p != "" || !isAttr) && uris.contains ((scope.lookup p).getD "") then l else name
    let ats := ats.filterMap fun a =>
      if a.name == "xmlns" || a.name.startsWith "xmlns:" then
        if uris.contains a.value then none else some a
      else some { a with name := stripName a.name true }
    let names := ats.map (·.name)
    if names.eraseDups.length != names.length then error "XC0109" "namespace removal creates duplicate attributes"
    else pure (.element (stripName name false) ats (← cs.mapM (deleteNamespaces uris f scope)))
  | _, _, n => pure n

def flattenJson (depth : Nat) (items : List XPath4.Seq) : List XPath4.Seq :=
  match depth with
  | 0 => items
  | n+1 => items.flatMap fun value => match value with
    | [.arr ms] => flattenJson n ms
    | _ => [value]

def groupingEqual (env : XPath4.Env) (a b : XPath4.Seq) : Result Bool :=
  evalBool "deep-equal(data($left),data($right))"
    {env with vars := [(⟨"", "left", ""⟩, a), (⟨"", "right", ""⟩, b)] ++ env.vars}

def wrapperAttributes (step : Node) (env : XPath4.Env) : Result (List XML.Attribute) := do
  let [.map entries] ← typedOption step "attributes" env "map{}" | error "XD0036" "wrapper attributes must be a map"
  let attributes ← entries.mapM fun (key,value) => do
    let q ← propertyQName env key
    let pfx := if q.uri == "http://www.w3.org/XML/1998/namespace" then "xml" else q.pfx
    if q.loc == "xmlns" || q.uri == "http://www.w3.org/2000/xmlns/" then error "XC0014" "namespace declarations are not wrapper attributes" else
    let pfx := if q.uri != "" && pfx == "" then "attr" ++ toString q.loc.length else pfx
    let name := if pfx == "" then q.loc else pfx ++ ":" ++ q.loc
    pure ((if q.uri == "" || pfx == "xml" then [] else [XML.Attribute.mk ("xmlns:" ++ pfx) q.uri]) ++ [XML.Attribute.mk name (seqString env value)])
  pure attributes.flatten

/-- Group only consecutive matched siblings. Comments, processing instructions and whitespace separators are included
only between members of the same group. Other unmatched siblings break it. -/
def wrapSiblingGroups (env : XPath4.Env) (name : String) (attributes : List XML.Attribute)
    (items : List (Bool × XPath4.Seq × List Node)) : Result (List Node) := do
  let mut output := []
  let mut pending : List Node := []
  let mut gap : List Node := []
  let mut previous : Option XPath4.Seq := none
  for (matched,key,nodes) in items do
    if matched then
      let same ← match previous with | some old => groupingEqual env old key | none => pure false
      if !same && previous.isSome then
        output := output ++ [.element name attributes pending] ++ gap
        pending := []
      else pending := pending ++ gap
      gap := []
      pending := pending ++ nodes
      previous := some key
    else if previous.isSome && nodes.all (fun n => match n with
        | .text t => t.trimAscii.toString == "" | .comment _ | .pi _ _ => true | _ => false) then
      gap := gap ++ nodes
    else
      if previous.isSome then output := output ++ [.element name attributes pending] ++ gap
      output := output ++ nodes
      pending := []
      gap := []
      previous := none
  if previous.isSome then output := output ++ [.element name attributes pending] ++ gap
  pure output

def wrapDescendants (env : XPath4.Env) (selectedIndices : List Nat) (name : String)
    (attributes : List XML.Attribute) (group : String) : Nat → XPath4.NodeRef → Result Node
  | 0, _ => unsupported "wrap tree depth limit"
  | fuel+1, ref => do
    let original ← nodeFromRef env 4096 ref
    let children := (env.nrec ref).children.toList
    let items ← children.zipIdx.mapM fun (idx,position) => do
      let child := ref.at idx
      let transformed ← wrapDescendants env selectedIndices name attributes group fuel child
      let selected := selectedIndices.contains idx
      let key ← if !selected || group == "" then pure (XPath4.sInt idx) else
        eval ("data((" ++ group ++ "))") {env with ctx := some [.node child], pos := position+1, size := children.length}
      pure (selected, retainItems env 4096 key, [transformed])
    let nodes ← wrapSiblingGroups env name attributes items
    if (env.nrec ref).kind == .document then pure (.element "#document" [] nodes) else
    match original with
    | .element tag attrs _ => pure (.element tag attrs nodes)
    | _ => pure original

def atomicPure (step : Node) (ports : List (String × List Document)) (env : XPath4.Env) : Result (List Document) := do
  let source := (ports.lookup "source").getD []
  let opt := fun n d => option step n env d
  match tag step with
  | "identity" => pure (identity source)
  | "set-properties" =>
    let values ← typedOption step "properties" env "map{}"
    let merge := (← opt "merge" "true") != "false"
    source.mapM (fun d => updateProperties env d values merge "XC0069")
  | "sink" => pure []
  | "count" =>
    let limit ← opt "limit" "0"
    let some lim := limit.toNat? | error "XD0036" "count limit must be nonnegative"
    pure [resultDoc (toString (if lim == 0 then source.length else min lim source.length))]
  | "error" =>
    let code ← opt "code" ""
    let (p,l) := XPath4.splitName code
    let u := ((ns step).lookup p).getD ""
    .error {code := "Q{" ++ u ++ "}" ++ l, message := "p:error", details := source.flatMap documentNodes, errorName := some ⟨u,l,p⟩}
  | "wrap-sequence" =>
    let (name, decls) ← qualifyOption step "wrapper" env (← opt "wrapper-prefix" "") (← opt "wrapper-namespace" "")
    let attributes ← wrapperAttributes step env
    let group ← opt "group-adjacent" ""
    let items ← source.zipIdx.mapM fun (d,index) => do
      let e := xpathEnv (some d) env.vars env.ns (index+1) source.length
      let key ← if group == "" then pure [] else eval ("data((" ++ group ++ "))") e
      pure (true, retainItems e 4096 key, documentNodes d)
    let nodes ← if source.isEmpty then pure [.element name (decls ++ attributes) []] else wrapSiblingGroups env name (decls ++ attributes) items
    let base := (XML.findAttr "xml:base" attributes).getD env.baseUri
    pure (nodes.map (fun node => ({node, baseUri := base} : Document)))
  | "pack" =>
    let (name, decls) ← qualifyOption step "wrapper" env (← opt "wrapper-prefix" "") (← opt "wrapper-namespace" "")
    let alt := (ports.lookup "alternate").getD []
    let attributes ← wrapperAttributes step env
    let base := (XML.findAttr "xml:base" attributes).getD env.baseUri
    pure ((List.range (max source.length alt.length)).map fun i =>
      ⟨.element name (decls ++ attributes) ((source[i]?.toList ++ alt[i]?.toList).flatMap documentNodes), "application/xml", base, [], none⟩)
  | "compare" =>
    let method ← opt "method" "deep-equal"
    if method != "deep-equal" then return ← error "XC0076" "unsupported comparison method"
    let a ← oneSource source
    let b ← oneSource ((ports.lookup "alternate").getD [])
    let ak ← classifyMediaType a.contentType
    let bk ← classifyMediaType b.contentType
    if ak != .xml || bk != .xml then return ← error "XC0077" "deep-equal comparison requires XML documents"
    let e : XPath4.Env := { env with docs := #[XPath4.Doc.ofNodes (documentNodes a), XPath4.Doc.ofNodes (documentNodes b)], vars := [(⟨"", "a", ""⟩, [.node ⟨0,0,none⟩]), (⟨"", "b", ""⟩, [.node ⟨1,0,none⟩])] }
    let same ← evalBool "deep-equal($a,$b)" e
    if !same && (← opt "fail-if-not-equal" "false") == "true" then error "XC0019" "documents differ"
    else pure [resultDoc (if same then "true" else "false")]
  | "filter" =>
    let d ← oneSource source
    let e := { (xpathEnv (some d) env.vars env.ns) with host := env.host }
    seqDocuments e (← eval (← opt "select" "/*") e) d.baseUri
  | "add-xml-base" =>
    let d ← oneSource source
    let all ← opt "all" "false"
    let relative ← opt "relative" "true"
    if all == "true" && relative == "true" then error "XC0058" "all and relative cannot both be true" else
    let pat := if all == "true" then "*" else "/*|*[@xml:base]"
    let value := if relative == "true" then "if (parent::*) then string(@xml:base) else base-uri(.)" else "base-uri(.)"
    runSheet (editSheet step pat [xsl "copy" [] [xsl "copy-of" [⟨"select", "@* except @xml:base"⟩],
      xsl "attribute" [⟨"name", "xml:base"⟩] [xsl "value-of" [⟨"select", value⟩]], xsl "apply-templates" [⟨"select", "node()"⟩]]]) d
  | "namespace-delete" =>
    let d ← oneSource source
    let prefixes := (← opt "prefixes" "").splitOn " " |>.filter (· != "")
    let uris ← prefixes.mapM fun p => match (ns step).lookup p with
      | some u => pure u
      | none => error "XC0108" ("unbound namespace prefix " ++ p)
    pure [{ d with value := none, node := ← deleteNamespaces uris 4096 [] d.node }]
  | "json-join" =>
    let depth ← opt "flatten-to-depth" "0"
    let n ← if depth == "unbounded" then pure 4096 else match depth.toNat? with
      | some n => pure n
      | none => error "XC0119" "invalid flatten-to-depth"
    let values := source.map fun d => freezeNodes (xpathEnv (some d)) (((xpathEnv (some d)).ctx).getD [])
    seqDocuments env [.arr (flattenJson n values)] env.baseUri
  | "json-merge" =>
    let duplicate ← opt "duplicates" "use-first"
    if !["use-first", "use-last", "use-any", "combine", "reject"].contains duplicate then error "XD0019" "invalid duplicates policy" else
    let key ← opt "key" "concat('_', $p:index)"
    let maps ← source.zipIdx |>.mapM fun (d,index) => do
      let e := xpathEnv (some d) ((⟨"http://www.w3.org/ns/xproc", "index", "p"⟩, [.atom (XPath4.Atomic.ofInt (Int.ofNat (index+1)))]) :: env.vars) env.ns
      let value := freezeNodes e (e.ctx.getD [])
      match value with
      | [.map kvs] => pure (XPath4.Item.map kvs)
      | _ =>
        let keys ← eval key e
        match keys with
        | [.atom a] => pure (XPath4.Item.map [(XPath4.Atomic.ofStr a.str, value)])
        | _ => error "XC0110" "merge key must be one atomic value"
    let e := { env with vars := [(⟨"","maps",""⟩, maps), (⟨"","duplicates",""⟩, XPath4.sStr duplicate)] ++ env.vars }
    let merged ← (eval "map:merge($maps,map{'duplicates':$duplicates})" e).mapError (fun er => if duplicate == "reject" then { er with code := "XC0106" } else er)
    seqDocuments e merged env.baseUri
  | "cast-content-type" =>
    let original ← oneSource source
    let ct ← opt "content-type" ""
    let target ← classifyMediaType ct
    let origin ← classifyMediaType original.contentType
    let sameKind := target == origin
    let d := if sameKind then original else {original with properties := original.properties.filter (fun (k,_) => propertyName k != some ⟨"", "serialization", ""⟩)}
    let isData := tag d.node == "data" && ((ns d.node).lookup (XPath4.splitName (d.node.elementTag.getD "")).1).getD "" == "http://www.w3.org/ns/xproc-step"
    let d ← if isData then do
      let declared := attr d.node "content-type"
      if declared == "" then error "XC0073" "c:data requires content-type" else
      if declared != ct then error "XC0074" "c:data content-type differs from requested type" else
      if attr d.node "encoding" "base64" != "base64" then error "XC0052" "unsupported c:data encoding" else
      let charset := (attr d.node "charset" "utf-8").toLower
      if !["utf-8", "utf8", "iso-8859-1", "us-ascii"].contains charset then error "XC0071" "unsupported c:data charset" else
      let some bytes := XSD.parseBase64Lex d.node.textContent | error "XC0072" "invalid base64 data"
      let bytes : ByteArray := ⟨(bytes.map UInt8.ofNat).toArray⟩
      let text ← if charset == "iso-8859-1" then pure (XML.decodeLatin1 bytes) else
        match String.fromUTF8? bytes with | some t => pure t | none => error "XC0071" "invalid encoded text"
      pure {d with value := none, node := .text text, contentType := "text/plain"}
      else pure d
    let origin ← classifyMediaType d.contentType
    if !isData && (sameKind || ((origin == .xml || origin == .html) && (target == .xml || target == .html))) then
      pure [{d with contentType := ct}]
    else if target == .text then
      let text ← if origin == .xml || origin == .html then pure (String.join ((documentNodes d).map (·.serialize))) else
        match d.value with
        | some values => fromXPath (env.serializeWith {method := "json"} values)
        | none => pure d.node.textContent
      pure [{d with value := none, node := .text text, contentType := ct}]
    else if target == .xml && origin == .json then
      let text ← match d.value with
        | some values => fromXPath (env.serializeWith {method := "json"} values)
        | none => pure d.node.textContent
      let e := {env with vars := (⟨"", "json", ""⟩, XPath4.sStr text) :: env.vars}
      let docs ← seqDocuments e (← eval "json-to-xml($json)" e) d.baseUri
      pure (docs.map (fun result => {result with contentType := ct, properties := d.properties}))
    else if target == .json && origin == .xml then
      let e := xpathEnv (some d) env.vars env.ns
      if tag d.node == "param-set" && ((ns d.node).lookup (XPath4.splitName (d.node.elementTag.getD "")).1).getD "" == "http://www.w3.org/ns/xproc-step" then
        let entries ← (kids d.node).mapM fun parameter => do
          let key ← propertyQName {env with ns := ns parameter ++ ns d.node} (XPath4.Atomic.ofStr (attr parameter "name"))
          pure (XPath4.Atomic.ofQN key, XPath4.sStr (attr parameter "value"))
        pure [{d with node := .text "", contentType := ct, value := some [.map entries]}]
      else
        let json ← eval "xml-to-json(.)" e
        pure [{d with value := none, node := .text (seqString e json), contentType := ct}]
    else if target == .json then
      let e := {env with vars := (⟨"", "json", ""⟩, XPath4.sStr d.node.textContent) :: env.vars}
      let _ ← (eval "parse-json($json)" e).mapError (fun err => {err with code := "XD0057"})
      pure [{d with contentType := ct}]
    else if target == .html then
      let e := {env with vars := (⟨"", "html", ""⟩, XPath4.sStr d.node.textContent) :: env.vars}
      let docs ← seqDocuments e (← eval "parse-html($html)" e) d.baseUri
      pure (docs.map (fun result => {result with contentType := ct, properties := d.properties}))
    else if target == .xml then
      match XML.parseXML d.node.textContent with
      | .ok doc => pure [{d with value := none, node := doc.root, contentType := ct}]
      | .error _ => error "XD0049" "cannot parse as XML"
    else unsupported ("cast-content-type " ++ ct)
  | "text-count" =>
    let d ← oneSource source
    pure [resultDoc (toString (textLines d.node.textContent).length)]
  | "text-join" =>
    let sep ← opt "separator" ""
    let pfx ← opt "prefix" ""
    let suffix ← opt "suffix" ""
    let ct ← opt "override-content-type" "text/plain"
    if !(ct.contains "/") then error "XD0079" "invalid media type" else
    if !ct.startsWith "text/" || ["text/xml", "text/html"].contains ct then error "XC0001" "text-join requires a text media type" else
    pure [⟨.text (pfx ++ String.intercalate sep (source.map (·.node.textContent)) ++ suffix), ct, env.baseUri, [], none⟩]
  | "text-head" | "text-tail" =>
    let d ← oneSource source
    let count ← opt "count" "10"
    let some n := count.toInt? | error "XD0036" "invalid line count"
    let ls := textLines d.node.textContent
    let selected := if n == 0 then ls else if tag step == "text-head" then
      (if n < 0 then ls.drop n.natAbs else ls.take n.toNat)
      else (if n < 0 then ls.take (ls.length - n.natAbs) else ls.drop (ls.length - n.toNat))
    pure [textDocument (String.intercalate "\n" selected ++ (if selected.isEmpty then "" else "\n")) d]
  | "text-sort" =>
    let d ← oneSource source
    let order ← opt "order" "ascending"
    let caseOrder ← opt "case-order" "#default"
    if !["ascending", "descending"].contains order || !["#default", "upper-first", "lower-first"].contains caseOrder then error "XD0019" "invalid sort ordering" else
    let lang ← opt "lang" ""
    if (lang.splitOn "-").any (fun part => part.length > 8) then error "XD0036" "invalid language tag" else
    let key ← opt "sort-key" "."
    for (line,i) in (textLines d.node.textContent).zipIdx do
      let e := { env with ctx := some (XPath4.sStr line), pos := i+1, size := (textLines d.node.textContent).length }
      let v ← (eval key e).mapError (fun er => { er with code := "XC0098" })
      if v.length > 1 then error "XC0099" "sort key must be at most one item"
    let sortAttrs ← (["sort-key", "order", "case-order", "lang", "collation", "stable"]).filterMapM fun n => do
      if attr step n == "" then pure none else
      pure (some (⟨if n == "sort-key" then "select" else n, ← opt n ""⟩ : XML.Attribute))
    let sortAttrs := if attr step "sort-key" == "" then ⟨"select", "."⟩ :: sortAttrs else sortAttrs
    let sheet := xsl "stylesheet" [⟨"xmlns:xsl", "http://www.w3.org/1999/XSL/Transform"⟩, ⟨"version", "3.0"⟩]
      [xsl "param" [⟨"name", "lines"⟩], xsl "template" [⟨"match", "/"⟩]
        [xsl "for-each" [⟨"select", "$lines"⟩]
          [xsl "sort" sortAttrs, xsl "value-of" [⟨"select", "."⟩], xsl "text" [] [.text "\n"]]]]
    let result ← (runSheet sheet d [(⟨"", "lines", ""⟩, (textLines d.node.textContent).map (fun s => .atom (XPath4.Atomic.ofStr s)))]).mapError (fun er => if er.unsupported then er else { er with code := "XC0098" })
    pure [textDocument (String.join (result.map (·.node.textContent))) d]
  | "text-replace" =>
    let d ← oneSource source
    let p ← opt "pattern" ""
    let r ← opt "replacement" ""
    let flags ← opt "flags" ""
    let e := { env with vars := [(⟨"","s",""⟩, XPath4.sStr d.node.textContent),
      (⟨"","p",""⟩, XPath4.sStr p), (⟨"","r",""⟩, XPath4.sStr r), (⟨"","f",""⟩, XPath4.sStr flags)] ++ env.vars }
    let emptyMatch ← (evalBool "matches('', $p, $f)" e).mapError (fun er => if er.unsupported then er else { er with code := "XD0030" })
    if emptyMatch then error "XD0030" "replacement pattern matches an empty string" else
    let value ← (eval "replace($s,$p,$r,$f)" e).mapError (fun er => if er.unsupported then er else { er with code := "XD0030" })
    pure [textDocument (seqString e value) d]
  | "text-line-count" => unsupported "nonstandard text-line-count"
  | "validate-with-xml-schema" =>
    let d ← oneSource source
    let schemas := (ports.lookup "schema").getD []
    if schemas.isEmpty then unsupported "schema discovery from instance" else
    let loaded : List XSD11.LoadedDoc := schemas.zipIdx |>.map fun (s,i) =>
      { loc := if s.baseUri == "" then "schema" ++ toString i ++ ".xsd" else s.baseUri, doc := { root := s.node, decl := none, doctype := none, prolog := [], epilog := [] } }
    let schema := XSD11.readSchemaDocs loaded (loaded.map (·.loc))
    if !schema.unsupported.isEmpty then unsupported "unsupported XML Schema component" else
    match XSD11.validateFor schema (← opt "mode" "strict") d.node d.baseUri with
    | .ok _ => pure [d]
    | .error e => if (← opt "assert-valid" "true") == "false" then pure [d] else error "XC0053" e.msg
  | "xslt" => xsltStep step ports env
  | "xquery" =>
    let q ← oneSource ((ports.lookup "query").getD [])
    let version ← opt "version" "3.1"
    if !["1.0", "3.0", "3.1", "4.0"].contains version then error "XC0009" "unsupported XQuery version" else
    if version != "3.1" && version != "4.0" && source.any (fun d => d.contentType == "application/json") then error "XC0101" "XQuery version does not accept JSON source" else
    let params ← mapParameters step env
    if version != "3.1" && version != "4.0" && params.any (fun (_,v) => v.any (fun i => match i with | .map _ | .arr _ => true | _ => false)) then
      error "XC0102" "XQuery version does not accept map or array parameters" else
    let populate ← opt "populate-default-collection" "true"
    let base := xpathEnv source.head? (params ++ env.vars) env.ns
    let e := collectionEnv { base with docs := (source.map (fun d => XPath4.Doc.ofNodes (documentNodes d) d.baseUri)).toArray } source (populate != "false")
    let kind ← classifyMediaType q.contentType
    let queryWrapper := tag q.node == "query" && ((ns q.node).lookup (XPath4.splitName (q.node.elementTag.getD "")).1).getD "" == "http://www.w3.org/ns/xproc-step"
    let query := if (kind == .xml || kind == .html) && !queryWrapper then String.join ((documentNodes q).map XML.Node.serialize) else q.node.textContent
    let values ← (evalXquery query e).mapError (fun er => ⟨if er.code.startsWith "XPST" || er.code.startsWith "XQST" then "XC0103" else "XC0104", er.msg, false, [], none⟩)
    queryDocuments e values env.baseUri
  | "delete" | "unwrap" | "rename" | "wrap" | "add-attribute" | "set-attributes" | "replace" | "insert" | "string-replace" | "make-absolute-uris" | "label-elements" =>
    let d ← oneSource source
    if tag step == "set-attributes" then
      let kind ← classifyMediaType d.contentType
      if kind != .xml && kind != .html then return ← error "XD0038" "set-attributes requires XML or HTML"
    let pat ← opt "match" (if tag step == "label-elements" then "*" else if tag step == "add-attribute" || tag step == "set-attributes" then "/*" else "")
    if pat == "" then error "XS0018" "required match option missing" else
    let context := xpathEnv (some d) env.vars env.ns
    let pattern ← fromXPath (({ ns := ns step } : XSLT4.SCx).pattern pat)
    let matching := (List.range (XPath4.Doc.ofNodes (documentNodes d)).nodes.size).filter fun i =>
      pattern.matches context (.node ⟨0,i,none⟩)
    if ["add-attribute", "set-attributes", "label-elements"].contains (tag step) &&
      matching.any (fun i => (context.nrec ⟨0,i,none⟩).kind != .element) then
      error "XC0023" "match selects a non-element node" else
    if tag step == "replace" && matching.any (fun i => (context.nrec ⟨0,i,none⟩).kind == .attribute) then
      error "XC0023" "cannot replace an attribute with a document" else
    if tag step == "unwrap" && matching.any (fun i => ![XPath4.NKind.document, .element].contains (context.nrec ⟨0,i,none⟩).kind) then
      error "XC0023" "unwrap requires element or document nodes" else
    if tag step == "delete" && matching.any (fun i => (context.nrec ⟨0,i,none⟩).kind == .document) then
      error "XC0023" "cannot delete the document node" else
    if tag step == "rename" && matching.any (fun i => ![XPath4.NKind.element, .attribute, .pi].contains (context.nrec ⟨0,i,none⟩).kind) then
      error "XC0023" "cannot rename this node kind" else
    if tag step == "rename" && matching.any (fun i => (context.nrec ⟨0,i,none⟩).kind == .attribute &&
      matching.any (fun j => i != j && (context.nrec ⟨0,j,none⟩).kind == .attribute && (context.nrec ⟨0,i,none⟩).parent == (context.nrec ⟨0,j,none⟩).parent)) then
      error "XC0023" "renaming two attributes would create duplicate names" else
    if tag step == "insert" && matching.any (fun i => (context.nrec ⟨0,i,none⟩).kind == .attribute) then
      error "XC0023" "cannot insert beside an attribute" else
    if tag step == "insert" && ["before", "after"].contains (← opt "position" "last-child") &&
      matching.any (fun i => (context.nrec ⟨0,i,none⟩).kind == .document) then
      error "XC0024" "cannot insert beside the document node" else
    if tag step == "insert" && ["first-child", "last-child"].contains (← opt "position" "last-child") &&
      matching.any (fun i => ![XPath4.NKind.document, .element].contains (context.nrec ⟨0,i,none⟩).kind) then
      error "XC0025" "insertion target cannot have children" else
    if tag step == "wrap" then
      let (name,decls) ← qualifyOption step "wrapper" env (← opt "wrapper-prefix" "") (← opt "wrapper-namespace" "")
      let attributes ← wrapperAttributes step env
      let group ← opt "group-adjacent" ""
      let transformed ← wrapDescendants context matching name (decls ++ attributes) group 4096 ⟨0,0,none⟩
      let node := if matching.contains 0 then .element name (decls ++ attributes) (documentNodes {node := transformed}) else transformed
      return [{d with node, value := none}]
    let body ← match tag step with
      | "make-absolute-uris" =>
        if matching.any (fun i => ![XPath4.NKind.element, .attribute].contains (context.nrec ⟨0,i,none⟩).kind) then error "XC0023" "URI match must select elements or attributes" else
        let base ← opt "base-uri" ""
        let expression := if base == "" then "resolve-uri(string(.),base-uri(.))" else
          "resolve-uri(string(.),'" ++ base.replace "'" "''" ++ "')"
        pure [xsl "choose" [] [
          xsl "when" [⟨"test", "self::*"⟩] [xsl "copy" [] [xsl "copy-of" [⟨"select", "@*"⟩], xsl "value-of" [⟨"select", expression⟩]]],
          xsl "otherwise" [] [xsl "attribute" [⟨"name", "{name()}"⟩, ⟨"namespace", "{namespace-uri()}"⟩] [xsl "value-of" [⟨"select", expression⟩]]]]]
      | "label-elements" =>
        let raw ← opt "attribute" "xml:id"
        let (name,decls) ← qualify step raw "" ""
        let label ← opt "label" "concat('_', $p:index)"
        let replace ← opt "replace" "true"
        let test := if replace == "true" then "true()" else
          "not(@*[local-name()='" ++ (XPath4.splitName name).2 ++ "' and namespace-uri()='" ++ namespaceOf decls ++ "'])"
        pure [xsl "variable" [⟨"name", "p:index"⟩] [xsl "number" [⟨"level", "any"⟩, ⟨"count", pat⟩]],
          xsl "copy" [] [xsl "copy-of" [⟨"select", "@*"⟩],
            xsl "if" [⟨"test", test⟩] [xsl "attribute" [⟨"name", name⟩, ⟨"namespace", namespaceOf decls⟩]
              [xsl "value-of" [⟨"select", label⟩]]], xsl "apply-templates" [⟨"select", "node()"⟩]]]
      | "delete" => pure []
      | "unwrap" => pure [xsl "apply-templates" [⟨"select", "node()"⟩]]
      | "replace" => pure [xsl "copy-of" [⟨"select", "$replacement/node()"⟩]]
      | "insert" =>
        let pos ← opt "position" "last-child"
        let ins := xsl "copy-of" [⟨"select", "$replacement/node()"⟩]
        let cp := xsl "copy-of" [⟨"select", "."⟩]
        if pos == "before" then pure [ins, cp]
        else if pos == "after" then pure [cp, ins]
        else if pos == "first-child" then pure [xsl "copy" [] [xsl "copy-of" [⟨"select", "@*"⟩], ins, xsl "apply-templates" [⟨"select", "node()"⟩]]]
        else if pos == "last-child" then pure [xsl "copy" [] [xsl "apply-templates" [⟨"select", "@*|node()"⟩], ins]]
        else error "XD0019" "invalid insert position"
      | "set-attributes" =>
        let attributes ← (wrapperAttributes step env).mapError (fun e => if e.code == "XC0014" then {e with code := "XC0059"} else e)
        let additions := (attributes.filter (fun a => !a.name.startsWith "xmlns:")).map fun a =>
          let pfx := (XPath4.splitName a.name).1
          let uri := if pfx == "xml" then "http://www.w3.org/XML/1998/namespace" else (XML.findAttr ("xmlns:" ++ pfx) attributes).getD ""
          xsl "attribute" [⟨"name", a.name⟩, ⟨"namespace", uri⟩] [.text a.value]
        pure [xsl "copy" [] ([xsl "copy-of" [⟨"select", "@*"⟩]] ++ additions ++ [xsl "apply-templates" [⟨"select", "node()"⟩]])]
      | "string-replace" =>
        let expr ← opt "replace" "''"
        pure [xsl "choose" [] [xsl "when" [⟨"test", "self::attribute()"⟩]
          [xsl "attribute" [⟨"name", "{name()}"⟩, ⟨"namespace", "{namespace-uri()}"⟩] [xsl "value-of" [⟨"select", expr⟩]]],
          xsl "otherwise" [] [xsl "value-of" [⟨"select", expr⟩]]]]
      | "wrap" =>
        let (name,decls) ← qualifyOption step "wrapper" env (← opt "wrapper-prefix" "") (← opt "wrapper-namespace" "")
        pure [.element name decls [xsl "copy" [] [xsl "apply-templates" [⟨"select", "@*|node()"⟩]]]]
      | "rename" =>
        let (name,decls) ← qualifyOption step "new-name" env (← opt "new-prefix" "") (← opt "new-namespace" "")
        if namespaceOf decls == "http://www.w3.org/2000/xmlns/" || name == "xmlns" then error "XC0013" "invalid rename QName" else
        if namespaceOf decls != "" && matching.any (fun i => (context.nrec ⟨0,i,none⟩).kind == .pi) then error "XC0013" "processing instruction name cannot be namespaced" else
        pure [xsl "choose" [] [xsl "when" [⟨"test", "self::*"⟩]
          [xsl "element" [⟨"name", name⟩, ⟨"namespace", namespaceOf decls⟩] [xsl "apply-templates" [⟨"select", "@*|node()"⟩]]],
          xsl "when" [⟨"test", "self::processing-instruction()"⟩]
            [xsl "processing-instruction" [⟨"name", name⟩] [xsl "value-of" [⟨"select", "."⟩]]],
          xsl "otherwise" [] [xsl "attribute" [⟨"name", name⟩, ⟨"namespace", namespaceOf decls⟩] [xsl "value-of" [⟨"select", "."⟩]]]]]
      | "add-attribute" =>
        let (name,decls) ← qualifyOption step "attribute-name" env (← opt "attribute-prefix" "") (← opt "attribute-namespace" "")
        if name == "xmlns" || namespaceOf decls == "http://www.w3.org/2000/xmlns/" then error "XC0059" "cannot add namespace declaration as attribute" else
        pure [xsl "copy" [] [xsl "apply-templates" [⟨"select", "@*"⟩],
          xsl "attribute" [⟨"name", name⟩, ⟨"namespace", namespaceOf decls⟩] [.text (← opt "attribute-value" "")],
          xsl "apply-templates" [⟨"select", "node()"⟩]]]
      | _ => unsupported ("XML edit " ++ tag step)
    let sheet := editSheet step pat body
    let replacement := (ports.lookup (if tag step == "insert" then "insertion" else if tag step == "set-attributes" then "attributes" else "replacement")).getD []
    let values := replacement.zipIdx |>.map fun (r,i) =>
      XPath4.Item.node { doc := 1000000+i, idx := 0, rt := some (XPath4.Doc.ofNodes (documentNodes r) r.baseUri) }
    runSheet sheet d [(⟨"", "replacement", ""⟩, values)]
  | _ => unsupported ("atomic step p:" ++ tag step)

/-- Dispatch capability, checked before the runtime reads bindings. -/
def supportedAtomic (name : String) : Bool :=
  ["identity", "set-properties", "sink", "count", "error", "wrap-sequence", "pack", "compare", "filter",
   "cast-content-type", "text-count", "text-join", "text-head", "text-tail", "text-sort", "text-replace",
   "validate-with-xml-schema", "xslt", "xquery", "delete", "unwrap", "rename", "wrap", "add-attribute",
   "set-attributes", "replace", "insert", "string-replace", "namespace-delete", "add-xml-base", "make-absolute-uris", "label-elements", "json-join", "json-merge"].contains name

def atomic (step : Node) (ports : List (String × List Document)) (env : XPath4.Env) : IO (Result (List Document)) :=
  pure (atomicPure step ports env)

end L4Factoidal.XProc31

namespace L4Factoidal.XProc31
private def probeSource : Document := ⟨.element "root" [] [.element "a" [] [.text "x"], .element "b" [] []], "application/xml", "", [], none⟩
private def probeEdit (kind : String) (attrs : List XML.Attribute) : Result (List Document) :=
  atomicPure (.element ("p:" ++ kind) (⟨"xmlns:p", "http://www.w3.org/ns/xproc"⟩ :: attrs) [])
    [("source", [probeSource])] (xpathEnv (some probeSource))
#guard (atomicPure (.element "p:count" [] []) [("source", [probeSource,probeSource])] {}).toOption.map (fun ds => ds.map (·.node.textContent)) == some ["2"]
#guard (probeEdit "delete" [⟨"match", "a"⟩]).toOption.map (fun ds => ds.map (·.node.textContent)) == some [""]
#guard (probeEdit "rename" [⟨"match", "a"⟩, ⟨"new-name", "c"⟩]).toOption.map (fun ds => ds.map (fun d => (kids d.node).map tag)) == some [["c", "b"]]
#guard (probeEdit "add-attribute" [⟨"match", "a"⟩, ⟨"attribute-name", "test"⟩, ⟨"attribute-value", "yes"⟩]).toOption.map (fun ds => ds.map (fun d => (kids d.node).map (fun n => attr n "test"))) == some [["yes", ""]]
end L4Factoidal.XProc31

namespace L4Factoidal.XProc31
private def collectionSheet : Document :=
  ⟨xsl "stylesheet" [⟨"xmlns:xsl", "http://www.w3.org/1999/XSL/Transform"⟩, ⟨"version", "3.0"⟩]
    [xsl "template" [⟨"name", "go"⟩]
      [.element "out" [] [xsl "value-of" [⟨"select", "count(collection())"⟩]]]], "application/xml", "", [], none⟩
private def collectionProbe : Result (List Document) :=
  atomicPure (.element "p:xslt" [⟨"template-name", "go"⟩] [])
    [("source", [probeSource, probeSource]), ("stylesheet", [collectionSheet])] {}
#guard collectionProbe.toOption.map (fun ds => ds.map (·.node.textContent)) == some ["2"]
#guard (atomicPure (.element "p:text-replace" [⟨"pattern", ""⟩, ⟨"replacement", "x"⟩] [])
  [("source", [⟨.text "abc", "text/plain", "", [], none⟩])] {}).toBool == false
end L4Factoidal.XProc31

namespace L4Factoidal.XProc31
private def castProbe (ct : String) (d : Document) : Result (List Document) :=
  atomicPure (.element "p:cast-content-type" [⟨"content-type", ct⟩] []) [("source", [d])] {}
#guard (castProbe "text/xml" {node := .element "doc" [] []}).toOption.map
  (fun ds => ds.map (fun d => (tag d.node,d.contentType))) == some [("doc","text/xml")]
#guard (castProbe "text/plain" {node := .element "c:data" [⟨"xmlns:c", "http://www.w3.org/ns/xproc-step"⟩, ⟨"content-type", "text/plain"⟩, ⟨"charset", "ISO-8859-1"⟩] [.text "Q29weSCp"]}).toOption.map (fun ds => ds.map (·.node.textContent)) == some ["Copy ©"]
#guard (castProbe "text/plain" {node := .element "doc" [] [], properties :=
  [(XPath4.Atomic.ofQN ⟨"", "serialization", ""⟩, [.map []]),
   (XPath4.Atomic.ofQN ⟨"", "custom", ""⟩, XPath4.sInt 7)]}).toOption.map
  (fun ds => ds.map (fun d => (d.properties.length, (documentProperty d ⟨"", "custom", ""⟩).length))) == some [(1,1)]
end L4Factoidal.XProc31

namespace L4Factoidal.XProc31
private def parameterMapProbe : Result Bool := do
  let source : Document := {node := .element "c:param-set" [⟨"xmlns:c", "http://www.w3.org/ns/xproc-step"⟩] [.element "c:param" [⟨"name", "answer"⟩, ⟨"value", "42"⟩] []]}
  let result ← castProbe "application/json" source
  let d ← oneSource result
  evalBool "map:get(.,QName('', 'answer')) = '42'" (xpathEnv (some d))
#guard parameterMapProbe.toOption == some true
end L4Factoidal.XProc31

namespace L4Factoidal.XProc31
#guard (wrapSiblingGroups {} "group" []
  [(true, XPath4.sInt 1, [.text "a"]), (false, [], [.comment "inside"]),
   (true, XPath4.sInt 1, [.text "b"]), (false, [], [.comment "outside"]),
   (true, XPath4.sInt 2, [.text "c"])]).toOption.map (fun nodes => nodes.map XML.Node.serialize) ==
  some ["<group>a<!--inside-->b</group>", "<!--outside-->", "<group>c</group>"]
end L4Factoidal.XProc31

namespace L4Factoidal.XProc31
#guard (atomicPure (.element "p:set-attributes" [⟨"attributes", "map{'att':1}"⟩] [])
  [("source", [{node := .element "doc" [] []}])] {}).toOption.map
  (fun ds => ds.map (fun d => attr d.node "att")) == some ["1"]
#guard (atomicPure (.element "p:unwrap" [⟨"match", "doc"⟩] [])
  [("source", [{node := .element "doc" [] []}])] {}).toOption.map
  (fun ds => ds.map (·.contentType)) == some ["application/xml"]
end L4Factoidal.XProc31

namespace L4Factoidal.XProc31
#guard match atomicPure (.element "p:error" [⟨"code", "err:example"⟩, ⟨"xmlns:err", "urn:error"⟩] [])
    [("source", [{node := .element "doc" [] [.element "value" [] [.text "detail"]]}])] {} with
  | .error e => e.code == "Q{urn:error}example" && e.details.map XML.Node.serialize == ["<doc><value>detail</value></doc>"]
  | .ok _ => false
end L4Factoidal.XProc31

namespace L4Factoidal.XProc31
private def lineProbe (step count : String) : Option (List String) :=
  (atomicPure (.element ("p:" ++ step) [⟨"count", count⟩] [])
    [("source", [{node := .text "one\ntwo\nthree", contentType := "text/plain"}])] {}).toOption.map
      (fun ds => ds.map (·.node.textContent))
#guard lineProbe "text-head" "0" == some ["one\ntwo\nthree\n"]
#guard lineProbe "text-head" "-1" == some ["two\nthree\n"]
#guard lineProbe "text-tail" "-1" == some ["one\ntwo\n"]
#guard match atomicPure (.element "p:error" [⟨"code", "plain"⟩] []) [] {} with
  | .error e => e.code == "Q{}plain" && e.errorName == some ⟨"", "plain", ""⟩
  | _ => false
end L4Factoidal.XProc31

namespace L4Factoidal.XProc31
#guard (atomicPure (.element "p:xquery" [] [])
  [("source", [{node := .element "doc" [] [.element "title" [] [.text "Title"]]}]),
   ("query", [{node := .element "result" [] [.text "{//title}"]}])] {}).toOption.map
  (fun ds => ds.map (fun d => (tag d.node, d.node.textContent))) == some [("result", "Title")]
end L4Factoidal.XProc31
