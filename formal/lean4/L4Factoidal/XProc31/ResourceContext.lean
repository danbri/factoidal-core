import L4Factoidal.XProc31.Loading
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.XProc31
open XML XPath4

/-- Carry only resource state across lexical XPath contexts. -/
def resourceState (outer inner : XPath4.Env) : XPath4.Env :=
  {outer with resources := inner.resources, resourceBytes := inner.resourceBytes, resourceEncodings := inner.resourceEncodings}

def resourceFunction (q : XPath4.QN) : Bool :=
  q.uri == "http://www.w3.org/2005/xpath-functions" &&
    ["doc", "doc-available", "json-doc", "unparsed-text", "unparsed-text-lines", "unparsed-text-available"].contains q.loc

/-- Read only a URI obtained from a resource function's first argument.
Absence or decoding failure is never replaced by fabricated content. -/
def preloadResourceCall (env : XPath4.Env) (q : XPath4.QN) (argument : XPath4.Expr) : IO XPath4.Env := do
  if !resourceFunction q then return env
  let .ok values := XPath4.eval 100000 env argument | return env
  let uri ← match values with
    | [.atom a] => if a.isStringLike then pure a.str else return env
    | [.node n] => pure (env.nodeString n)
    | _ => return env
  let absolute := Syntax.resolveIri env.baseUri uri
  if !(absolute.startsWith "file:") then return env
  -- Refresh, including invalidating stale content when a preceding step deleted it.
  let cleared := {env with resources := env.resources.filter (fun (u,_) => u != absolute && u != uri), resourceBytes := env.resourceBytes.filter (fun (u,_) => u != absolute && u != uri)}
  let .ok bytes ← loadDocumentBytes absolute | return cleared
  let updated := {cleared with resourceBytes := (absolute,bytes) :: cleared.resourceBytes}
  let text := if ["doc", "doc-available"].contains q.loc then
      (XML.decodeXmlBytes bytes).toOption
    else (decodeDocumentText bytes none).toOption
  match text with
  | some text => return {updated with resources := (absolute,text) :: updated.resources}
  | none => return updated

/-- Walk the complete XPath expression tree. Let/for bindings and selected
conditional branches use their dynamic contexts when those can be evaluated. -/
def preloadExpression : Nat → XPath4.Env → XPath4.Expr → IO XPath4.Env
  | 0, env, _ => pure env
  | fuel+1, env, expression => do
    match expression with
    | .letE bindingName type value body =>
      let env ← preloadExpression fuel env value
      match XPath4.eval 100000 env value >>= (fun values => env.coerce type values ("$" ++ bindingName.show)) with
      | .ok values =>
        let localEnv := {env with vars := (bindingName,values) :: env.vars}
        return resourceState env (← preloadExpression fuel localEnv body)
      | .error _ => return env
    | .forE kind bindingName second position type source body =>
      let env ← preloadExpression fuel env source
      let bindings : XPath4.M (List (XPath4.Seq × Option XPath4.Seq)) := do
        let values ← XPath4.eval 100000 env source
        match kind with
        | .item => pure (values.map (fun value => ([value],none)))
        | .member => values.flatMapM fun item => match item with
          | .arr members => pure (members.map (fun member => (member,none)))
          | _ => XPath4.err "XPTY0004" "array required"
        | .entry => values.flatMapM fun item => match item with
          | .map entries => pure (entries.map (fun (key,value) => ([.atom key],some value)))
          | _ => XPath4.err "XPTY0004" "map required"
      let .ok bindings := bindings | return env
      let mut updated := env
      for ((value,secondValue),index) in bindings.zipIdx do
        let .ok value := env.coerce type value ("$" ++ bindingName.show) | continue
        let variables := (bindingName,value) :: (position.toList.map (fun q => (q, sInt (index+1)))) ++ env.vars
        let variables := match second,secondValue with | some q,some v => (q,v)::variables | _,_ => variables
        updated := resourceState updated (← preloadExpression fuel {updated with vars := variables} body)
      return updated
    | .smap source body | .slash source body | .filter source body =>
      let env ← preloadExpression fuel env source
      let .ok values := XPath4.eval 100000 env source | return env
      let mut updated := env
      for (value,index) in values.zipIdx do
        updated := resourceState updated (← preloadExpression fuel
          {updated with ctx := some [value], pos := index+1, size := values.length} body)
      return updated
    | .quant _ bindingName type source body =>
      let env ← preloadExpression fuel env source
      let .ok values := XPath4.eval 100000 env source | return env
      let mut updated := env
      for value in values do
        let .ok value := env.coerce type [value] ("$" ++ bindingName.show) | continue
        updated := resourceState updated (← preloadExpression fuel {updated with vars := (bindingName,value)::env.vars} body)
      return updated
    | .ifE condition yes no =>
      let env ← preloadExpression fuel env condition
      match XPath4.eval 100000 env condition >>= XPath4.ebv with
      | .ok test => preloadExpression fuel env (if test then yes else no)
      | .error _ => pure env
    | _ =>
      let operands : List XPath4.Expr := match expression with
        | .seq es | .arrS es | .tmpl es | .ext _ es _ _ _ => es
        | .slash a b | .filter a b | .bin _ a b | .smap a b | .pipe a b => [a,b]
        | .step _ _ predicates => predicates
        | .dstep _ test predicates => test :: predicates
        | .call _ args keywords => args.filterMap id ++ keywords.filterMap (·.2)
        | .dyn f args => f :: args.filterMap id
        | .mapArrow source f args => source :: f :: args.filterMap id
        | .inline _ _ body _ => [body]
        | .mapC entries => entries.flatMap (fun (a,b) => [a,b])
        | .arrC e | .neg e | .plus e | .instOf e _ | .treat e _ | .cast e _ _ | .castable e _ _ => [e]
        | .lookup e key => e :: key.toList
        | .ulookup key => key.toList
        | .quant _ _ _ source body => [source,body]
        | _ => []
      let mut env := env
      for operand in operands do env ← preloadExpression fuel env operand
      match expression with
      | .call q args keywords =>
        let argument := ((args.head?.bind id)).orElse (fun _ =>
          (keywords.find? (fun (name,_) => ["uri", "href"].contains name)).bind (·.2))
        match argument with
        | some argument => preloadResourceCall env q argument
        | none => pure env
      | .dyn (.fref q _) args =>
        match (args.head?.bind id) with | some argument => preloadResourceCall env q argument | none => pure env
      | .mapArrow source (.fref q _) _ => preloadResourceCall env q source
      | _ => pure env

def preloadXPathSource (env : XPath4.Env) (source : String) : IO XPath4.Env :=
  match XPath4.parseXPath4 source env.ns env.schema.declared with
  | .ok expression => preloadExpression 4096 env expression
  | .error _ => pure env

/-- AVT/TVT extraction respects escaped braces, quoted strings and comments by
using the same scanner as template evaluation. -/
def templateExpressions : Nat → List Char → List String
  | 0, _ => []
  | _, [] => []
  | fuel+1, '{' :: '{' :: rest | fuel+1, '}' :: '}' :: rest => templateExpressions fuel rest
  | fuel+1, '{' :: rest =>
    match scanAvtExpression (rest.length+1) rest 0 none 0 [] with
    | .ok (expression,tail) => expression :: templateExpressions fuel tail
    | .error _ => []
  | fuel+1, _ :: rest => templateExpressions fuel rest

def preloadResourceNode : Nat → XPath4.Env → Bool → XML.Node → IO XPath4.Env
  | 0, env, _, _ => pure env
  | fuel+1, outer, inheritedExpansion, node => do
    let namespaces := ns node ++ outer.ns.filter (fun (p,_) => !((ns node).any (fun (n,_) => n == p)))
    let base := attr node "xml:base"
    let env := {outer with ns := namespaces, baseUri := if base == "" then outer.baseUri else Syntax.resolveIri outer.baseUri base}
    let expansion := attr node "expand-text" (attr node "p:expand-text" (if inheritedExpansion then "true" else "false")) != "false"
    let mut env := env
    match node with
    | .element _ attributes children =>
      for property in attributes do
        if property.name == "xmlns" || property.name.startsWith "xmlns:" then continue
        if ["select", "test"].contains property.name then
          env ← preloadXPathSource env property.value
        else
          for expression in templateExpressions (property.value.length+1) property.value.toList do
            env ← preloadXPathSource env expression
      for child in children do env ← preloadResourceNode fuel env expansion child
    | .text text | .cdata text =>
      if expansion then
        for expression in templateExpressions (text.length+1) text.toList do
          env ← preloadXPathSource env expression
    | _ => pure ()
    return resourceState outer env

def preloadXPathResources (env : XPath4.Env) (node : XML.Node) : IO XPath4.Env :=
  preloadResourceNode 4096 env true node

#guard templateExpressions 100 "{{doc('literal')}} {doc($path)}".toList == ["doc($path)"]
#guard templateExpressions 100 "{concat('}', unparsed-text('file:///x'))}".toList == ["concat('}', unparsed-text('file:///x'))"]

/-- Actual resource IO regression: dynamic URI, refresh after overwrite,
removal after deletion, and no reads from arbitrary string literals. -/
def resourceContextRegression : IO Bool := IO.FS.withTempDir fun root => do
  let path := root / "resource.xml"
  IO.FS.writeFile path "<doc>first</doc>"
  let env : XPath4.Env := {baseUri := "file://" ++ root.toString ++ "/pipeline.xpl", vars := [(⟨"","path",""⟩, XPath4.sStr "resource.xml")]}
  let expression := "string(doc($path)/doc)"
  let node := XML.Node.element "p:variable" [⟨"select",expression⟩] []
  let loaded ← preloadXPathResources env node
  if (eval expression loaded).toOption.map (seqString loaded) != some "first" then return false
  IO.FS.writeFile path "<doc>second</doc>"
  let refreshed ← preloadXPathResources loaded node
  if (eval expression refreshed).toOption.map (seqString refreshed) != some "second" then return false
  let localEnv ← preloadXPathSource env "let $p := 'resource.xml' return doc($p)"
  if localEnv.resourceBytes.isEmpty then return false
  let literal ← preloadXPathSource env "'resource.xml'"
  if !literal.resourceBytes.isEmpty || !literal.resources.isEmpty then return false
  let inactive ← preloadXPathSource env "if (false()) then doc('resource.xml') else ()"
  if !inactive.resourceBytes.isEmpty then return false
  IO.FS.removeFile path
  let missing ← preloadXPathResources refreshed node
  return missing.resourceBytes.isEmpty && missing.resources.isEmpty && !(eval expression missing).toBool

end L4Factoidal.XProc31
