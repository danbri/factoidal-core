import L4Factoidal.XProc31.Atomic
import L4Factoidal.Schematron.FromXml
import L4Factoidal.Schematron.Validate

namespace L4Factoidal.XProc31
open XML

def supportsSchematron (name : String) : Bool := name == "validate-with-schematron"

def unsupportedSchematron : Nat → Node → Bool
  | 0, _ => true
  | fuel+1, node =>
    ["include", "extends", "diagnostics"].contains (tag node) || attr node "abstract" == "true" || attr node "is-a" != "" ||
      (kids node).any (unsupportedSchematron fuel)

def schematronBindings (env : XPath4.Env) (bindings : List Schematron.Let) : Result XPath4.Env := do
  let mut env := env
  for binding in bindings do
    let name ← propertyQName env (XPath4.Atomic.ofStr binding.name)
    let value ← eval binding.value env
    env := {env with vars := (name,value)::env.vars}
  pure env

def schematronMessage (env : XPath4.Env) : Nat → Node → Result String
  | 0, _ => unsupported "Schematron message depth limit"
  | fuel+1, node =>
    match node with
    | .text text | .cdata text => pure text
    | .element _ _ children =>
      if tag node == "value-of" then do pure (seqString env (← eval (attr node "select") env))
      else if tag node == "name" then do pure (seqString env (← eval ("name(" ++ attr node "path" "." ++ ")") env))
      else do pure (String.join (← children.mapM (schematronMessage env fuel)))
    | _ => pure ""

def findingReport (format : String) (findings : List Schematron.Finding) (events : List Node)
    (uri : String) : Document :=
  let root : Node := if format == "xvrl" then
    .element "xvrl:report" [⟨"xmlns:xvrl", "http://www.xproc.org/ns/xvrl"⟩]
      (findings.map fun finding => .element "xvrl:detection" [⟨"severity", "error"⟩, ⟨"code", finding.kind⟩]
        [.element "xvrl:location" [⟨"xpath",finding.path⟩] [], .element "xvrl:message" [] [.text finding.message]])
    else .element "svrl:schematron-output" [⟨"xmlns:svrl", "http://purl.oclc.org/dsdl/svrl"⟩]
      (events ++ findings.map fun finding =>
        .element (if finding.kind == "assert-fail" then "svrl:failed-assert" else "svrl:successful-report")
          [⟨"test", finding.test⟩, ⟨"location", finding.path⟩]
          [.element "svrl:text" [] [.text finding.message]])
  {node := root, baseUri := uri}

def schematronPorts (step : Node) (ports : List (String × List Document))
    (env : XPath4.Env) : Result (List (String × List Document)) := do
  let source ← oneSource ((ports.lookup "source").getD [])
  let schemaDoc ← oneSource ((ports.lookup "schema").getD [])
  let schemaRoot := schemaDoc.node
  let schema ← match Schematron.parseSchematron schemaRoot.serialize with
    | .ok schema => pure schema
    | .error message => error "XC0151" message
  if unsupportedSchematron 4096 schemaRoot then return ← unsupported "Schematron include, abstract expansion or diagnostics"
  let queryBinding := attr schemaRoot "queryBinding" "xslt"
  if !["xslt", "xslt2", "xslt3", "xpath", "xpath2", "xpath3"].contains queryBinding then
    return ← unsupported ("Schematron query binding " ++ queryBinding)
  let phase ← option step "phase" env "#DEFAULT"
  let phase := if phase == "#DEFAULT" then attr schemaRoot "defaultPhase" "#ALL" else phase
  let active ← if phase == "#ALL" then pure none else
    match (named schemaRoot "phase").find? (fun node => attr node "id" == phase) with
    | some node => pure (some ((named node "active").map (attr · "pattern")))
    | none => error "XC0151" ("unknown Schematron phase " ++ phase)
  let reportFormat ← option step "report-format" env "svrl"
  if !["svrl", "xvrl"].contains reportFormat then return ← error "XC0117" ("unsupported Schematron report format " ++ reportFormat)
  let parameters ← mapParameters step env
  let context := { (xpathEnv (some source) (parameters ++ env.vars) (schema.namespaces ++ ns schemaRoot)) with resources := env.resources, resourceBytes := env.resourceBytes }
  let context ← schematronBindings context schema.lets
  let mut findings : List Schematron.Finding := []
  let mut events : List Node := []
  for (pattern,patternIndex) in schema.patterns.zipIdx do
    if active.any (fun ids => !ids.contains pattern.id) then continue
    events := events ++ [.element "svrl:active-pattern" [⟨"id",pattern.id⟩] []]
    let rawPattern := ((named schemaRoot "pattern")[patternIndex]?).getD (.element "pattern" [] [])
    let context ← schematronBindings context ((named rawPattern "let").filterMap Schematron.letOf)
    let mut claimed : List Nat := []
    for rule in pattern.rules do
      let compiled ← fromXPath (({ns := context.ns} : XSLT4.SCx).pattern rule.context)
      let indices := (List.range (context.docs[0]!).nodes.size).filter fun index =>
        !claimed.contains index && compiled.matches context (.node ⟨0,index,none⟩)
      claimed := claimed ++ indices
      for index in indices do
        let item : XPath4.Seq := [.node ⟨0,index,none⟩]
        let focused : XPath4.Env := {context with
          ctx := some item
          host := fun q arity =>
            if q.uri == "http://www.w3.org/2005/xpath-functions" && q.loc == "current" && arity == 0 then some (fun _ _ => pure item) else context.host q arity}
        let focused ← schematronBindings focused rule.lets
        let location := seqString focused (← eval "path(.)" focused)
        events := events ++ [.element "svrl:fired-rule" [⟨"context",rule.context⟩] []]
        let rawRule := ((named rawPattern "rule").find? (fun node => attr node "context" == rule.context)).getD (.element "rule" [] [])
        let rawAssertions := (kids rawRule).filter (fun node => ["assert","report"].contains (tag node))
        for (assertion,number) in rule.assertions.zipIdx do
          let passed ← evalBool assertion.test focused
          let message ← match rawAssertions[number]? with
            | some node => schematronMessage focused 4096 node
            | none => pure assertion.message
          let assertion := {assertion with message := Schematron.normalizeSpace message}
          if let some finding := Schematron.applyAssertion assertion rule.context location (if passed then .true' else .false') then
            findings := findings ++ [finding]
  let report := findingReport reportFormat findings events env.baseUri
  if (← option step "assert-valid" env "true") != "false" && Schematron.hasViolations findings then
    return ← .error {code := "XC0054", message := String.intercalate "; " (findings.map (·.message)), details := [report.node]}
  pure [("result",[source]), ("report",[report])]

def schematronStep (step : Node) (ports : List (String × List Document))
    (env : XPath4.Env) : IO (Result (List Document)) :=
  pure ((schematronPorts step ports env).map (fun ports => (ports.lookup "result").getD []))

private def reportSchema : Document :=
  {node := .element "schema" [⟨"xmlns", "http://purl.oclc.org/dsdl/schematron"⟩]
    [.element "pattern" [] [.element "rule" [⟨"context", "doc"⟩]
      [.element "assert" [⟨"test", "@ok"⟩] [.text "missing ok"],
       .element "report" [⟨"test", "true()"⟩] [.text "report hit"]]]]}
#guard match schematronPorts (.element "p:validate-with-schematron" [] [])
    [("source",[{node := .element "doc" [⟨"ok","yes"⟩] []}]),("schema",[reportSchema])] {} with
  | .error e => e.code == "XC0054" | _ => false
#guard (schematronPorts (.element "p:validate-with-schematron" [⟨"assert-valid","false"⟩] [])
    [("source",[{node := .element "doc" [] []}]),("schema",[reportSchema])] {}).toOption.map
  (fun ports => ((ports.lookup "report").getD []).any (fun d =>
    (named d.node "failed-assert").length == 1 && (named d.node "successful-report").length == 1)) == some true
end L4Factoidal.XProc31
