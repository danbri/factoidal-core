import L4Factoidal.XProc31.Static
import L4Factoidal.XPath4.ExprEq

namespace L4Factoidal.XProc31

def templateVariableReads (scope : List (String × String)) : Nat → List Char → List XPath4.QN
  | 0, _ => []
  | _+1, [] => []
  | f+1, '{'::'{'::cs | f+1, '}'::'}'::cs => templateVariableReads scope f cs
  | f+1, '{'::cs =>
    match scanAvtExpression (f+1) cs 0 none 0 [] with
    | .error _ => []
    | .ok (expr,rest) =>
      ((XPath4.parseXPath expr scope).toOption.map XPath4.Expr.varsRead |>.getD []) ++
      templateVariableReads scope f rest
  | f+1, _::cs => templateVariableReads scope f cs

def jobVariableReads : Nat → List (String × String) → Bool → XML.Node → List XPath4.QN
  | 0, _, _, _ => []
  | f+1, inherited, enabled, node =>
    let enabled := match XML.findAttr "expand-text" node.elementAttrs with
      | some "false" => false | some "true" => true | _ => enabled
    let scope := ns node ++ inherited
    let reads := node.elementAttrs.flatMap fun a =>
      if a.name == "select" || a.name == "test" || a.name == "document-properties" then
        (XPath4.parseXPath a.value scope).toOption.map XPath4.Expr.varsRead |>.getD []
      else if enabled then templateVariableReads scope (a.value.length+1) a.value.toList else []
    let textReads := match node with
      | .text text | .cdata text => if enabled then templateVariableReads scope (text.length+1) text.toList else []
      | _ => []
    if ["declare-step", "documentation", "pipeinfo"].contains (tag node) then []
    else reads ++ textReads ++ (children node).flatMap (jobVariableReads f scope enabled)

def pipelineJobs (pipeline : XML.Node) : List XML.Node :=
  (kids pipeline).filter (fun node => isPipelineStep node || tag node == "variable")

def previousExecutable (jobs : List XML.Node) (index : Nat) : Option Nat :=
  ((jobs.take index).zipIdx.filter (fun (node,_) => isPipelineStep node)).getLast?.map (·.2)

def scheduledConnections (nameOf : XML.Node → String → XPath4.QN) (pipeline : XML.Node) : Connections := Id.run do
  let jobs := pipelineJobs pipeline
  let executable := jobs.zipIdx.filter (fun (node,_) => isPipelineStep node)
  let edges := pipelineConnections pipeline
  return jobs.zipIdx.map fun (node,index) =>
    let dataEdges := if tag node == "variable" then
        let explicit := (referencedSteps node).filterMap fun name =>
          executable.find? (fun (n,_) => attr n "name" == name) |>.map (·.2)
        let context := (XPath4.parseXPath (attr node "select") (ns node)).toOption.any
          (expressionNeedsFocus ((attr node "select").length+1))
        let ownInput := attr node "href" != "" || attr node "pipe" != "" || !(kids node).isEmpty
        explicit ++ (if context && !ownInput then (previousExecutable jobs index).toList else [])
      else
        let ordinal := (executable.takeWhile (fun (_,i) => i < index)).length
        ((edges[ordinal]?).getD []).filterMap fun i => (executable[i]?).map (·.2)
    let reads := jobVariableReads 4096 [] (attr pipeline "expand-text" != "false") node
    let lexicalEdges := reads.filterMap fun q =>
      ((jobs.take index).zipIdx.reverse.find? (fun (n,_) => tag n == "variable" && nameOf n (attr n "name") == q)).map (·.2)
    (dataEdges ++ lexicalEdges).eraseDups

-- A forward effect dependency must run its writer before the reader while
-- both still obtain the filename from the earlier variable's document focus.
#guard (orderConnections (scheduledConnections (fun _ name => ⟨"",name,""⟩)
  (inheritNS 32 [] (.element "p:declare-step" [{name := "xmlns:p", value := "http://www.w3.org/ns/xproc"}] [
    .element "p:identity" [] [.element "p:with-input" [] [.element "filename" [] []]],
    .element "p:variable" [{name := "name", value := "path"}, {name := "select", value := "string(.)"}] [],
    .element "p:load" [{name := "name", value := "reader"}, {name := "href", value := "{$path}"}, {name := "depends", value := "writer"}] [],
    .element "p:store" [{name := "name", value := "writer"}, {name := "href", value := "{$path}"}] [
      .element "p:with-input" [] [.element "doc" [] []]]])))) == some [0,1,3,2]

end L4Factoidal.XProc31
