import L4Factoidal.XProc31.Core
import L4Factoidal.XSLT4.Static
import L4Factoidal.XSLT4.Interp
import L4Factoidal.XPath4.BaseUri

namespace L4Factoidal.XProc31

/-- XML and HTML inputs retain their document properties through viewport. -/
def viewportXmlType (contentType : String) : Bool :=
  let media := (contentType.splitOn ";").headD contentType
  media == "application/xml" || media == "text/xml" || media.endsWith "+xml" || media == "text/html"

def viewportPattern (step : XML.Node) (env : XPath4.Env) : Result XSLT4.Pattern := do
  let source ← option step "match" env
  let static : XSLT4.SCx := { ns := ns step, xpathNs := ((ns step).lookup "").getD "", baseUri := env.baseUri }
  (static.pattern source).mapError fun e => ⟨"XS0107", e.msg, false⟩

/-- Unlike XSLT template rule selection, a viewport does not mask pattern
errors. The underlying XSLT pattern evaluator is shared. -/
def viewportMatches (pattern : XSLT4.Pattern) (env : XPath4.Env) (node : XPath4.NodeRef) : Result Bool :=
  let item := XPath4.Item.node node
  let e := { env with vars := (XSLT4.vCurrent, [item]) :: env.vars }
  match pattern.ip with
  | some (ip, _) => pure (XSLT4.ipMatch e 512 ip item)
  | none => (XSLT4.patMatch e 512 pattern.e item).mapError fun err =>
      ⟨if err.code.startsWith "XPST" then "XS0107" else err.code, err.msg, false⟩

/-- Store the iteration position at selected topmost nodes. A selected ancestor
suppresses every descendant; unmatched attributes are never rebuilt as children. -/
def viewportPositions (pattern : XSLT4.Pattern) (env : XPath4.Env) : Result (Array Nat × Nat) := do
  let doc := env.docs[0]!
  let mut positions := Array.replicate doc.nodes.size 0
  let mut count := 0
  let mut skipUntil := 0
  for idx in [:doc.nodes.size] do
    if idx < skipUntil then continue
    let ref : XPath4.NodeRef := ⟨0, idx, none⟩
    if ← viewportMatches pattern env ref then
      let record := doc.get idx
      if record.kind == .attribute || record.kind == .namespace then
        return ← error "XD0010" "viewport match selects an attribute or namespace node"
      count := count + 1
      positions := positions.set! idx count
      skipUntil := record.last + 1
  pure (positions, count)

/-- Detached replacement roots without a default namespace must stay in no
namespace when inserted below an element that has a default namespace. -/
def viewportReplacement : XML.Node → XML.Node
  | .element name attrs children =>
    if attrs.any (·.name == "xmlns") then .element name attrs children
    else .element name ({name := "xmlns", value := ""} :: attrs) children
  | n => n

/-- Rebuild the document from its XDM table, replacing a selected subtree with
all documents returned by the callback, without reprocessing those documents. -/
def viewportRebuild (env : XPath4.Env) (source : Document) (positions : Array Nat) (count : Nat)
    (callback : Nat → Nat → Document → IO (Result (List Document))) :
    Nat → XPath4.NodeRef → IO (Result (List XML.Node))
  | 0, _ => pure (unsupported "viewport tree depth limit")
  | fuel+1, ref => do
    let record := env.nrec ref
    let position := positions[ref.idx]?.getD 0
    if position > 0 then
      let fragment ← match nodeFromRef env (fuel+1) ref with
        | .error e => return .error e
        | .ok n => pure n
      let input : Document := { source with
        node := fragment
        baseUri := (env.baseUriOf ref).getD source.baseUri
        contentType := if record.kind == .text then "text/plain" else source.contentType }
      match ← callback position count input with
      | .error e => return .error e
      | .ok outputs =>
        if outputs.any (fun d => !(viewportXmlType d.contentType) && !(d.contentType.startsWith "text/")) then
          return error "XD0073" "viewport subpipeline result is not XML, HTML, or text"
        return .ok ((outputs.flatMap documentNodes).map viewportReplacement)
    let mut children : Array XML.Node := #[]
    for child in record.children do
      match ← viewportRebuild env source positions count callback fuel (ref.at child) with
      | .error e => return .error e
      | .ok nodes => children := children ++ nodes.toArray
    match record.kind with
    | .document => return .ok children.toList
    | .element =>
      let attrs := record.attrs.toList.map fun idx =>
        let a := env.nrec (ref.at idx)
        ({ name := a.name.show, value := a.value } : XML.Attribute)
      let decls := record.inscope.map fun (p, uri) =>
        ({ name := if p == "" then "xmlns" else "xmlns:" ++ p, value := uri } : XML.Attribute)
      return .ok [.element record.name.show (attrs ++ decls) children.toList]
    | .text => return .ok [.text record.value]
    | .comment => return .ok [.comment record.value]
    | .pi => return .ok [.pi record.name.loc record.value]
    | _ => return error "XD0010" "viewport cannot materialize an attribute or namespace as a child"

/-- The callback receives iteration position, iteration size, and current
subtree document. Runtime provides the subpipeline and its port bindings. -/
def viewportStepWithFocus (step : XML.Node) (docs : List Document) (env : XPath4.Env)
    (callback : Nat → Nat → Document → IO (Result (List Document))) : IO (Result (List Document)) := do
  if docs.any (fun d => !viewportXmlType d.contentType) then
    return error "XD0072" "viewport requires XML or HTML sources"
  let pattern ← match viewportPattern step env with
    | .error e => return .error e
    | .ok p => pure p
  let mut plans : Array (Document × XPath4.Env × Array Nat × Nat) := #[]
  let mut total := 0
  for source in docs do
    let e := { env with
      docs := #[XPath4.Doc.ofNodes (documentNodes source) source.baseUri]
      ctx := some [.node ⟨0,0,none⟩] }
    let (positions, count) ← match viewportPositions pattern e with
      | .error er => return .error er
      | .ok p => pure p
    plans := plans.push (source, e, positions, count)
    total := total + count
  let mut output : Array Document := #[]
  let mut offset := 0
  for (source, e, positions, count) in plans do
    match ← viewportRebuild e source positions total
        (fun position size doc => callback (offset + position) size doc) 4096 ⟨0,0,none⟩ with
    | .error er => return .error er
    | .ok nodes =>
      let node := match nodes with | [n] => n | _ => XML.Node.element "#document" [] nodes
      output := output.push { source with node }
    offset := offset + count
  return .ok output.toList

def viewportStep (step : XML.Node) (docs : List Document) (env : XPath4.Env)
    (callback : Document → IO (Result (List Document))) : IO (Result (List Document)) :=
  viewportStepWithFocus step docs env (fun _ _ doc => callback doc)

-- Topmost selection must not run the subpipeline again on nested matches.
#guard (do
  let source : Document := {node := .element "a" [] [.element "a" [] []]}
  let env := xpathEnv (some source)
  let pattern ← viewportPattern (.element "p:viewport" [{name := "match", value := "a"}] []) env
  let (_, count) ← viewportPositions pattern env
  pure count : Result Nat).toOption == some 1

#guard (do
  let source : Document := {node := .element "a" [{name := "x", value := "1"}] []}
  let env := xpathEnv (some source)
  let pattern ← viewportPattern (.element "p:viewport" [{name := "match", value := "@x"}] []) env
  viewportPositions pattern env : Result (Array Nat × Nat)).toBool == false

end L4Factoidal.XProc31
