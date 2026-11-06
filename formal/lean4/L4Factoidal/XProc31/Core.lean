import L4Factoidal.XPath4.Eval
import L4Factoidal.XPath4.Serialize
import L4Factoidal.XML.Theorems

namespace L4Factoidal.XProc31
open XML

structure Document where
  node : XML.Node
  contentType : String := "application/xml"
  baseUri : String := ""
  /-- Non-core document properties, with QName keys and retained XDM values.
      content-type and base-uri are materialized from the fields above. -/
  properties : List (XPath4.Atomic × XPath4.Seq) := []
  /-- Native XDM content for map/array documents. Serialization occurs only at boundaries. -/
  value : Option XPath4.Seq := none
deriving Inhabited

structure ProcError where
  code : String
  message : String
  unsupported : Bool := false
  details : List XML.Node := []
  errorName : Option XPath4.QN := none
deriving Inhabited, Repr

abbrev Result := Except ProcError

def unsupported {α} (s : String) : Result α := .error ⟨"unsupported", s, true, [], none⟩
def error {α} (code msg : String) : Result α := .error ⟨code, msg, false, [], none⟩
def localName (s : String) : String := (XPath4.splitName s).2
def tag (n : Node) : String := localName (n.elementTag.getD "")
def attr (n : Node) (s : String) (fallback : String := "") : String :=
  (XML.findAttr s n.elementAttrs).getD fallback
def kids (n : Node) : List Node := n.allChildElements
def children : Node → List Node | .element _ _ cs => cs | _ => []
def named (n : Node) (s : String) : List Node := (kids n).filter (fun c => tag c == s)
def ns (n : Node) : List (String × String) := n.elementAttrs.filterMap fun a =>
  if a.name == "xmlns" then some ("", a.value)
  else if a.name.startsWith "xmlns:" then some ((a.name.drop 6).toString, a.value) else none

def inheritNS : Nat → List XML.Attribute → Node → Node
  | 0, _, n => n
  | f+1, inherited, .element t as cs =>
    let extra := inherited.filter (fun a => !(as.any (fun b => a.name == b.name)))
    let as := as ++ extra
    let decls := as.filter (fun a => a.name == "xmlns" || a.name.startsWith "xmlns:")
    .element t as (cs.map (inheritNS f decls))
  | _, _, n => n

def documentNodes (d : Document) : List Node :=
  match d.node with
  | .element "#document" _ cs => cs
  | n => [n]

def documentElement (d : Document) : Node :=
  ((documentNodes d).find? (fun n => n.elementTag.isSome)).getD d.node

def documentXml (d : Document) : String := String.join ((documentNodes d).map Node.serialize)

def propertyName (key : XPath4.Atomic) : Option XPath4.QN :=
  match key.v with
  | .qn q => some q
  | _ => none

def documentProperties (d : Document) : List (XPath4.Atomic × XPath4.Seq) :=
  [(XPath4.Atomic.ofQN ⟨"", "content-type", ""⟩, XPath4.sStr d.contentType)] ++
  (if d.baseUri == "" then [] else [(XPath4.Atomic.ofQN ⟨"", "base-uri", ""⟩, [.atom (XPath4.Atomic.ofUri d.baseUri)])]) ++
  d.properties.filter (fun (key,_) => propertyName key != some ⟨"", "content-type", ""⟩ && propertyName key != some ⟨"", "base-uri", ""⟩)

def documentProperty (d : Document) (name : XPath4.QN) : XPath4.Seq :=
  ((documentProperties d).find? (fun (key,_) => propertyName key == some name)).map (·.2) |>.getD []

/-- Detach property node references from the current document-table numbering.
Nested maps and arrays retain their types and values; nothing is serialized. -/
def retainItems (env : XPath4.Env) : Nat → XPath4.Seq → XPath4.Seq
  | 0, values => values
  | f+1, values => values.map fun item => match item with
    | .node n => .node {n with rt := some (env.doc n)}
    | .map entries => .map (entries.map (fun (k,v) => (k,retainItems env f v)))
    | .arr members => .arr (members.map (retainItems env f))
    | _ => item

def xpathEnv (context : Option Document) (bindings : List (XPath4.QN × XPath4.Seq) := [])
    (namespaces : List (String × String) := []) (pos size : Nat := 1) : XPath4.Env :=
  match context with
  | none => { ns := namespaces, vars := bindings }
  | some d =>
    let binary := match d.value with
      | some [.atom a] => match a.v with | .x (.bin ..) => true | _ => false
      | _ => false
    { docs := #[XPath4.Doc.ofNodes (if binary then [] else documentNodes d) d.baseUri]
      ctx := if binary then some [.node ⟨0,0,none⟩] else if d.value.isSome then d.value else if d.contentType == "application/json" || d.contentType.endsWith "+json" then
        match XPath4.evalString "parse-json($raw)" { vars := [(⟨"", "raw", ""⟩, XPath4.sStr d.node.textContent)] } with
        | .ok value => some value
        | .error _ => none
      else some [.node ⟨0,0,none⟩]
      pos := pos
      size := size
      ns := namespaces
      vars := bindings
      baseUri := d.baseUri }

def fromXPath {α} (r : XPath4.M α) : Result α := r.mapError fun e =>
  ⟨e.code, e.msg, e.code == "XPST0017" || e.msg.contains "not implemented", [], none⟩

def eval (s : String) (env : XPath4.Env) : Result XPath4.Seq :=
  (fromXPath (XPath4.evalString s env)).mapError fun e =>
    if e.code == "XPDY0002" then { e with code := "XD0001" } else e
def evalBool (s : String) (env : XPath4.Env) : Result Bool := do
  fromXPath (XPath4.ebv (← eval s env))
def seqString (env : XPath4.Env) (s : XPath4.Seq) : String :=
  String.intercalate " " (s.map (fun i => match i with
    | .atom a => a.str
    | .node n => (env.doc n).stringValue n.idx
    | _ => ""))

/-- Scan one enclosed XPath expression. Braces in strings and nested comments
are not delimiters. The accumulator is reversed to keep scanning linear. -/
def scanAvtExpression : Nat → List Char → Nat → Option Char → Nat → List Char →
    Result (String × List Char)
  | 0, _, _, _, _, _ => unsupported "AVT expression scanning limit"
  | _+1, [], _, _, _, _ => error "XS0107" "unclosed attribute value template expression"
  | fuel+1, c::cs, depth, quote, comments, acc =>
    if comments > 0 then
      match c, cs with
      | '(', ':'::rest => scanAvtExpression fuel rest depth none (comments+1) (':'::'('::acc)
      | ':', ')'::rest => scanAvtExpression fuel rest depth none (comments-1) (')'::':'::acc)
      | _, _ => scanAvtExpression fuel cs depth none comments (c::acc)
    else match quote with
    | some q =>
      if c == q then
        match cs with
        | d::rest =>
          if d == q then scanAvtExpression fuel rest depth quote 0 (d::c::acc)
          else scanAvtExpression fuel cs depth none 0 (c::acc)
        | [] => scanAvtExpression fuel cs depth none 0 (c::acc)
      else scanAvtExpression fuel cs depth quote 0 (c::acc)
    | none =>
      match c, cs with
      | '(', ':'::rest => scanAvtExpression fuel rest depth none 1 (':'::'('::acc)
      | '\'', _ | '"', _ => scanAvtExpression fuel cs depth (some c) 0 (c::acc)
      | '{', _ => scanAvtExpression fuel cs (depth+1) none 0 (c::acc)
      | '}', _ =>
        if depth == 0 then pure (String.ofList acc.reverse, cs)
        else scanAvtExpression fuel cs (depth-1) none 0 (c::acc)
      | _, _ => scanAvtExpression fuel cs depth none 0 (c::acc)

/-- XProc value templates accept atomic values and XML nodes. An array,
map or function must raise XD0051, including inside a mixed sequence. -/
def avtSequenceString (env : XPath4.Env) (items : XPath4.Seq) : Result String := do
  let strings ← items.mapM fun item => match item with
    | .atom a => pure a.str
    | .node n => pure ((env.doc n).stringValue n.idx)
    | _ => error "XD0051" "value template result contains a map, array or function"
  pure (String.intercalate " " strings)

/-- Evaluate an AVT with a reversed output character accumulator. Each source
character is scanned once; each expression is passed to the XPath evaluator. -/
def renderAvt (env : XPath4.Env) : Nat → List Char → List Char → Result String
  | 0, _, _ => unsupported "AVT scanning limit"
  | _+1, [], out => pure (String.ofList out.reverse)
  | fuel+1, '{'::'{'::cs, out => renderAvt env fuel cs ('{'::out)
  | fuel+1, '}'::'}'::cs, out => renderAvt env fuel cs ('}'::out)
  | fuel+1, '{'::cs, out => do
      let (expression, rest) ← scanAvtExpression (fuel+1) cs 0 none 0 []
      let values ← match eval expression env with
        | .error e =>
          if e.code == "XPST0003" then error "XS0107" e.message else .error e
        | .ok v => pure v
      let value ← avtSequenceString env values
      renderAvt env fuel rest (value.toList.reverse ++ out)
  | _+1, '}'::_, _ => error "XS0107" "unescaped closing brace in attribute value template"
  | fuel+1, c::cs, out => renderAvt env fuel cs (c::out)

def avtLoop (env : XPath4.Env) (fuel : Nat) (cs : List Char) (out : String) : Result String :=
  renderAvt env fuel cs out.toList.reverse

def avt (s : String) (env : XPath4.Env) : Result String :=
  avtLoop env (s.length+1) s.toList ""

#guard (avt "{{literal}}: {(1,2,3)}" {}).toOption == some "{literal}: 1 2 3"
#guard (avt "{map{'x': map{'y': 7}}?x?y}" {}).toOption == some "7"
#guard (avt "{'a}''b'}" {}).toOption == some "a}'b"
#guard (avt "{(: } (: { :) :) 3}" {}).toOption == some "3"
#guard (avt "{map{'x':1}}" {}).toBool == false
#guard (match avt "{('ok', [1,2])}" {} with | .error e => e.code | .ok _ => "") == "XD0051"
#guard (match avt "{(17}" {} with | .error e => e.code | .ok _ => "") == "XS0107"
#guard (match avt "unescaped}" {} with | .error e => e.code | .ok _ => "") == "XS0107"

def option (step : Node) (name : String) (env : XPath4.Env) (fallback : String := "") : Result String :=
  match (named step "with-option").find? (fun n => attr n "name" == name) with
  | some n => do pure (seqString env (← eval (attr n "select") env))
  | none => avt (attr step name fallback) env

def nodeFromRef (env : XPath4.Env) : Nat → XPath4.NodeRef → Result Node
  | 0, _ => unsupported "result tree depth limit"
  | f+1, n => do
    let r := env.nrec n
    match r.kind with
    | .text => pure (.text r.value)
    | .comment => pure (.comment r.value)
    | .pi => pure (.pi r.name.loc r.value)
    | .element =>
      let ats := r.attrs.toList.map fun i =>
        let a := env.nrec (n.at i)
        ({name := a.name.show, value := a.value} : XML.Attribute)
      let decls := r.inscope.map fun (p,u) => ({name := if p == "" then "xmlns" else "xmlns:" ++ p, value := u} : XML.Attribute)
      pure (.element r.name.show (ats ++ decls) (← r.children.toList.mapM (fun i => nodeFromRef env f (n.at i))))
    | .document =>
      match r.children.toList with
      | [i] => nodeFromRef env f (n.at i)
      | cs => pure (.element "#document" [] (← cs.mapM (fun i => nodeFromRef env f (n.at i))))
    | _ => error "XD0016" "attribute or namespace cannot be a document"

def seqDocuments (env : XPath4.Env) (s : XPath4.Seq) (baseUri : String := "") : Result (List Document) :=
  s.mapM fun i => match i with
    | .node n => do
      let node ← nodeFromRef env 4096 n
      let textOnly := match node with | .text _ | .cdata _ => true | _ => false
      pure {node, baseUri := if textOnly then "" else baseUri, contentType := if textOnly then "text/plain" else "application/xml"}
    | .atom a =>
      let binary := match a.v with | .x (.bin ..) => true | _ => false
      pure {node := .text a.str, contentType := if binary then "application/octet-stream" else "application/json", value := some [.atom a]}
    | .map _ | .arr _ => pure {node := .text "", contentType := "application/json", baseUri, value := some (retainItems env 4096 [i])}
    | _ => unsupported "function item cannot be a document"

def identity (docs : List Document) : List Document := docs
def forEachDocuments (f : Document → Result (List Document)) (docs : List Document) : Result (List Document) :=
  List.flatten <$> docs.mapM f

end L4Factoidal.XProc31

namespace L4Factoidal.XProc31
/-- The native map payload preserves both multi-item values and node identity. -/
private def nativeMapProbe : Result Bool := do
  let source : Document := {node := .element "node" [] [.text "retained"]}
  let env := xpathEnv (some source)
  let docs ← seqDocuments env [.map [(XPath4.Atomic.ofStr "sequence", XPath4.sInt 1 ++ XPath4.sInt 2),
    (XPath4.Atomic.ofStr "node", [.node ⟨0,0,none⟩])]]
  let some doc := docs.head? | pure false
  let context := xpathEnv (some doc)
  evalBool "count(.?sequence) = 2 and .?node/node/string() = 'retained'" context
#guard nativeMapProbe.toOption == some true
end L4Factoidal.XProc31
