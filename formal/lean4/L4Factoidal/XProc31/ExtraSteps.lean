import L4Factoidal.XProc31.Core
import L4Factoidal.XML.Encoding
import L4Factoidal.XPath4.BaseUri
import L4Factoidal.XPath4.Uri

namespace L4Factoidal.XProc31
open XML

def supportsExtra (name : String) : Bool := ["namespace-rename", "xinclude"].contains name

def extraOne (docs : List Document) : Result Document :=
  match docs with | [d] => pure d | _ => error "XD0006" "step requires one source document"

def scopeSet (scope : List (String × String)) (pfx uri : String) : List (String × String) :=
  (pfx,uri) :: scope.filter (·.1 != pfx)

def nameInScope (scope : List (String × String)) (isAttribute : Bool) (name : String) : XPath4.QN :=
  let (pfx,loc) := XPath4.splitName name
  { pfx, loc, uri := if isAttribute && pfx == "" then "" else if pfx == "xml" then XPath4.nsXML else (scope.lookup pfx).getD "" }

def freshPrefix (scope : List (String × String)) : String := Id.run do
  for i in [:scope.length+1] do
    let p := "ns" ++ toString (i+1)
    if !(scope.any (·.1 == p)) then return p
  return "ns" ++ toString (scope.length+2)

/-- Rename expanded names first, then fix namespace bindings. Prefix conflicts
between an element and an unchanged attribute require a fresh prefix. -/
def renameNamespaceTree (fromUri toUri applyTo : String) : Nat → List (String × String) → Node → Result Node
  | 0, _, _ => unsupported "namespace-rename tree depth limit"
  | fuel+1, inherited, .element name attrs children => do
    let original := (ns (.element name attrs children)).foldr (fun (p,u) sc => scopeSet sc p u) inherited
    let element := nameInScope original false name
    let newUri := if applyTo != "attributes" && element.uri == fromUri then toUri else element.uri
    let newPrefix := if newUri == "" then "" else element.pfx
    let newName := if newPrefix == "" then element.loc else newPrefix ++ ":" ++ element.loc
    let mut scope := scopeSet original newPrefix newUri
    let mut used := [(newPrefix,newUri)]
    let mut seen : List (String × String) := []
    let mut output : Array XML.Attribute := #[]
    for a in attrs do
      if a.name == "xmlns" || a.name.startsWith "xmlns:" then continue
      let q := nameInScope original true a.name
      let uri := if applyTo != "elements" && q.uri == fromUri then toUri else q.uri
      if seen.contains (uri,q.loc) then return ← error "XC0092" "namespace rename creates duplicate expanded attribute names"
      seen := (uri,q.loc) :: seen
      let pfx := if uri == "" then "" else if uri == XPath4.nsXML then "xml"
        else if q.pfx != "" && ((used.lookup q.pfx).isNone || used.lookup q.pfx == some uri) then q.pfx
        else match scope.find? (fun (p,u) => p != "" && u == uri && ((used.lookup p).isNone || used.lookup p == some uri)) with
          | some (p,_) => p
          | none => freshPrefix scope
      if pfx != "" then
        scope := scopeSet scope pfx uri
        used := (pfx,uri) :: used
      output := output.push {name := if pfx == "" then q.loc else pfx ++ ":" ++ q.loc, value := a.value}
    let declarations := scope.filterMap fun (p,u) =>
      if p == "xml" || (p != "" && u == "") then none
      else some ({name := if p == "" then "xmlns" else "xmlns:" ++ p, value := u} : XML.Attribute)
    let children ← children.mapM (renameNamespaceTree fromUri toUri applyTo fuel original)
    pure (.element newName (output.toList ++ declarations) children)
  | _, _, n => pure n

def namespaceRenameStep (step : Node) (docs : List Document) (env : XPath4.Env) : Result (List Document) := do
  let source ← extraOne docs
  let fromUri ← option step "from" env ""
  let toUri ← option step "to" env ""
  let applyTo ← option step "apply-to" env "all"
  if !["all", "elements", "attributes"].contains applyTo then error "XD0036" "invalid namespace-rename apply-to"
  else if [fromUri,toUri].any (fun u => u == XPath4.nsXML || u == "http://www.w3.org/2000/xmlns/") then
    unsupported "renaming reserved XML namespaces"
  else
    let node ← renameNamespaceTree fromUri toUri applyTo 4096 [] source.node
    pure [{source with node}]

/-- XPointer framework scheme data; escaped parentheses do not affect balance. -/
def pointerBody : Nat → List Char → Nat → List Char → Result (String × List Char)
  | 0, _, _, _ => unsupported "XPointer scanning limit"
  | _+1, [], _, _ => error "XC0029" "unclosed XPointer scheme"
  | fuel+1, '^'::c::rest, depth, acc =>
    if c == '^' || c == '(' || c == ')' then pointerBody fuel rest depth (c::acc)
    else error "XC0029" "invalid XPointer escape"
  | fuel+1, '('::rest, depth, acc => pointerBody fuel rest (depth+1) ('('::acc)
  | fuel+1, ')'::rest, depth, acc =>
    if depth == 1 then pure (String.ofList acc.reverse,rest)
    else pointerBody fuel rest (depth-1) (')'::acc)
  | fuel+1, c::rest, depth, acc => pointerBody fuel rest depth (c::acc)

def pointerSchemes : Nat → List Char → List (String × String) → Result (List (String × String))
  | 0, _, _ => unsupported "XPointer schemes limit"
  | fuel+1, source, out => do
    let source := source.dropWhile Char.isWhitespace
    if source.isEmpty then pure out.reverse else
    let name := source.takeWhile (· != '(')
    let rest := source.drop name.length
    if rest.isEmpty then error "XC0029" "invalid XPointer scheme" else
    let (body,rest) ← pointerBody (source.length+1) rest.tail! 1 []
    pointerSchemes fuel rest ((String.ofList name |>.trimAscii.toString,body)::out)

def xincludeLanguage (env : XPath4.Env) (ref : XPath4.NodeRef) : String := Id.run do
  for r in ref :: env.ancestors ref do
    let record := env.nrec r
    for a in record.attrs do
      let a := env.nrec (r.at a)
      if a.name.uri == XPath4.nsXML && a.name.loc == "lang" then return a.value
  return ""

def setXmlAttribute (node : Node) (name value : String) : Node :=
  match node with
  | .element tag attrs children => .element tag ({name,value} :: attrs.filter (·.name != name)) children
  | n => n

structure IncludeOptions where
  fixBase : Bool := true
  fixLang : Bool := true

def xincludeSelect (nodes : List Node) (uri pointer parentLang : String) (options : IncludeOptions) : Result (List Node) := do
  let env : XPath4.Env := { docs := #[XPath4.Doc.ofNodes nodes uri], ctx := some [.node ⟨0,0,none⟩] }
  let selected ← if pointer == "" then pure [.node ⟨0,0,none⟩] else
    if !pointer.contains '(' then
      eval "//*[@xml:id = $id]" {env with vars := [(⟨"","id",""⟩, XPath4.sStr pointer)]}
    else do
      let schemes ← pointerSchemes (pointer.length+1) pointer.toList []
      let mut namespaces := []
      let mut found : XPath4.Seq := []
      for (scheme,body) in schemes do
        if scheme == "xmlns" then
          match body.splitOn "=" with
          | p::rest => namespaces := (p.trimAscii.toString, String.intercalate "=" rest |>.trimAscii.toString) :: namespaces
          | _ => pure ()
        else if scheme == "xpath" || scheme == "xpointer" then
          let value ← eval body {env with ns := namespaces}
          if !value.isEmpty then found := value; break
        else if scheme == "element" then
          return ← unsupported "XPointer element scheme"
      if found.isEmpty then error "XC0029" "XPointer selected no nodes" else pure found
  if selected.isEmpty then return ← error "XC0029" "XPointer selected no nodes"
  let mut result : Array Node := #[]
  for item in selected do
    let ref ← match item with | .node r => pure r | _ => error "XC0029" "XPointer selected a non-node"
    let refs := if (env.nrec ref).kind == .document then (env.nrec ref).children.toList.map ref.at else [ref]
    for ref in refs do
      if (env.nrec ref).kind == .attribute || (env.nrec ref).kind == .namespace then
        return ← error "XC0029" "XPointer selected an attribute or namespace"
      let mut node ← nodeFromRef env 4096 ref
      if (env.nrec ref).kind == .element then
        if options.fixBase then node := setXmlAttribute node "xml:base" ((env.baseUriOf ref).getD uri)
        let lang := xincludeLanguage env ref
        if options.fixLang && lang != parentLang then node := setXmlAttribute node "xml:lang" lang
        if (XML.findAttr "xmlns" node.elementAttrs).isNone then node := setXmlAttribute node "xmlns" ""
      result := result.push node
  pure result.toList

/-- File access stays in IO; parsing, inclusion, pointer evaluation, and fixup
are Lean functions. Network retrieval is explicitly unsupported. -/
def includeBytes (uri : String) : IO (Result ByteArray) := do
  if uri.startsWith "http:" || uri.startsWith "https:" then return unsupported "network XInclude retrieval"
  if XPath4.uriHasScheme uri && !uri.startsWith "file:" then return unsupported "non-file XInclude URI"
  if uri.contains '#' then return error "XC0029" "XInclude href must not contain a fragment identifier"
  let raw := if uri.startsWith "file://localhost/" then (uri.drop 16).toString
    else if uri.startsWith "file://" then (uri.drop 7).toString else uri
  if uri.startsWith "file://" && !raw.startsWith "/" then return unsupported "remote file authority in XInclude URI"
  let path := XPath4.uriDecode false raw
  try return .ok (← IO.FS.readBinFile path)
  catch e => return error "XC0029" (toString e)

mutual

def includeNodes (options : IncludeOptions) (active : List String) : Nat → String → String → List Node → IO (Result (List Node))
  | 0, _, _, _ => pure (unsupported "XInclude depth limit")
  | fuel+1, base, lang, nodes => do
    let mut out : Array Node := #[]
    for node in nodes do
      match ← includeNode options active fuel base lang node with
      | .error e => return .error e
      | .ok result => out := out ++ result.toArray
    return .ok out.toList

def includeNode (options : IncludeOptions) (active : List String) : Nat → String → String → Node → IO (Result (List Node))
  | 0, _, _, _ => pure (unsupported "XInclude depth limit")
  | fuel+1, base, lang, node => do
    let base := if attr node "xml:base" == "" then base else XPath4.resolveRef base (attr node "xml:base")
    let lang := (XML.findAttr "xml:lang" node.elementAttrs).getD lang
    let q := nameInScope (ns node) false (node.elementTag.getD "")
    if q.uri == "http://www.w3.org/2001/XInclude" && q.loc == "include" then
      let uri := XPath4.resolveRef base (attr node "href")
      if active.contains uri then return error "XC0029" "cyclic XInclude"
      let result ← includeResource options (uri :: active) fuel uri (attr node "parse" "xml")
        (attr node "encoding") (attr node "xpointer") lang
      match result with
      | .ok nodes => return .ok nodes
      | .error e =>
        if e.unsupported then return .error e
        let fallbacks := (kids node).filter fun child =>
          let q := nameInScope (ns child) false (child.elementTag.getD "")
          q.uri == "http://www.w3.org/2001/XInclude" && q.loc == "fallback"
        match fallbacks with
        | [fallback] => includeNodes options active fuel base lang (children fallback)
        | _ => return .error e
    else match node with
    | .element name attrs children =>
      match ← includeNodes options active fuel base lang children with
      | .error e => return .error e
      | .ok children => return .ok [.element name attrs children]
    | n => return .ok [n]

def includeResource (options : IncludeOptions) (active : List String) (fuel : Nat)
    (uri parse encoding pointer parentLang : String) : IO (Result (List Node)) := do
  let bytes ← match ← includeBytes uri with
    | .error e => return .error e
    | .ok bytes => pure bytes
  if parse == "text" then
    if pointer != "" then return unsupported "text XInclude with XPointer"
    let text := XPath4.decodeResource bytes (if encoding == "" then none else some encoding) false
    return do
      let text ← text.mapError (fun e => ⟨"XC0029",e.msg,false⟩)
      if !text.toList.all XML.isXmlChar then error "XC0029" "text inclusion contains a character forbidden in XML"
      else pure [.text ((text.replace "\r\n" "\n").replace "\r" "\n")]
  else if parse != "xml" then return error "XC0029" "invalid XInclude parse mode"
  else
    let text ← match XML.decodeXmlBytes bytes with
      | .error e => return error "XC0029" e
      | .ok text => pure text
    let document ← match XML.parseXML text with
      | .error e => return error "XC0029" (toString e)
      | .ok document => pure document
    let nodes := document.children.map (inheritNS 4096 [])
    match ← includeNodes options active fuel uri "" nodes with
    | .error e => return .error e
    | .ok nodes => return xincludeSelect nodes uri pointer parentLang options
end

def xincludeStep (step : Node) (docs : List Document) (env : XPath4.Env) : IO (Result (List Document)) := do
  let source ← match extraOne docs with | .error e => return .error e | .ok d => pure d
  let options ← match (do
      let base ← option step "fixup-xml-base" env "true"
      let lang ← option step "fixup-xml-lang" env "true"
      if !["true","false","1","0"].contains base || !["true","false","1","0"].contains lang then
        error "XD0036" "XInclude fixup option must be boolean"
      else pure ({fixBase := base == "true" || base == "1", fixLang := lang == "true" || lang == "1"} : IncludeOptions)) with
    | .error e => return .error e
    | .ok options => pure options
  let nodes := (documentNodes source).map (inheritNS 4096 [])
  match ← includeNodes options [source.baseUri] 4096 source.baseUri "" nodes with
  | .error e => return .error e
  | .ok nodes =>
    let node := match nodes with | [n] => n | _ => .element "#document" [] nodes
    return .ok [{source with node}]

def extraAtomic (step : Node) (ports : List (String × List Document)) (env : XPath4.Env) : IO (Result (List Document)) :=
  let source := (ports.lookup "source").getD []
  match tag step with
  | "namespace-rename" => pure (namespaceRenameStep step source env)
  | "xinclude" => xincludeStep step source env
  | _ => pure (unsupported ("extra step " ++ tag step))

#guard (renameNamespaceTree "urn:a" "" "all" 20 []
  (.element "a" [{name := "xmlns:n", value := "urn:a"}, {name := "x",value := "1"}, {name := "n:x",value := "2"}] [])).toBool == false
#guard (pointerSchemes 100 "xpath(/doc/p[contains(.,'^(x^)')])".toList []).toOption ==
  some [("xpath", "/doc/p[contains(.,'(x)')]")]

end L4Factoidal.XProc31
