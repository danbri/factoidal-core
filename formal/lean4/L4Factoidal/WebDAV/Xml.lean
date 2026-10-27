/-
L4Factoidal.WebDAV.Xml — the XML bodies of WebDAV (RFC 4918 §14).
https://github.com/danbri/factoidal/issues/1066

Request bodies are read with this tree's XML parser
(`L4Factoidal.XML.Parser.parseXML`) and its namespace layer
(`applyDeclarations`, `resolveElementName`): an element is matched by its
EXPANDED name (namespace name and local part), never by its prefix, as RFC
4918 §17 requires ("element names ... are qualified by namespace"). A body
that is not well-formed XML, or not namespace-well-formed, is refused (400,
RFC 4918 §8.2: "the server MUST respond with a 400 (Bad Request)").

Responses are written with the tree's serializer output (`Node.serialize`, produced from a work list by `serializeFlat`), one
`DAV:response` at a time, joined in one loop, so a multistatus of any
number of members is written in fixed stack.

A dead property keeps the element the client sent, as written, and the
namespace bindings in force at it (`DeadValue`); writing it back adds those
bindings as declarations on the element, so a value whose content uses a
prefix declared on an ancestor of the property (litmus `propvalnspace`)
reads back the same.

Every reader here descends one level at a time (`El.children`, a
`filterMap` over one child list); no reader recurses over the depth of the
document.
-/
import L4Factoidal.XML.Theorems
import L4Factoidal.XML.NamespaceView
import L4Factoidal.WebDAV.Config

namespace L4Factoidal.WebDAV

open L4Factoidal.XML

def davNs : String := "DAV:"

/-- An element of a request body: its expanded name, the element as written,
the namespace bindings in force at it (after its own declarations), and the
XML version of the document. -/
structure El where
  name : ExpandedName
  raw : Node
  scope : NsScope
  version : String := "1.0"

instance : Inhabited El := ⟨{ name := { namespace_ := none, localPart := "" }, raw := .text "", scope := [] }⟩

/-- Is the element `DAV:<local>`? -/
def El.isDav (e : El) (local_ : String) : Bool :=
  e.name.namespace_ == some davNs && e.name.localPart == local_

/-- The element children, each with its scope. -/
def El.children (e : El) : List El :=
  match e.raw with
  | .element _ _ kids => kids.filterMap (fun k =>
      match k with
      | .element tag attrs _ => do
          let sc ← applyDeclarations e.version e.scope attrs
          let n ← resolveElementName sc tag
          pure { name := n, raw := k, scope := sc, version := e.version }
      | _ => none)
  | _ => []

def El.child? (e : El) (local_ : String) : Option El :=
  e.children.find? (·.isDav local_)

/-- The character content of an element, its children's included. -/
def El.text (e : El) : String := e.raw.textContent

/-- The deepest element nesting a request body may have. A body deeper than
this is refused (400) before it is parsed: the parse tree and its
serialization recurse once per nesting level, and a property value of
100,000 levels overflowed the wasm stack (tests/webdav/scaling.mjs,
2026-10-27). RFC 4918 sets no depth; a server may refuse a body it does
not process (§8.2: 400 for a body it cannot read as the method requires). -/
def maxBodyDepth : Nat := 256

/-- Where the depth scan is: in text, just after `<`, in a start tag (and
in which quote), in an end tag, in `<!…>` or `<?…>`. -/
inductive ScanMode where
  | text | afterLt | startTag | quoted (q : Char) | endTag | other
deriving DecidableEq

/-- The depth scan's state: depth now, deepest seen, mode, the character
before. -/
structure DepthScan where
  depth : Nat := 0
  deepest : Nat := 0
  mode : ScanMode := .text
  prev : Char := ' '

/-- One character of the depth scan. A start tag opens a level, `</`
closes one, `/>` at the end of a start tag closes one. A `/>` in text or
in a quoted attribute value is not a tag end, so text cannot lower the
count; a `<` inside a comment counts as an opening, so the count can be
higher than the true depth, never lower. -/
def depthStep (st : DepthScan) (c : Char) : DepthScan :=
  let st' := match st.mode with
    | .text => if c == '<' then { st with mode := .afterLt } else st
    | .afterLt =>
      if c == '/' then { st with mode := .endTag, depth := st.depth - 1 }
      else if c == '!' || c == '?' then { st with mode := .other }
      else { st with mode := .startTag, depth := st.depth + 1, deepest := max st.deepest (st.depth + 1) }
    | .startTag =>
      if c == '"' || c == '\'' then { st with mode := .quoted c }
      else if c == '>' then
        if st.prev == '/' then { st with mode := .text, depth := st.depth - 1 } else { st with mode := .text }
      else st
    | .quoted q => if c == q then { st with mode := .startTag } else st
    | .endTag | .other => if c == '>' then { st with mode := .text } else st
  { st' with prev := c }

/-- The deepest nesting the scan sees: one fold over the characters. -/
def nestingDepth (s : String) : Nat := (s.foldl depthStep {}).deepest

#guard nestingDepth "<a><b/><c><d>x</d></c></a>" == 3
#guard nestingDepth "<?xml version=\"1.0\"?><!-- c --><a/>" == 1
#guard nestingDepth "<a x=\"/>\"><b>/></b><b>/></b></a>" == 2
#guard nestingDepth "<x>/><x>/><x>/><x>" == 4

/-- Read a request body: the root element. -/
def parseBody (text : String) : Except String El :=
  if nestingDepth text > maxBodyDepth then
    .error s!"the body nests elements deeper than {maxBodyDepth} levels"
  else
  match parseXML text with
  | .error e => .error s!"the body is not well-formed XML ({e.message})"
  | .ok d =>
    if !d.namespaceWellFormed then .error "the body is not namespace-well-formed XML"
    else
      let version := (d.decl.map (·.version)).getD "1.0"
      match d.root with
      | .element tag attrs _ =>
        match applyDeclarations version initialScope attrs with
        | none => .error "the body is not namespace-well-formed XML"
        | some sc =>
          match resolveElementName sc tag with
          | none => .error "the body is not namespace-well-formed XML"
          | some n => .ok { name := n, raw := d.root, scope := sc, version }
      | _ => .error "the body has no root element"

/-! ## Dead property values -/

/-- A dead property's value: the property element as the client wrote it,
and the namespace bindings in force at it that it does not declare itself
(prefix, namespace name; `""` is the default namespace). -/
structure DeadValue where
  raw : Node
  bindings : List (String × String) := []
deriving DecidableEq, Inhabited

/-- The prefixes an element declares on itself. -/
def declaredPrefixes (attrs : List Attribute) : List String :=
  attrs.filterMap (fun a =>
    if a.name == "xmlns" then some ""
    else if a.name.startsWith "xmlns:" then some (dropS a.name 6) else none)

/-- The value of an element, kept for writing back. -/
def El.deadValue (e : El) : DeadValue :=
  let own := declaredPrefixes e.raw.elementAttrs
  { raw := e.raw
    bindings := (visibleBindings e.scope).filter (fun (p, _) => p != "xml" && !own.contains p) }

/-- The element to write: the client's element with the inherited bindings
declared on it. -/
def DeadValue.node (v : DeadValue) : Node :=
  match v.raw with
  | .element tag attrs kids =>
    .element tag (attrs ++ v.bindings.map (fun (p, u) =>
      ({ name := if p == "" then "xmlns" else "xmlns:" ++ p, value := u } : Attribute))) kids
  | other => other

/-- A dead property: its name and its value. -/
structure DeadProp where
  name : ExpandedName
  value : DeadValue
deriving DecidableEq, Inhabited

/-! ## Writing -/

/-- An element in the `DAV:` namespace, written with the prefix `D`. -/
def dav (local_ : String) (kids : List Node := []) : Node := .element ("D:" ++ local_) [] kids

def davText (local_ text : String) : Node := dav local_ [.text text]

/-- An empty element of any expanded name: `D:` for `DAV:`, a declared
prefix `R` for another namespace, and an explicit empty default
namespace for no namespace. -/
def nameNode (n : ExpandedName) (kids : List Node := []) : Node :=
  match n.namespace_ with
  | some u =>
    if u == davNs then dav n.localPart kids
    else .element ("R:" ++ n.localPart) [{ name := "xmlns:R", value := u }] kids
  | none => .element n.localPart [{ name := "xmlns", value := "" }] kids

/-- The reason phrase of a status code (RFC 9110 §15, RFC 4918 §11). -/
def reason : Nat → String
  | 200 => "OK" | 201 => "Created" | 204 => "No Content" | 207 => "Multi-Status"
  | 400 => "Bad Request" | 401 => "Unauthorized" | 403 => "Forbidden" | 404 => "Not Found"
  | 405 => "Method Not Allowed" | 409 => "Conflict" | 412 => "Precondition Failed"
  | 415 => "Unsupported Media Type" | 423 => "Locked" | 424 => "Failed Dependency"
  | 500 => "Internal Server Error" | 502 => "Bad Gateway" | 507 => "Insufficient Storage"
  | _ => "Status"

def statusLine (n : Nat) : String := "HTTP/1.1 " ++ toString n ++ " " ++ reason n

/-- One `DAV:propstat`. -/
def propstat (status : Nat) (props : List Node) : Node :=
  dav "propstat" [dav "prop" props, davText "status" (statusLine status)]

/-- One `DAV:response` with property results. Empty groups are left out. -/
def propResponse (href : String) (groups : List (Nat × List Node)) : Node :=
  dav "response" (davText "href" href ::
    (groups.filter (fun (_, ps) => !ps.isEmpty)).map (fun (s, ps) => propstat s ps))

/-- One `DAV:response` with a status for the resource as a whole. -/
def statusResponse (href : String) (status : Nat) (error : List Node := []) : Node :=
  dav "response" ([davText "href" href, davText "status" (statusLine status)] ++
    (if error.isEmpty then [] else [dav "error" error]))

def xmlDecl : String := "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n"

/-- A piece of the serializer's work list: a node to write, or the end tag
of an element whose children are written. -/
inductive Piece where
  | node (n : Node)
  | close (tag : String)

/-- The tree serializer's output (`Node.serialize`, with its escaping and
its attribute writer) produced from a work list: one loop, so a response
of any width or depth is written in fixed stack. `Node.serialize` recurses
once per child and once per level; a PROPFIND answer with 20,000 property
names overflowed the wasm stack through it (tests/webdav/scaling.mjs,
2026-10-27). The `#guard`s below compare the two on trees with every kind
of node. The fuel (2^30 pieces) is above any response this server can hold
in memory. -/
def serializeLoop : Nat → List Piece → String → String
  | 0, _, acc => acc
  | _, [], acc => acc
  | n + 1, .close t :: rest, acc => serializeLoop n rest (acc ++ "</" ++ t ++ ">")
  | n + 1, .node nd :: rest, acc =>
    match nd with
    | .element tag attrs [] => serializeLoop n rest (acc ++ "<" ++ tag ++ serializeAttrs attrs ++ "/>")
    | .element tag attrs kids =>
      serializeLoop n (kids.map Piece.node ++ (.close tag :: rest)) (acc ++ "<" ++ tag ++ serializeAttrs attrs ++ ">")
    | leaf => serializeLoop n rest (acc ++ leaf.serialize)

def serializeFlat (n : Node) : String := serializeLoop (2 ^ 30) [.node n] ""

private def sampleTree : Node :=
  .element "D:a" [{ name := "x", value := "1\"<" }]
    [ .text "t&<>", .element "b" [] [], .cdata "c]]", .comment " k ", .pi "p" "d"
    , .element "D:c" [] [.element "e" [{ name := "y", value := "\t" }] [.text "deep"]] ]

#guard serializeFlat sampleTree == sampleTree.serialize
#guard serializeFlat (.element "x" [] []) == (Node.element "x" [] []).serialize
#guard serializeFlat (.text "a<b") == (Node.text "a<b").serialize

/-- A 207 body: the responses, each serialized on its own, joined in one
loop. -/
def multistatus (rs : List Node) : String :=
  let body := rs.foldl (fun acc r => acc ++ serializeFlat r ++ "\n") ""
  xmlDecl ++ "<D:multistatus xmlns:D=\"DAV:\">\n" ++ body ++ "</D:multistatus>\n"

/-- A body holding one element in `DAV:` (an error body, RFC 4918 §16, or a
`DAV:prop` answer to LOCK). The `D` prefix is declared on it. -/
def davDocument (n : Node) : String :=
  match n with
  | .element tag attrs kids =>
    xmlDecl ++ serializeFlat (Node.element tag (attrs ++ [{ name := "xmlns:D", value := davNs }]) kids) ++ "\n"
  | other => xmlDecl ++ serializeFlat other

/-- An error body with one precondition element (RFC 4918 §16). -/
def errorBody (condition : Node) : String := davDocument (dav "error" [condition])

/-! ## Reading the request bodies -/

/-- What a PROPFIND asks for (RFC 4918 §9.1, §14.20). -/
inductive PropReq where
  /-- Every property; with `DAV:include`, these too. -/
  | allprop (extra : List ExpandedName)
  | propname
  | prop (names : List ExpandedName)
deriving Inhabited

/-- Read a PROPFIND body. An empty body is `allprop` (RFC 4918 §9.1: "A
client may choose not to submit a request body. An empty PROPFIND request
body MUST be treated as if it were an 'allprop' request."). -/
def propfindOf (body : String) : Except String PropReq :=
  if (trimS body) == "" then .ok (.allprop []) else do
  let root ← parseBody body
  if !root.isDav "propfind" then throw "the body is not DAV:propfind"
  let kids := root.children
  let names (e : El) : List ExpandedName := e.children.map (·.name)
  match kids.find? (·.isDav "allprop"), kids.find? (·.isDav "propname"), kids.find? (·.isDav "prop") with
  | some _, none, none => pure (.allprop (((kids.find? (·.isDav "include")).map names).getD []))
  | none, some _, none => pure .propname
  | none, none, some p => pure (.prop (names p))
  | _, _, _ => throw "DAV:propfind holds exactly one of allprop, propname, prop"

/-- One instruction of a PROPPATCH (RFC 4918 §14.19): set a value, or
remove (`none`). -/
abbrev PatchOp := ExpandedName × Option DeadValue

/-- Read a PROPPATCH body: the instructions in document order (RFC 4918
§9.2: "Instructions MUST either all be executed or none executed ... in
document order"). -/
def proppatchOf (body : String) : Except String (List PatchOp) := do
  let root ← parseBody body
  if !root.isDav "propertyupdate" then throw "the body is not DAV:propertyupdate"
  let groups := root.children.filter (fun e => e.isDav "set" || e.isDav "remove")
  if groups.isEmpty then throw "DAV:propertyupdate holds no set or remove"
  let ops := groups.foldl (fun acc g =>
    let props := ((g.child? "prop").map El.children).getD []
    acc ++ props.map (fun p => ((p.name, if g.isDav "set" then some p.deadValue else none) : PatchOp))) []
  pure ops

/-- What a LOCK request body asks for (RFC 4918 §14.11). -/
structure LockInfo where
  exclusive : Bool
  owner : Option DeadValue := none
deriving Inhabited

def lockinfoOf (body : String) : Except String LockInfo := do
  let root ← parseBody body
  if !root.isDav "lockinfo" then throw "the body is not DAV:lockinfo"
  let scope ← match root.child? "lockscope" with
    | some s =>
      if (s.child? "exclusive").isSome then pure true
      else if (s.child? "shared").isSome then pure false
      else throw "DAV:lockscope is exclusive or shared"
    | none => throw "DAV:lockinfo has no lockscope"
  match root.child? "locktype" with
  | some t => if (t.child? "write").isNone then throw "the only lock type is DAV:write"
  | none => throw "DAV:lockinfo has no locktype"
  pure { exclusive := scope, owner := (root.child? "owner").map El.deadValue }

/-! ## Tests -/

private def en (ns local_ : String) : ExpandedName := { namespace_ := some ns, localPart := local_ }

#guard (match propfindOf "" with | .ok (.allprop []) => true | _ => false)
#guard (match propfindOf "<?xml version=\"1.0\"?><D:propfind xmlns:D=\"DAV:\"><D:propname/></D:propfind>" with
        | .ok .propname => true | _ => false)
#guard (match propfindOf "<propfind xmlns=\"DAV:\"><prop><getetag/><x:foo xmlns:x=\"http://e/\"/></prop></propfind>" with
        | .ok (.prop ns) => ns == [en "DAV:" "getetag", en "http://e/" "foo"] | _ => false)
-- A prefix bound to DAV: other than D is the same name.
#guard (match propfindOf "<z:propfind xmlns:z=\"DAV:\"><z:allprop/></z:propfind>" with
        | .ok (.allprop []) => true | _ => false)
-- Not well-formed, and an undeclared prefix: refused.
#guard (propfindOf "<D:propfind xmlns:D=\"DAV:\"><D:prop>").toOption.isNone
#guard (propfindOf "<D:propfind xmlns:D=\"DAV:\"><X:prop/></D:propfind>").toOption.isNone
#guard (propfindOf "<D:propfind xmlns:D=\"DAV:\"/>").toOption.isNone

-- A value whose content uses a prefix declared on the root keeps it.
private def pp : String :=
  "<D:propertyupdate xmlns:D=\"DAV:\" xmlns:Z=\"http://z/\"><D:set><D:prop>" ++
  "<Z:p1><Z:inner>v</Z:inner></Z:p1></D:prop></D:set>" ++
  "<D:remove><D:prop><Z:p2/></D:prop></D:remove></D:propertyupdate>"

#guard (match proppatchOf pp with
        | .ok [(n1, some v), (n2, none)] =>
            n1 == en "http://z/" "p1" && n2 == en "http://z/" "p2" &&
            v.node.serialize == "<Z:p1 xmlns:D=\"DAV:\" xmlns:Z=\"http://z/\"><Z:inner>v</Z:inner></Z:p1>"
        | _ => false)
#guard (match lockinfoOf "<D:lockinfo xmlns:D=\"DAV:\"><D:lockscope><D:shared/></D:lockscope><D:locktype><D:write/></D:locktype><D:owner>me</D:owner></D:lockinfo>" with
        | .ok li => !li.exclusive && li.owner.isSome | _ => false)
#guard (lockinfoOf "<D:lockinfo xmlns:D=\"DAV:\"><D:locktype><D:write/></D:locktype></D:lockinfo>").toOption.isNone
#guard (nameNode (en "http://e/" "foo")).serialize == "<R:foo xmlns:R=\"http://e/\"/>"
#guard (nameNode { namespace_ := none, localPart := "bar" }).serialize == "<bar xmlns=\"\"/>"
#guard multistatus [statusResponse "/m/" 404] ==
  "<?xml version=\"1.0\" encoding=\"utf-8\"?>\n<D:multistatus xmlns:D=\"DAV:\">\n" ++
  "<D:response><D:href>/m/</D:href><D:status>HTTP/1.1 404 Not Found</D:status></D:response>\n" ++
  "</D:multistatus>\n"

/-- The names a PROPPATCH reads are the names of the elements it holds: a
remove instruction keeps no value. -/
theorem proppatch_remove_none (n : ExpandedName) : ((n, none) : PatchOp).2 = none := rfl

end L4Factoidal.WebDAV
