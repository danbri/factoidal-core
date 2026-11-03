import L4Factoidal.XML.NamespaceView
import Std.Data.TreeMap
import L4Factoidal.Syntax.IriResolve

/- Same-document SVG references. IDs select the first element in original tree
   order; source paths identify nodes independently of possibly duplicate IDs. -/
namespace NativeSVGReferences
open L4Factoidal.XML
structure Entry where
  node : NamespaceNode
  path : List Nat
  parentBase : Option String
  deriving Repr
structure Index where
  targets : Std.TreeMap String Entry
  documentURL : Option String

def Index.get? (index : Index) (id : String) : Option Entry := index.targets.get? id
private def attr (attrs : List NamespaceAttribute) (key : String) : Option String :=
  (attrs.find? (fun a => a.name.namespace_.isNone && a.name.localPart == key)).map (·.value)

/-- Resolve xml:base in the original source element's context. Shadow instances
    preserve this context instead of rebasing references against the use host. -/
def elementBase (attrs : List NamespaceAttribute) (parent : Option String) : Option String :=
  match attrs.find? (fun a => a.name.namespace_ == some "http://www.w3.org/XML/1998/namespace" && a.name.localPart == "base") with
  | none => parent
  | some baseAttr => some (L4Factoidal.Syntax.resolveAgainst? parent baseAttr.value)

def collect (root : NamespaceNode) (maxNodes : Nat) (documentURL : Option String := none)
    (initialBaseURL : Option String := none) : Except String Index := do
  let mut pending := [(root,([] : List Nat),initialBaseURL.orElse (fun _ => documentURL))]
  let mut out : Std.TreeMap String Entry := {}
  for _ in [:maxNodes] do
    match pending with
    | [] => return ⟨out,documentURL⟩
    | (node,path,parentBase)::rest =>
      if path.length > 32 then throw "SVG identifier nesting exceeds 32"
      pending := rest
      match node with
      | .other _ => pure ()
      | .element _ attrs children =>
        if let some id := attr attrs "id" then
          if !out.contains id then out := out.insert id ⟨node,path,parentBase⟩
        let base := elementBase attrs parentBase
        pending := (children.zipIdx.map fun (child,i) => (child,path ++ [i],base)) ++ pending
  if pending.isEmpty then return ⟨out,documentURL⟩
  throw "SVG identifier node count exceeds input bound"

private def locateAux (node : NamespaceNode) (here : List Nat) (parentBase : Option String) :
    List Nat → Except String Entry
  | [] => .ok ⟨node,here,parentBase⟩
  | index::rest =>
    match node with
    | .other _ => .error "SVG root source path enters a non-element"
    | .element _ attrs children =>
      match children[index]? with
      | none => .error "SVG root source path is outside the original document"
      | some child => locateAux child (here ++ [index]) (elementBase attrs parentBase) rest

private theorem locateAux_path (node : NamespaceNode) (here : List Nat)
    (parentBase : Option String) (path : List Nat) (entry : Entry)
    (found : locateAux node here parentBase path = .ok entry) : entry.path = here ++ path := by
  induction path generalizing node here parentBase with
  | nil => simp only [locateAux,Except.ok.injEq] at found; cases found; simp
  | cons index rest ih =>
    cases node with
    | other raw => simp [locateAux] at found
    | element name attrs children =>
      simp only [locateAux] at found
      split at found
      · contradiction
      · rename_i child selected
        simpa [List.append_assoc] using ih child (here ++ [index]) (elementBase attrs parentBase) found

/-- Select the root from the same original DOM used by the ID index. Child
    positions include text/comments; a caller cannot substitute another root. -/
def locate (document : NamespaceNode) (path : List Nat)
    (initialBaseURL : Option String := none) : Except String Entry :=
  if path.length > 32 then .error "SVG root source path nesting exceeds 32"
  else locateAux document [] initialBaseURL path

theorem locate_path (document : NamespaceNode) (path : List Nat)
    (initialBaseURL : Option String) (entry : Entry)
    (found : locate document path initialBaseURL = .ok entry) : entry.path = path := by
  simp only [locate] at found
  split at found
  · contradiction
  · simpa using locateAux_path document [] initialBaseURL path entry found

#print axioms locate_path

/-- Prefer SVG2 href even when empty; deprecated xlink is fallback only. -/
def href (attrs : List NamespaceAttribute) : Option String :=
  (attr attrs "href").orElse fun _ =>
    (attrs.find? (fun a => a.name.namespace_ == some "http://www.w3.org/1999/xlink" &&
      a.name.localPart == "href")).map (·.value)
private def hex (byte : UInt8) : Option UInt8 :=
  if 48 <= byte && byte <= 57 then some (byte-48)
  else if 65 <= byte && byte <= 70 then some (byte-55)
  else if 97 <= byte && byte <= 102 then some (byte-87)
  else none

/-- Decode percent-escaped UTF-8 bytes once, without treating '+' as a space.
    Malformed escaping or UTF-8 is an invalid reference, not an element ID. -/
def decodeFragment (input : String) : Option String := Id.run do
  let bytes := input.toUTF8
  let mut out := ByteArray.empty
  let mut cursor := 0
  for _ in [:bytes.size] do
    if cursor < bytes.size then
      let byte := bytes[cursor]!
      if byte == 37 then
        if cursor+2 >= bytes.size then return none
        let some high := hex bytes[cursor+1]! | return none
        let some low := hex bytes[cursor+2]! | return none
        out := out.push (high*16+low)
        cursor := cursor+3
      else
        out := out.push byte
        cursor := cursor+1
  return String.fromUTF8? out

/-- RFC3986-resolution-based same-document references. No network fetching.
    Without retrieval context only fragment-only references with no changed
    xml:base are decidable here; other document URLs are explicit unsupported. -/
def fragment (value : String) (documentURL : Option String := none)
    (baseURL : Option String := none) : Except String (Option String) := do
  let value := value.trimAscii.toString
  if value.isEmpty then return none
  let source ← match documentURL with
    | none =>
      if baseURL.isSome || !value.startsWith "#" then
        throw "external/document-URL use references require host URL context"
      else pure (String.ofList (value.toList.drop 1))
    | some document => do
      let resolved := L4Factoidal.Syntax.parseIri (L4Factoidal.Syntax.resolveIri (baseURL.getD document) value)
      let retrieval := L4Factoidal.Syntax.parseIri (L4Factoidal.Syntax.resolveIri document document)
      if L4Factoidal.Syntax.recompose {resolved with fragment:=none} !=
          L4Factoidal.Syntax.recompose {retrieval with fragment:=none} then
        throw "external use reference unsupported"
      pure (resolved.fragment.getD "")
  return (decodeFragment source).filter (!·.isEmpty)
end NativeSVGReferences
