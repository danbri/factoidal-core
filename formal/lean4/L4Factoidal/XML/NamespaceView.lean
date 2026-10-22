/-
Namespace-aware view over the plain XML parser. Namespaces in XML §§3, 6:
declarations apply before resolving an element and its attributes; unprefixed
attributes have no namespace. Namespace validation remains separate from XML.

`parseNamespaceView` checks the whole document before constructing this view.
The vocabulary projection is an internal reader adapter, not serializable XML:
target elements become local names, foreign names retain a `{namespace}name`
marker, and only no-namespace attributes retain bare names. Consumers must
compare these names exactly, never strip prefixes from the projection.
-/
import L4Factoidal.XML.Namespaces

namespace L4Factoidal.XML

structure NamespaceAttribute where
  name : ExpandedName
  value : String
deriving Repr, Inhabited

inductive NamespaceNode where
  | element (name : ExpandedName) (attrs : List NamespaceAttribute)
      (children : List NamespaceNode)
  | other (raw : Node)
deriving Repr, Inhabited

mutual
/-- Resolve a tree using the same scope operations as namespace validation. -/
def namespaceView (version : String) (parent : NsScope)
    (raw : Node) : Option NamespaceNode := do
  match raw with
  | .element tag attrs children =>
    let scope ← applyDeclarations version parent attrs
    let name ← resolveElementName scope tag
    let expanded ← (attrs.filter (fun a => (expandAttrKey scope a).isSome)).mapM
      (fun a => do
        let n ← resolveAttributeName scope a.name
        pure ({ name := n, value := a.value } : NamespaceAttribute))
    let kids ← namespaceViews version scope children
    pure (.element name expanded kids)
  | other => pure (.other other)

/-- Structural traversal of the child list; every sibling inherits the same
parent scope, so declarations in one sibling cannot leak into the next. -/
def namespaceViews (version : String) (parent : NsScope) :
    List Node → Option (List NamespaceNode)
  | [] => some []
  | n :: rest => do
    let first ← namespaceView version parent n
    let remaining ← namespaceViews version parent rest
    pure (first :: remaining)
end

/-- Parse and validate namespace well-formedness, including duplicate expanded
attributes, undeclared prefixes and reserved bindings, before exposing names. -/
def parseNamespaceView (src : String) : Except String NamespaceNode := do
  let d ← (parseXML src).mapError (fun e => s!"XML: {e.message} at {e.position}")
  if !d.namespaceWellFormed then throw "XML namespace well-formedness violation"
  match namespaceView ((d.decl.map (·.version)).getD "1.0") initialScope d.root with
  | some root => pure root
  | none => throw "XML namespace resolution failed"

private def foreignName (n : ExpandedName) : String :=
  "{" ++ n.namespace_.getD "" ++ "}" ++ n.localPart

/-- Adapt resolved names for a single-vocabulary reader. Foreign elements are
preserved as foreign, including descendants and text. XML attributes retain
their fixed `xml:` spelling; other qualified attributes never become bare names.
The result is an internal view and must not be passed to an XML serializer. -/
def NamespaceNode.forVocabulary (uri : String) : NamespaceNode → Node
  | .other raw => raw
  | .element name attrs children =>
    .element (if name.namespace_ == some uri then name.localPart else foreignName name)
      (attrs.map (fun a =>
        { name := match a.name.namespace_ with
            | none => a.name.localPart
            | some ns => if ns == xmlNsUri then "xml:" ++ a.name.localPart
                         else foreignName a.name
          value := a.value }))
      (children.map (NamespaceNode.forVocabulary uri))

/-- Visible bindings, with shadowed and explicitly undeclared prefixes removed.
Order is an implementation choice; callers must not infer semantic ordering. -/
def visibleBindings (scope : NsScope) : List (String × String) :=
  ((scope.map (·.1)).eraseDups).filterMap (fun p =>
    (lookupPrefix scope p).map (fun u => (p, u)))

/-- Scope at a child-index path in a document's node list. This adapter keeps
XPath node addresses independent of namespace semantics. An empty path is the
document scope; invalid paths or declarations fail instead of losing bindings. -/
def scopeAtPath (version : String) (nodes : List Node) (path : List Nat)
    (parent : NsScope := initialScope) : Option NsScope :=
  match path with
  | [] => some parent
  | i :: rest => do
    let n ← nodes[i]?
    match n with
    | .element _ attrs children =>
      let scope ← applyDeclarations version parent attrs
      -- Preserve declaration order for clients that enumerate namespace nodes:
      -- inherited bindings first, local declarations last, replacing shadows.
      let declared := attrs.filterMap (fun a => match splitQName a.name with
        | .simple "xmlns" => some ""
        | .prefixed "xmlns" p => some p
        | _ => none)
      let order := (parent.map (·.1)).filter (fun p => !declared.contains p) ++ declared
      let ordered := order.map (fun p => (p, lookupPrefix scope p))
      scopeAtPath version children rest ordered
    | _ => if rest.isEmpty then some parent else none

end L4Factoidal.XML
