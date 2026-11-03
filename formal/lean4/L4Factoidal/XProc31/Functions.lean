import L4Factoidal.XProc31.Core
import L4Factoidal.XPath4.BaseUri
import L4Factoidal.Fn.String

namespace L4Factoidal.XProc31
open XPath4

/-- XProc function namespace; error codes remain in the XProc error namespace. -/
def nsXProc : String := "http://www.w3.org/ns/xproc"

def functionString (values : Seq) : M String :=
  match values with
  | [] => pure ""
  | [.atom a] => pure a.str
  | [.node n] => match n.rt with
    | some d => pure (d.stringValue n.idx)
    | none => err "XPTY0004" "a string argument is required"
  | _ => err "XPTY0004" "a singleton string argument is required"

/-- Resolve lexical QNames and EQNames in the caller's static namespace
context. A prefixed name must have an in-scope binding. -/
def functionQName (c : HostCall) (values : Seq) : M QN := do
  match values with
  | [.atom a] =>
    if let .qn q := a.v then return q
  | _ => pure ()
  let name ← functionString values
  if name.startsWith "Q{" then
    match (name.drop 2).toString.splitOn "}" with
    | [u,l] =>
      if XML.isName l && !(l.contains ":") then pure ⟨u,l,""⟩
      else err "XD0015" "invalid EQName local part"
    | _ => err "XD0015" "invalid EQName"
  else
    let (p,l) := XPath4.splitName name
    if !XML.isName name || l == "" || l.contains ":" then err "XD0015" "invalid QName" else
    let uri ← if p == "xml" then pure nsXML else if p == "" then pure ((c.ns.lookup "").getD "")
      else match c.ns.lookup p with
      | some u => pure u
      | none => err "XD0015" ("unbound QName prefix " ++ p)
    pure ⟨uri,l,p⟩

/-- XProc `p:urify` on POSIX systems. File names have no drive letters;
backslashes in relative paths are ordinary characters and are percent encoded.
Absolute URIs do not need a base. Relative references require an absolute,
hierarchical base, then use the shared RFC 3986 resolver. -/
def urifyPosix (reference base : String) : M String := do
  let r := Syntax.parseIri reference
  let scheme := r.scheme.map String.toLower
  let isFile := scheme == some "file"
  let fileAbsolute := isFile && r.path.startsWith "/"
  let otherAbsolute := scheme.isSome && !isFile &&
    (r.authority.isSome || r.path.startsWith "/" ||
      (scheme.getD "").length > 1 && !["http", "https", "ftp"].contains (scheme.getD "") && r.path != "")
  if fileAbsolute then
    return Syntax.recompose { r with scheme := some "file", authority := some (r.authority.getD ""), path := Syntax.removeDotSegments r.path }
  if otherAbsolute then return reference
  let b := Syntax.parseIri base
  let bs := b.scheme.map String.toLower
  if bs.isNone || (bs == some "file" && !b.path.startsWith "/") then
    err "XD0074" "urify requires an absolute base URI"
  else if !b.path.startsWith "/" && b.authority.isNone then
    err "XD0080" "urify cannot resolve against an opaque base URI"
  else if scheme.isSome && scheme != bs then
    err "XD0077" "relative URI scheme differs from base URI scheme"
  else
    let r := if scheme.isSome then { r with scheme := none } else r
    -- A leading run of at least three slashes is an absolute path, not
    -- an empty replacement authority. An explicit file URI differs.
    let r := if scheme.isNone && reference.startsWith "///" then
      { r with authority := none, path := "/" ++ String.ofList (r.path.toList.dropWhile (· == '/')) }
      else r
    let result := Syntax.recompose (Syntax.transformReferences { b with scheme := bs } r)
    pure (if scheme.isNone then Fn.String.iriToUri result else result)

def systemProperty (episode : String) (q : QN) : String :=
  if q.uri != nsXProc then "" else
  match q.loc with
  | "episode" => episode
  | "locale" => "en"
  | "product-name" => "Factoidal XProc"
  | "product-version" => "0.1"
  | "vendor" => "Factoidal"
  | "vendor-uri" => "https://github.com/danbri/factoidal-core"
  | "version" => "3.0 3.1"
  | "xpath-version" => "3.1 4.0"
  | "psvi-supported" => "false"
  | _ => ""

/-- Shared static/dynamic host functions. The runtime supplies the same
availability predicate it uses for dispatch, extended by visible implemented
user declarations. An empty atomic declaration is not an implementation.
The episode parameter lets the IO host supply one identifier per execution. -/
def xprocFunction (q : QN) (arity : Nat)
    (available : QN → Bool := fun _ => false)
    (episode : String := "factoidal-xproc") : Option HostFn :=
  if q.uri != nsXProc then none else
  match q.loc, arity with
  | "urify", 1 | "urify", 2 => some fun c args => do
      let reference ← functionString (args.getD 0 [])
      let base ← if arity == 2 then functionString (args.getD 1 []) else pure c.baseUri
      pure [.atom (Atomic.ofUri (← urifyPosix reference base))]
  | "system-property", 1 => some fun c args => do
      pure (sStr (systemProperty episode (← functionQName c (args.getD 0 []))))
  | "step-available", 1 => some fun c args => do
      pure (sBool (available (← functionQName c (args.getD 0 []))))
  | _, _ => none

#guard (urifyPosix "../space here/thing" "file:///work/sub/").toOption == some "file:///work/space%20here/thing"
#guard (urifyPosix "///a" "https://example.org/base/").toOption == some "https://example.org/a"
#guard (urifyPosix "file:/a/../b" "urn:opaque").toOption == some "file:///b"
#guard (urifyPosix "\\a\\b" "file:///work/").toOption == some "file:///work/%5Ca%5Cb"
#guard (urifyPosix "?föö=bär#ß" "https://example.org/").toOption == some "https://example.org/?f%C3%B6%C3%B6=b%C3%A4r#%C3%9F"
#guard (urifyPosix "file:" "file:///work/").toOption == some "file:///work/"
#guard (urifyPosix "file:relative" "https://example.org/").toBool == false
#guard (urifyPosix "relative" "urn:opaque").toBool == false
#guard (functionQName {ns := [("p", nsXProc)]} (sStr "p:identity")).toOption.map (·.eqn) == some ("Q{" ++ nsXProc ++ "}identity")
#guard (functionQName {} (sStr "unbound:name")).toBool == false
#guard (functionQName {} (sStr "Q{urn:test}a")).toOption.map (·.uri) == some "urn:test"
#guard systemProperty "execution-1" ⟨nsXProc, "episode", "p"⟩ == "execution-1"

end L4Factoidal.XProc31
