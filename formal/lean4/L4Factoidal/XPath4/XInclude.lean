/-
L4Factoidal.XPath4.XInclude — XML Inclusions (XInclude) 1.1 for the
`xinclude` option of `fn:doc` and `fn:parse-xml` (F&O 4.0 §14.6.1).

https://www.w3.org/TR/xinclude-11/ . An `xi:include` element (namespace
`http://www.w3.org/2001/XInclude`) is replaced by the resource its `href`
names, resolved against the base URI of the including document:

* `parse="xml"` (the default): the document element of the parsed
  resource, after its own inclusions, with base URI fixup (an `xml:base`
  attribute, §4.7.5) and, when the including element has a default
  namespace, `xmlns=""` so that the included names keep their namespace;
* `parse="text"`: a text node with the resource text.

A resource that cannot be read (or an `xpointer`, which this
implementation does not evaluate) is a resource error: the children of the
`xi:fallback` child are used, and without a fallback the error stays.
Including a resource that is already being included (a loop) is a fatal
error. The nesting is bounded by `fuel`.

The functions are pure: the caller gives the resource lookup (`fetch`)
and the XML parser (`parseRoot`).
-/
import L4Factoidal.XML.Document
import L4Factoidal.XML.Parser

namespace L4Factoidal.XPath4.XInclude

open L4Factoidal.XML

def xiNs : String := "http://www.w3.org/2001/XInclude"

inductive XiErr where
  /-- A resource error (XInclude 1.1 §4.4): the fallback applies. -/
  | resource (msg : String)
  /-- A fatal error. -/
  | fatal (msg : String)

def XiErr.msg : XiErr → String
  | .resource m => m
  | .fatal m => m

/-- The namespace bindings an element adds to the scope (newest first). -/
def scopeOf (sc : List (String × String)) (attrs : List Attribute) : List (String × String) :=
  attrs.foldl (fun sc a =>
    if a.name == "xmlns" then ("", a.value) :: sc
    else if a.name.startsWith "xmlns:" then ((a.name.drop 6).toString, a.value) :: sc
    else sc) sc

/-- The namespace URI and local name of an element name in a scope. -/
def nameOf (sc : List (String × String)) (tag : String) : String × String :=
  match tag.splitOn ":" with
  | [p, l] => ((sc.lookup p).getD "", l)
  | _ => ((sc.lookup "").getD "", tag)

def attrOf (attrs : List Attribute) (n : String) : Option String :=
  (attrs.find? (·.name == n)).map (·.value)

/-- A reference against the URI of the resource that holds it (its
    directory). -/
def resolveAgainst (base h : String) : String :=
  if base == "" || (h.splitOn "://").length > 1 || h.startsWith "/" then h
  else match (base.splitOn "/").dropLast with
    | [] => h
    | dirs => String.intercalate "/" dirs ++ "/" ++ h

/-- Base URI fixup and namespace fixup of an included element. -/
def fixup (href : String) (sc : List (String × String)) : Node → Node
  | .element tag attrs kids =>
    let attrs := if (attrOf attrs "xml:base").isSome then attrs
      else attrs ++ [{ name := "xml:base", value := href }]
    let attrs := if (sc.lookup "").getD "" != "" && (attrOf attrs "xmlns").isNone
      then attrs ++ [{ name := "xmlns", value := "" }] else attrs
    .element tag attrs kids
  | n => n

/-- Process the inclusions of a node: the nodes that replace it. `chain`
    holds the resources being included (for loop detection), `base` is the
    URI of the resource that holds the node, `sc` its namespace scope. -/
def expand (fetch : String → Option String) (parseRoot : String → Except String Node) :
    Nat → List String → String → List (String × String) → Node → Except XiErr (List Node)
  | 0, _, _, _, _ => .error (.fatal "XInclude nesting too deep")
  | f + 1, chain, base, sc, n =>
    match n with
    | .element tag attrs kids =>
      let sc := scopeOf sc attrs
      let (u, l) := nameOf sc tag
      if u == xiNs && l == "include" then
        let href := (attrOf attrs "href").getD ""
        let parse := (attrOf attrs "parse").getD "xml"
        let target := resolveAgainst base href
        let got : Except XiErr (List Node) :=
          if parse != "xml" && parse != "text" then .error (.fatal ("parse=\"" ++ parse ++ "\""))
          else if (attrOf attrs "xpointer").isSome then .error (.resource "xpointer is not evaluated")
          else if href == "" then .error (.fatal "an include without href")
          else if parse == "xml" && chain.contains target then .error (.fatal ("inclusion loop: " ++ target))
          else match fetch target with
            | none => .error (.resource ("cannot read " ++ target))
            | some t =>
              if parse == "text" then .ok [.text t]
              else match parseRoot t with
                | .error m => .error (.fatal (target ++ ": " ++ m))
                | .ok root => (expand fetch parseRoot f (target :: chain) target [] root).map
                    (·.map (fixup href sc))
        match got with
        | .error (.resource m) =>
          let fb := kids.find? (fun k => match k with
            | .element t _ _ => nameOf sc t == (xiNs, "fallback")
            | _ => false)
          match fb with
          | some (.element _ _ fkids) => do
            let parts ← fkids.mapM (expand fetch parseRoot f chain base sc)
            pure parts.flatten
          | _ => .error (.resource m)
        | r => r
      else if u == xiNs && l == "fallback" then
        .error (.fatal "xi:fallback is not a child of xi:include")
      else do
        let parts ← kids.mapM (expand fetch parseRoot f chain base sc)
        pure [.element tag attrs parts.flatten]
    | other => .ok [other]

/-! ## Checks -/

/-- The text of the nodes that replace the root of `src`, under a
    resource table (`#guard` helper). -/
def runText (res : List (String × String)) (src : String) : String :=
  let parseRoot (t : String) : Except String Node := match parseXML t with
    | .ok d => .ok d.root
    | .error _ => .error "not well-formed"
  match parseXML src with
  | .error _ => "not well-formed"
  | .ok d => match expand (res.lookup ·) parseRoot 16 ["main.xml"] "main.xml" [] d.root with
    | .ok ns =>
      let rec txt : Nat → Node → String
        | 0, _ => ""
        | f + 1, .element t as ks => "<" ++ t ++ String.join (as.map (fun a => " " ++ a.name ++ "=" ++ a.value)) ++ ">" ++
            String.join (ks.map (txt f)) ++ "</" ++ t ++ ">"
        | _, .text s => s
        | _, _ => ""
      String.join (ns.map (txt 50))
    | .error (.resource m) => "resource error: " ++ m
    | .error (.fatal m) => "fatal error: " ++ m

-- parse="xml": the included element, with base URI fixup
#guard runText [("dir/b.xml", "<b>x</b>")]
  "<a xmlns:xi='http://www.w3.org/2001/XInclude'><xi:include href='dir/b.xml'/></a>" ==
  "<a xmlns:xi=http://www.w3.org/2001/XInclude><b xml:base=dir/b.xml>x</b></a>"
-- parse="text"
#guard runText [("t.txt", "1 < 2")]
  "<a xmlns:xi='http://www.w3.org/2001/XInclude'><xi:include href='t.txt' parse='text'/></a>" ==
  "<a xmlns:xi=http://www.w3.org/2001/XInclude>1 < 2</a>"
-- a resource error uses the fallback
#guard runText []
  "<a xmlns:xi='http://www.w3.org/2001/XInclude'><xi:include href='none.xml'><xi:fallback>f</xi:fallback></xi:include></a>" ==
  "<a xmlns:xi=http://www.w3.org/2001/XInclude>f</a>"
-- a resource error without a fallback
#guard runText []
  "<a xmlns:xi='http://www.w3.org/2001/XInclude'><xi:include href='none.xml'/></a>" ==
  "resource error: cannot read none.xml"
-- an inclusion loop is a fatal error
#guard runText [("main.xml", "<a xmlns:xi='http://www.w3.org/2001/XInclude'><xi:include href='main.xml'/></a>")]
  "<a xmlns:xi='http://www.w3.org/2001/XInclude'><xi:include href='main.xml'/></a>" ==
  "fatal error: inclusion loop: main.xml"
-- an element in another namespace named include is not an inclusion
#guard runText [] "<a xmlns:xi='urn:other'><xi:include href='x'/></a>" ==
  "<a xmlns:xi=urn:other><xi:include href=x></xi:include></a>"

end L4Factoidal.XPath4.XInclude
