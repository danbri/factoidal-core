import L4Factoidal.XSLT.Transform
import L4Factoidal.XSLT4.Transform

/-! XML pages that name an XSLT stylesheet.

W3C "Associating Style Sheets with XML documents": a prolog processing
instruction `<?xml-stylesheet type="text/xsl" href="..."?>` names the stylesheet.
Lean finds the instruction, chooses the engine from the stylesheet's `version`,
runs it, and gives the result text to the normal HTML path. The host only fetches
the bytes. No stylesheet can read a file: neither engine receives any other
document, so `document()`, `xsl:import` and `xsl:include` stop with a refusal. -/
namespace WebXslt
open L4Factoidal

private def xsltTypes := ["text/xsl","text/xslt","application/xslt+xml","application/xml","text/xml"]
private def voidTags := ["area","base","br","col","embed","hr","img","input","link","meta","param","source","track","wbr"]

/-- Pseudo-attributes of a processing instruction: `name="value"` or `name='value'`. -/
def pseudoAttrs (data : String) : List (String × String) := Id.run do
  let mut out : List (String × String) := []
  let mut name := ""
  let mut value := ""
  let mut quote : Option Char := none
  for c in data.toList do
    match quote with
    | some q =>
      if c == q then
        out := (name,value)::out
        name := ""
        value := ""
        quote := none
      else value := value.push c
    | none =>
      if c == '"' || c == '\'' then quote := some c
      else if c != '=' && !c.isWhitespace then name := name.push c
  return out.reverse

private def field (attrs : List (String × String)) (key : String) : Option String :=
  (attrs.find? (·.1 == key)).map (·.2)

/-- The stylesheet this page names. `none` for any page that is not XML with an
    `xml-stylesheet` instruction in its prolog. An HTML page is never refused
    here, even when its text holds the words of the instruction. -/
def stylesheetHref (source : String) : Except String (Option String) := do
  if (source.splitOn "<?xml-stylesheet").length < 2 then return none
  let text := source.trimAscii.toString
  let text := if text.startsWith "\uFEFF" then (text.drop 1).toString else text
  let declared := text.startsWith "<?xml"
  if !declared && !text.startsWith "<!--" then return none
  let document ← match XML.parseXML text with
    | .ok document => pure document
    | .error e =>
      if declared then throw s!"XML page: {e.message} at {e.position}" else return none
  let found := document.prolog.filterMap fun node => match node with
    | .pi "xml-stylesheet" data => some (pseudoAttrs data)
    | _ => none
  if found.isEmpty then return none
  let active := found.filter fun attrs => (field attrs "alternate").getD "no" != "yes"
  let some attrs := active.find? (fun attrs => xsltTypes.contains ((field attrs "type").getD "").toLower)
    | throw s!"xml-stylesheet type unsupported: {((active.head?.bind (field · "type")).getD "none")}"
  let some href := field attrs "href" | throw "xml-stylesheet has no href"
  if href.isEmpty || href.startsWith "#" then throw "embedded xml-stylesheet unsupported"
  return some href

/-- The HTML parser reads `<div/>` as an open tag, and `<title/>` would take the
    rest of the page as its text. Write each empty non-void element in full. -/
def expandEmptyTags (text : String) : String := Id.run do
  let mut out : Array Char := #[]
  let mut tag : Array Char := #[]
  let mut state := 0 -- 0 text, 1 tag name, 2 in tag, 3 comment or instruction
  let mut quote : Option Char := none
  for c in text.toList do
    if state == 3 then
      out := out.push c
      if c == '>' && (out.size < 3 || (out[out.size-2]! == '-' && out[out.size-3]! == '-') || out[out.size-2]! == '?') then state := 0
    else if state == 0 then
      out := out.push c
      if c == '<' then
        tag := #[]
        state := 1
    else if let some q := quote then
      out := out.push c
      if c == q then quote := none
    else if c == '"' || c == '\'' then
      out := out.push c
      quote := some c
    else if state == 1 && (c == '!' || c == '?') && tag.isEmpty then
      out := out.push c
      state := 3
    else if c == '>' then
      let name := String.ofList tag.toList
      if out.back? == some '/' && !voidTags.contains name.toLower then
        out := out.pop ++ (">" ++ "</" ++ name ++ ">").toList.toArray
      else out := out.push c
      state := 0
    else
      out := out.push c
      if state == 1 then
        if c.isWhitespace || c == '/' then state := 2 else tag := tag.push c
  return String.ofList out.toList

private def escapeText (s : String) : String :=
  (s.replace "&" "&amp;").replace "<" "&lt;"

private def stylesheetRoot (style : String) : Except String XML.Node := do
  match XML.parseXML style with
  | .ok document => pure document.root
  | .error e => throw s!"XSLT stylesheet: {e.message} at {e.position}"

private def outputMethod (root : XML.Node) : String :=
  let output := root.allChildElements.find? fun child =>
    match child.elementTag with
    | some tag => tag == "output" || tag.endsWith ":output"
    | none => false
  (output.bind (XSLT.attrOf · "method")).getD ""

/-- Serialized principal result of XSLT 2.0, 3.0 or 4.0. -/
private def runXslt4 (style source url styleUrl : String) : Except String String := do
  let sheet ← match XSLT4.compileStylesheet styleUrl [(styleUrl,style)] with
    | .ok sheet => pure sheet
    | .error e => throw s!"XSLT compile {e.code}: {e.msg}"
  let document ← match XPath4.Doc.ofString source url with
    | .ok document => pure document
    | .error e => throw s!"XML page: {e}"
  let env : XPath4.Env := {docs:=#[document]}
  let result ← match XSLT4.transform sheet {globalCtx:=some (.node (XPath4.NodeRef.mk' 0 0)),env} with
    | .ok result => pure result
    | .error e => throw s!"XSLT run {e.code}: {e.msg}"
  let value : XPath4.M XPath4.Seq := match result.raw with
    | [.node n] => if (env.nrec n).kind == .document then pure result.raw
        else do pure [← XSLT4.materialize env (2 ^ 45) (.doc (XSLT4.Out.ofSeq result.raw) "")]
    | _ => do pure [← XSLT4.materialize env (2 ^ 45) (.doc (XSLT4.Out.ofSeq result.raw) "")]
  match value >>= XSLT4.serializeResult sheet env [("omit-xml-declaration","yes")] with
  | .ok text => pure text
  | .error e => throw s!"XSLT serialize {e.code}: {e.msg}"

/-- Run the stylesheet. The result is markup for the HTML path, and the name of
    the engine. `version` chooses the engine, as XSLT 4.0 §3.9 reads it. -/
def transform (source style url styleUrl : String) : Except String (String × String) := do
  let root ← stylesheetRoot style
  let some version := (XSLT.attrOf root "version").orElse (fun _ => XSLT.attrOf root "xsl:version")
    | throw "XSLT stylesheet has no version"
  let method := outputMethod root
  let (text,engine) ← if version.startsWith "1." then do
      let document ← match XML.parseXML source with
        | .ok document => pure document
        | .error e => throw s!"XML page: {e.message} at {e.position}"
      let sheet ← match XML.parseXML style with
        | .ok document => pure document
        | .error e => throw s!"XSLT stylesheet: {e.message} at {e.position}"
      match XSLT.transform sheet document with
      | .produced text => pure (text,"xslt-1.0")
      | .refused reason => throw s!"XSLT 1.0 refused: {reason}"
    else if ["2.0","3.0","4.0"].contains version then
      pure (← runXslt4 style source url styleUrl,s!"xslt-4 (version {version})")
    else throw s!"unsupported XSLT version: {version}"
  -- The XSLT 1.0 serializer escapes text for every output method.
  if method == "text" then
    return (s!"<!doctype html><pre>{if engine == "xslt-1.0" then text else escapeText text}</pre>",engine)
  if method == "html" && engine != "xslt-1.0" then return (text,engine)
  return (expandEmptyTags text,engine)

end WebXslt
