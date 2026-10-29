import L4Factoidal.XML.Validity
import L4Factoidal.XProc31.Core
import L4Factoidal.XProc31.MediaTypes
import L4Factoidal.XML.Encoding
import L4Factoidal.XML.Namespaces
import L4Factoidal.XPath4.Html
import L4Factoidal.XPath4.BaseUri
import L4Factoidal.XPath4.Uri

namespace L4Factoidal.XProc31

/-- Decode text with existing codecs. An explicit charset controls interpretation;
a byte-order mark is stripped only when compatible with that charset. Text
content is not restricted to the XML character repertoire (bom-014/015). -/
def decodeDocumentText (bytes : ByteArray) (charset : Option String) : Result String := do
  if let some name := charset then
    if !XPath4.supportedEncodings.contains name.toUpper then
      return ← error "XD0060" ("unsupported character encoding " ++ name)
  let charset := charset.map (fun name => if name.toUpper == "UTF8" then "UTF-8" else name)
  let (encoding, offset) := XPath4.inferEncoding bytes charset
  let body := bytes.extract offset bytes.size
  let invalid {α} : Result α := error "XD0011" ("invalid byte sequence for " ++ encoding)
  match encoding.toUpper with
  | "UTF-8" | "UTF8" => (XML.decodeUtf8 body).mapError (fun _ => ⟨"XD0011", "invalid UTF-8 text", false, [], none⟩)
  | "UTF-16LE" => match XPath4.decodeUtf16 bytes offset false with | some s => pure s | none => invalid
  | "UTF-16BE" | "UTF-16" => match XPath4.decodeUtf16 bytes offset true with | some s => pure s | none => invalid
  | "US-ASCII" | "ASCII" => (XML.decodeAscii body).mapError (fun _ => ⟨"XD0011", "invalid ASCII text", false, [], none⟩)
  | "ISO-8859-1" | "LATIN1" => pure (XML.decodeLatin1 body)
  | name => error "XD0060" ("unsupported character encoding " ++ name)

def documentFilePath (uri : String) : Result String := do
  if uri.startsWith "http:" || uri.startsWith "https:" then unsupported "network document loading"
  else if uri.contains '#' then error "XD0011" "document URI contains a fragment identifier"
  else if XPath4.uriHasScheme uri && !uri.startsWith "file:" then unsupported "non-file document URI"
  else
    let raw := if uri.startsWith "file://localhost/" then (uri.drop 16).toString
      else if uri.startsWith "file://" then (uri.drop 7).toString
      else if uri.startsWith "file:" then (uri.drop 5).toString else uri
    if uri.startsWith "file://" && !raw.startsWith "/" then unsupported "remote file authority"
    else pure (XPath4.uriDecode false raw)

def loadDocumentBytes (uri : String) : IO (Result ByteArray) := do
  let path ← match documentFilePath uri with | .error e => return .error e | .ok p => pure p
  try return .ok (← IO.FS.readBinFile path)
  catch e => return error "XD0011" (toString e)

/-- Reuse the XML parser's Name and ExternalID productions to discover file
resources. Internal entity literals and comments are not interpreted as
external declarations. Unparsed NDATA entities are not fetched. -/
def externalIdAt (chars : XML.Chars) (position : Nat) : Option (String × Nat) := do
  let entity := XML.peekLit "<!ENTITY" chars position
  let doctype := XML.peekLit "<!DOCTYPE" chars position
  if !entity && !doctype then none else do
    let start := XML.skipSpace chars (position + if entity then 8 else 9)
    let start := if entity && XML.charAt chars start == '%' then XML.skipSpace chars (start+1) else start
    match XML.parseName chars start with
    | .err _ _ => none
    | .ok _ afterName =>
      match XML.parseExternalIDSys chars (XML.skipSpace chars afterName) with
      | .err _ _ => none
      | .ok systemId afterId =>
        if entity && XML.peekLit "NDATA" chars (XML.skipSpace chars afterId) then none
        else some (systemId, afterId)

def externalIds (source : String) : List String := Id.run do
  let chars := source.toList.toArray
  let mut result : List String := []
  let mut position := 0
  for _ in [:chars.size] do
    if position >= chars.size then break
    if XML.peekLit "<!--" chars position then
      match XML.parseComment .v10 chars position with
      | .ok _ next => position := next; continue
      | .err _ _ => pure ()
    match externalIdAt chars position with
    | some (identifier, next) =>
      if !result.contains identifier then result := identifier :: result
      position := next
    | none =>
      let c := XML.charAt chars position
      if c == '\'' || c == '"' then
        match XML.parseSystemLiteral chars position with
        | .ok _ next => position := next
        | .err _ _ => position := position + 1
      else position := position + 1
  return result.reverse

structure DocumentResource where
  systemId : String
  uri : String
  text : String

/-- The XML Resolver API receives a system identifier without a context URI.
Preloading resolves each declaration against its own resource URI; conflicting
uses of one lexical identifier are refused instead of reading the wrong file. -/
def preloadDocumentResources : Nat → List (String × String) → List DocumentResource → IO (Result (List DocumentResource))
  | 0, _, _ => pure (unsupported "external XML resource depth limit")
  | _+1, [], resources => pure (.ok resources)
  | fuel+1, (base,source)::pending, resources => do
    let mut resources := resources
    let mut pending := pending
    for systemId in externalIds source do
      let uri := XPath4.resolveRef base systemId
      if let some prior := resources.find? (·.systemId == systemId) then
        if prior.uri != uri then return unsupported "external XML system identifier has multiple base URI contexts"
        continue
      let bytes ← match ← loadDocumentBytes uri with | .error e => return .error e | .ok b => pure b
      let text ← match XML.decodeXmlBytes bytes with
        | .error e => return error "XD0011" ("external XML resource: " ++ e)
        | .ok s => pure s
      resources := {systemId, uri, text} :: resources
      pending := pending ++ [(uri,text)]
    preloadDocumentResources fuel pending resources

def parsedXmlDocument (uri contentType : String) (text : String) (validateDtd : Bool := false) : IO (Result Document) := do
  let resources ← match ← preloadDocumentResources 256 [(uri,text)] [] with
    | .error e => return .error e
    | .ok r => pure r
  let resolve : XML.Resolver := fun identifier => (resources.find? (·.systemId == identifier)).map (·.text)
  match XML.parseDecodedXMLWith resolve text with
  | .error e => return error "XD0011" (toString e)
  | .ok parsed =>
    if validateDtd && !(XML.validate parsed).isEmpty then return error "XD0023" "DTD validation failed"
    if !XML.isNamespaceWellFormed ((parsed.decl.map (·.version)).getD "1.0") parsed.root then
      return error "XD0011" "document is not namespace-well-formed"
    if parsed.doctype.any (·.incomplete) then return unsupported "external XML declarations require unresolved parameter entity expansion"
    let node := match parsed.children with | [n] => n | ns => XML.Node.element "#document" [] ns
    return .ok {node, contentType, baseUri := uri}

def inferredDocumentType (uri : String) : String :=
  let path := uri.toLower
  if path.endsWith ".txt" || path.endsWith ".text" || path.endsWith ".csv" || path.endsWith ".xq" || path.endsWith ".xquery" then "text/plain"
  else if path.endsWith ".json" then "application/json"
  else if path.endsWith ".html" || path.endsWith ".htm" then "text/html"
  else if path.endsWith ".xhtml" then "application/xhtml+xml"
  else if path.endsWith ".svg" then "image/svg+xml"
  else if [".zip", ".gz", ".png", ".jpg", ".jpeg", ".gif", ".pdf", ".bin"].any (fun ext => path.endsWith ext) then "application/octet-stream"
  else "application/xml"

/-- Shared local loader for p:document and p:load. It retains parsed JSON as
XDM, uses the HTML parser for text/html, and keeps XML document fragments. -/
def loadDocument (uri contentType : String) (validateDtd : Bool := false) : IO (Result Document) := do
  let contentType := if contentType == "" then inferredDocumentType uri else contentType
  let media ← match parseMediaType contentType with | .error e => return .error e | .ok m => pure m
  if media.kind == .binary then return unsupported "binary document representation"
  let bytes ← match ← loadDocumentBytes uri with | .error e => return .error e | .ok b => pure b
  let charset := media.parameters.lookup "charset"
  match media.kind with
  | .text =>
    match decodeDocumentText bytes charset with
    | .error e => return .error e
    | .ok text => return .ok {node := .text text, contentType, baseUri := uri}
  | .json =>
    let text ← match decodeDocumentText bytes charset with | .error e => return .error e | .ok t => pure t
    match XPath4.evalString "parse-json($raw)" { vars := [(⟨"","raw",""⟩, XPath4.sStr text)] } with
    | .error e => return error "XD0057" e.msg
    | .ok value => return .ok {node := .text text, contentType, baseUri := uri, value := some value}
  | .html =>
    if media.subtype == "xhtml+xml" then
      let text ← match charset with
        | some _ => match decodeDocumentText bytes charset with | .error e => return .error e | .ok t => pure t
        | none => match XML.decodeXmlBytes bytes with | .error e => return error "XD0011" e | .ok t => pure t
      return ← parsedXmlDocument uri contentType text validateDtd
    let options : XPath4.Seq := match charset with
      | none => []
      | some encoding => [.map [(XPath4.Atomic.ofStr "encoding", XPath4.sStr encoding)]]
    let env : XPath4.Env := {baseUri := uri}
    match XPath4.parseHtmlSource env options (.inr bytes) uri "xproc-load" with
    | .error e => return error "XD0011" e.msg
    | .ok nodes =>
      match seqDocuments env nodes uri with
      | .error e => return .error e
      | .ok [doc] => return .ok {doc with contentType}
      | .ok _ => return error "XD0011" "HTML parser did not return one document"
  | .xml =>
    let text ← match charset with
      | some _ => match decodeDocumentText bytes charset with | .error e => return .error e | .ok t => pure t
      | none => match XML.decodeXmlBytes bytes with | .error e => return error "XD0011" e | .ok t => pure t
    parsedXmlDocument uri contentType text validateDtd
  | .binary => return unsupported "binary document representation"

#guard (decodeDocumentText ⟨#[0xef,0xbb,0xbf,0x41]⟩ none).toOption == some "A"
#guard (decodeDocumentText ⟨#[0xff,0xfe,0x41,0]⟩ none).toOption == some "A"
#guard (decodeDocumentText ⟨#[0xfe,0xff,0,0x41]⟩ (some "utf-16")).toOption == some "A"
#guard (decodeDocumentText ⟨#[0xef,0xbb,0xbf,0x41]⟩ (some "iso-8859-1")).toOption == some "ï»¿A"
#guard (match decodeDocumentText ⟨#[0xfe,0xff,0,0x41]⟩ (some "utf-16le") with
  | .ok s => !s.startsWith "A"
  | .error _ => false)
#guard (decodeDocumentText ⟨#[0xc0,0xaf]⟩ none).toBool == false
#guard externalIds "<!DOCTYPE a [<!ENTITY e SYSTEM 'e.xml'>]><a>SYSTEM 'not-a-resource'</a>" == ["e.xml"]
#guard externalIds "<!-- <!ENTITY fake SYSTEM 'secret'> --><!DOCTYPE a SYSTEM 'd.dtd'><a/>" == ["d.dtd"]

end L4Factoidal.XProc31
