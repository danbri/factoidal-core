import L4Factoidal.XProc31.Atomic
import L4Factoidal.XProc31.BinaryDocument
import L4Factoidal.XProc31.Loading
import L4Factoidal.XProc31.Zip
import L4Factoidal.XProc31.FileSteps
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.XProc31
open XML

def supportsArchive (name : String) : Bool :=
  ["archive", "archive-manifest", "unarchive"].contains name

def archiveZipResult {α : Type} : Except Zip.Error α → Result α
  | .ok value => .ok value
  | .error (.malformed message) => error "XC0085" message
  | .error (.unsupported message) => unsupported message

def archiveFormat (step : Node) (env : XPath4.Env) : Result Unit := do
  let format ← option step "format" env "zip"
  if format == "zip" || format == "Q{}zip" then pure ()
  else if ["tar", "jar", "ar", "arj", "cpio", "7z"].contains format then
    unsupported ("archive format " ++ format)
  else error "XC0085" ("unknown archive format " ++ format)

def readArchiveDocument (doc : Document) : Result Zip.Archive := do
  let ct := ((doc.contentType.splitOn ";").headD "").trimAscii.toString
  if !["application/zip", "application/octet-stream", "application/x-zip-compressed", "application/java-archive"].contains ct then
    error "XC0081" "archive input has an incompatible content type" else pure ()
  let some bytes := binaryBytes doc | error "XC0085" "archive input has no binary data"
  archiveZipResult (Zip.read bytes)

def archiveUri (base reference : String) : Result String := do
  if !RDF.isIriReference reference then error "XD0064" "invalid archive URI reference" else pure ()
  let uri := Syntax.resolveIri base reference
  if !RDF.isAbsoluteIri uri then error "XD0064" "invalid archive URI" else pure uri

def archiveRelativeTo (step : Node) (env : XPath4.Env) : Result String := do
  let relative ← option step "relative-to" env
  if relative == "" then pure "" else
  let declaration := (named step "with-option").find? (fun n => attr n "name" == "relative-to")
  let localBase := declaration.map (fun n => attr n "xml:base") |>.getD ""
  let base ← if localBase == "" then pure env.baseUri else archiveUri env.baseUri localBase
  archiveUri base relative

def archiveBase (step : Node) (env : XPath4.Env) (doc : Document) : Result String := do
  let relative ← archiveRelativeTo step env
  let base ← if relative == "" then
      if doc.baseUri == "" then error "XC0120" "archive has no base URI and relative-to was not supplied"
      else pure doc.baseUri
    else pure relative
  pure (if base.endsWith "/" then base else base ++ "/")

def archiveMediaType (name : String) : String :=
  if name.endsWith ".jpg" || name.endsWith ".jpeg" then "image/jpeg"
  else if [".xml", ".xhtml", ".html", ".htm", ".json", ".txt", ".csv", ".svg"].any (fun suffix => name.endsWith suffix) then
    inferredDocumentType name
  else "application/octet-stream"

def archiveManifest (archive : Zip.Archive) (base : String) : Document :=
  {node := .element "c:archive" [⟨"xmlns:c", "http://www.w3.org/ns/xproc-step"⟩,
      ⟨"format", "zip"⟩] (archive.entries.filterMap fun entry =>
    if entry.isDirectory then none else some (.element "c:entry"
      ([⟨"name",entry.name⟩, ⟨"href",Syntax.resolveIri base (Fn.String.iriToUri entry.name)⟩,
        ⟨"content-type",archiveMediaType entry.name⟩,
        ⟨"size",toString entry.bytes.size⟩, ⟨"method",if entry.method == 0 then "none" else "deflated"⟩] ++
        if entry.comment == "" then [] else [⟨"comment",entry.comment⟩]) []))}

def archivePatterns (step : Node) (env : XPath4.Env) (name : String) : Result (List String) :=
  match (named step "with-option").find? (fun n => attr n "name" == name) with
  | some opt => do pure ((← eval (attr opt "select") env).map (fun item => seqString env [item]))
  | none => if attr step name == "" then pure [] else do pure [← option step name env]

def archiveMatches (env : XPath4.Env) (patterns : List String) (name : String) : Result Bool := do
  for pattern in patterns do
    if ← evalBool "matches($name,$pattern)" {env with vars :=
      [(⟨"","name",""⟩,XPath4.sStr name),(⟨"","pattern",""⟩,XPath4.sStr pattern)] ++ env.vars} then return true
  pure false

def archiveMethod (method : String) : Result Nat :=
  if method == "none" then pure 0 else if method == "deflated" then pure 8
  else error "XC0079" ("unsupported ZIP method " ++ method)

def archiveParameters (step : Node) (env : XPath4.Env) : Result (List (XPath4.Atomic × XPath4.Seq)) := do
  let [.map parameters] ← typedOption step "parameters" env "map{}"
    | error "XC0079" "archive parameters must be a map"
  pure parameters

def archiveParameter (parameters : List (XPath4.Atomic × XPath4.Seq)) (name fallback : String) : String :=
  ((parameters.find? (fun (key,_) => key.str == name)).map (fun (_,value) => seqString {} value)).getD fallback

def inferredEntryName (relative uri : String) : Result String := do
  if uri == "" then error "XC0084" "archive source document has no base URI" else pure ()
  let raw := if relative != "" && uri.startsWith relative then (uri.drop relative.length).toString
    else (Syntax.parseIri uri).path
  let name := String.ofList (raw.toList.dropWhile (· == '/'))
  if name == "" then error "XC0084" "archive source document has no usable entry name" else pure name

structure ArchiveCandidate where
  name : String
  href : String
  descriptor : Node
  source : Option Document

def archiveCandidates (sources manifests : List Document) (relative : String) (env : XPath4.Env) : Result (List ArchiveCandidate) := do
  if manifests.length > 1 then error "XC0112" "archive requires at most one manifest" else pure ()
  if sources.any (fun d => d.baseUri == "") || (sources.map (·.baseUri)).eraseDups.length != sources.length then
    error "XC0084" "archive source base URIs must be present and distinct" else pure ()
  let mut candidates : List ArchiveCandidate := []
  if let some manifest := manifests.head? then
    let node := documentElement manifest
    let cName := fun (n : Node) =>
      let (p,l) := XPath4.splitName (n.elementTag.getD "")
      if ((ns n).lookup p).getD "" == "http://www.w3.org/ns/xproc-step" then l else ""
    if cName node != "archive" then error "XC0100" "manifest root must be c:archive" else pure ()
    for entry in kids (inheritNS 4096 [] node) do
      if cName entry != "entry" || attr entry "name" == "" || attr entry "href" == "" then
        error "XC0100" "manifest entries require name and href" else pure ()
      let href ← archiveUri (if manifest.baseUri == "" then env.baseUri else manifest.baseUri) (attr entry "href")
      candidates := candidates ++ [{
        name := attr entry "name", href, descriptor := entry
        source := sources.find? (fun doc => doc.baseUri == href)}]
  for source in sources do
    if !(candidates.any (fun candidate => candidate.href == source.baseUri)) then
      candidates := candidates ++ [{
        name := ← inferredEntryName relative source.baseUri
        href := source.baseUri, descriptor := .element "c:entry" [] [], source := some source}]
  if (candidates.map (·.name)).eraseDups.length != candidates.length then
    error "XC0084" "archive entry names must be distinct" else pure candidates

def candidateEntry (candidate : ArchiveCandidate) (method : String) (env : XPath4.Env) : IO (Result Zip.Entry) := do
  let method ← match archiveMethod (attr candidate.descriptor "method" method) with
    | .ok value => pure value | .error e => return .error e
  let bytes ← match candidate.source with
    | some doc => match documentBytes doc [.map []] env with
      | .ok bytes => pure bytes | .error e => return .error e
    | none => match ← loadDocumentBytes candidate.href with
      | .ok bytes => pure bytes | .error e => return .error e
  return .ok {name := candidate.name, bytes, method, comment := attr candidate.descriptor "comment"}

/-- Primary archive bytes and a separate XML report. Existing member order is
retained by update/freshen/delete; new entries follow manifest/source order. -/
def createArchiveStep (step : Node) (ports : List (String × List Document)) (env : XPath4.Env) : IO (Result (List (String × List Document))) := do
  let opts := do
    archiveFormat step env
    let params ← archiveParameters step env
    let command := archiveParameter params "command" "update"
    if !["create","update","freshen","delete"].contains command then error "XC0079" "unknown archive command" else pure ()
    let method := archiveParameter params "method" "deflated"
    let _ ← archiveMethod method
    let level := archiveParameter params "level" "default"
    if !["default","smallest","fastest","none"].contains level then error "XC0079" "unknown archive compression level" else pure ()
    if level != "default" then unsupported "nondefault ZIP compression level" else pure ()
    let relative ← archiveRelativeTo step env
    let sources := (ports.lookup "source").getD []
    let candidates ← archiveCandidates sources ((ports.lookup "manifest").getD []) relative env
    let archives := (ports.lookup "archive").getD []
    if archives.length > 1 || (command == "delete" && archives.isEmpty) then
      error "XC0080" "archive command received an invalid number of archives" else pure ()
    let archive ← match archives with | [] => pure ({entries := []} : Zip.Archive) | doc::_ => readArchiveDocument doc
    pure (command,method,candidates,archive)
  let .ok (command,method,candidates,archive) := opts | return opts.map (fun _ => [])
  let mut entries := archive.entries
  if command == "delete" then
    entries := entries.filter (fun entry => !(candidates.any (fun candidate => candidate.name == entry.name)))
  else
    for candidate in candidates do
      let present := entries.any (fun entry => entry.name == candidate.name)
      if command == "freshen" && !present then continue
      let entry ← match ← candidateEntry candidate method env with
        | .ok entry => pure entry | .error e => return .error e
      if present then entries := entries.map (fun old => if old.name == entry.name then entry else old)
      else entries := entries ++ [entry]
  let archive := {archive with entries}
  let bytes ← match archiveZipResult (Zip.write archive) with
    | .ok bytes => pure bytes | .error e => return .error e
  return .ok [("result",[binaryDocument bytes "application/zip"]), ("report",[archiveManifest archive ""])]

def archiveStep (step : Node) (ports : List (String × List Document)) (env : XPath4.Env) : IO (Result (List (String × List Document))) := do
  if tag step == "archive" then return ← createArchiveStep step ports env
  let opts := do
    archiveFormat step env
    let [doc] := (ports.lookup "source").getD [] | error "XD0006" "archive reader requires one document"
    let archive ← readArchiveDocument doc
    let base ← archiveBase step env doc
    pure (archive,base,← fileContentOverrides step env,← archivePatterns step env "include-filter",← archivePatterns step env "exclude-filter")
  let .ok (archive,base,overrides,inclusions,exclusions) := opts | return opts.map (fun _ => [])
  if tag step == "archive-manifest" then
    let manifest := archiveManifest archive base
    let revised := (children manifest.node).mapM fun node => overrideFileContentType env overrides (attr node "name") node
    return revised.map (fun nodes => [("result",[{manifest with node := .element "c:archive" manifest.node.elementAttrs nodes}])])
  let mut docs := []
  for entry in archive.entries do
    if entry.isDirectory then continue
    let selected := do
      let included ← if inclusions.isEmpty then pure true else archiveMatches env inclusions entry.name
      let excluded ← archiveMatches env exclusions entry.name
      pure (included && !excluded)
    let .ok selected := selected | return selected.map (fun _ => [])
    if !selected then continue
    let uri := Syntax.resolveIri base (Fn.String.iriToUri entry.name)
    let contentType := do
      let node ← overrideFileContentType env overrides entry.name
        (.element "entry" [⟨"content-type",archiveMediaType entry.name⟩] [])
      pure (attr node "content-type")
    let .ok contentType := contentType | return contentType.map (fun _ => [])
    match ← documentFromBytes uri contentType entry.bytes with
    | .error e => return .error e
    | .ok doc => docs := docs ++ [doc]
  return .ok [("result",docs)]

#guard (inferredEntryName "" "https://example.org/folder/doc.xml").toOption == some "folder/doc.xml"
#guard (inferredEntryName "https://example.org/folder/" "https://example.org/folder/doc.xml").toOption == some "doc.xml"
#guard (archiveMethod "stored").toBool == false
#guard (archiveUri "file:///fixtures/test.xml" "::").toBool == false
#guard (archiveRelativeTo (.element "p:archive-manifest" [] [
  .element "p:with-option" [⟨"name","relative-to"⟩,⟨"select","'test/'"⟩,
    ⟨"xml:base","http://example.org/base/"⟩] []]) {baseUri := "file:///fixture.xml"}).toOption ==
  some "http://example.org/base/test/"

/-- Exercise actual serialized bytes and XML parsing through the public step
API, including replacement, freshen exclusion and delete preservation. -/
def archiveStepsRegression : IO Bool := do
  let makeStep : String → Node := fun command => .element "p:archive"
    [⟨"parameters", "map{'command':'" ++ command ++ "'}"⟩] []
  let source : Document := {node := .element "original" [] [], baseUri := "https://example.org/a.xml"}
  let replacement : Document := {node := .element "replacement" [] [], baseUri := source.baseUri}
  let added : Document := {node := .element "added" [] [], baseUri := "https://example.org/b.xml"}
  let made ← archiveStep (makeStep "create") [("source",[source])] {}
  let some made := made.toOption | return false
  let initial := (made.lookup "result").getD []
  let fresh ← archiveStep (makeStep "freshen") [("source",[replacement,added]),("archive",initial)] {}
  let some fresh := fresh.toOption | return false
  let freshDocs := (fresh.lookup "result").getD []
  let [freshDoc] := freshDocs | return false
  let some freshZip := (readArchiveDocument freshDoc).toOption | return false
  if freshZip.entries.length != 1 then return false
  let some replacementText := (XML.decodeXmlBytes freshZip.entries.head!.bytes).toOption | return false
  let some replacementXml := (XML.parseXML replacementText).toOption | return false
  if replacementXml.root.elementTag != some "replacement" then return false
  let updated ← archiveStep (makeStep "update") [("source",[added]),("archive",freshDocs)] {}
  let some updated := updated.toOption | return false
  let updatedDocs := (updated.lookup "result").getD []
  let deleted ← archiveStep (makeStep "delete") [("source",[source]),("archive",updatedDocs)] {}
  let some deleted := deleted.toOption | return false
  let unpacked ← archiveStep (.element "p:unarchive" [⟨"relative-to","https://example.org/unpacked/"⟩] [])
    [("source",(deleted.lookup "result").getD [])] {}
  let some unpacked := unpacked.toOption | return false
  let [doc] := (unpacked.lookup "result").getD [] | return false
  return (documentElement doc).elementTag == some "added" && doc.baseUri == "https://example.org/unpacked/b.xml"

end L4Factoidal.XProc31
