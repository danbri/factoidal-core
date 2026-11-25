import Std.Data.TreeMap
import L4Factoidal.XProc31.Zip
import L4Factoidal.XML.NamespaceView
import L4Factoidal.WHATWG.Base64
import L4Factoidal.WHATWG.URL.PercentEncode

/-! Read an unencrypted EPUB 3 publication in memory. The book exposes its manifest
and spine independently of a host. The browser reader below projects XHTML into
passive markup with internal anchors and bounded inline raster images. -/
namespace L4Factoidal.Epub

open XML

def maxArchiveBytes : Nat := 8 * 1024 * 1024
def maxExpandedBytes : Nat := 16 * 1024 * 1024
def maxMetadataBytes : Nat := 256 * 1024
def maxChapterBytes : Nat := 4 * 1024 * 1024
def maxInlineImageBytes : Nat := 2 * 1024 * 1024

private def ocf := "urn:oasis:names:tc:opendocument:xmlns:container"
private def opf := "http://www.idpf.org/2007/opf"
private def dc := "http://purl.org/dc/elements/1.1/"
private def xhtml := "http://www.w3.org/1999/xhtml"

structure Resource where
  id : String
  path : String
  mediaType : String
  bytes : ByteArray
  deriving Inhabited

structure Book where
  title : String
  manifest : Array Resource
  spine : Array Resource

private def named (ns name : String) : NamespaceNode → Bool
  | .element n _ _ => n.namespace_ == some ns && n.localPart == name
  | .other _ => false

private def children : NamespaceNode → List NamespaceNode
  | .element _ _ kids => kids
  | .other _ => []

private def child (node : NamespaceNode) (ns name : String) : Option NamespaceNode :=
  (children node).find? (named ns name)

private def attr (node : NamespaceNode) (key : String) : String :=
  match node with
  | .element _ attrs _ => ((attrs.find? fun a => a.name.namespace_.isNone && a.name.localPart == key).map (·.value)).getD ""
  | .other _ => ""

private def rawText : NamespaceNode → String
  | .other (.text s) | .other (.cdata s) => s
  | _ => ""

private def cleanSegment (part : String) : Bool :=
  !part.isEmpty && part != "." && part != ".." &&
  part.toList.all (fun c => c > '\x1f' && c != '\x7f' && c != '/' && c != '\\' && c != ':' &&
    c != '?' && c != '#')

private def safePath (path : String) : Bool :=
  !path.isEmpty && (path.splitOn "/").all cleanSegment

private def segmentStep (acc : List String) (part : String) : Option (List String) :=
  if part == "." then some acc
  else if part == ".." then match acc with
    | [] => none
    | _ :: rest => some rest
  else if cleanSegment part then some (part :: acc)
  else none

/-- Resolve an archive-relative URL. Percent decoding is performed per segment
before validation, so escaped separators cannot change the archive path. -/
def resolvePath (base href : String) : Option String := do
  if href.isEmpty || href.startsWith "/" || href.toList.any (fun c => c == '#' || c == '?' || c == '\\') then none
  else
    let dir := ((base.splitOn "/").reverse.drop 1)
    let parts ← (href.splitOn "/").foldlM (fun acc field => do
      let part ← String.fromUTF8? (WHATWG.URL.percentDecode field.toUTF8)
      segmentStep acc part) dir
    let path := String.intercalate "/" parts.reverse
    if safePath path then some path else none

private def parse (bytes : ByteArray) (limit : Nat) : Except String NamespaceNode := do
  if bytes.size > limit then throw "EPUB XML size limit exceeded"
  let some source := String.fromUTF8? bytes | throw "EPUB XML is not UTF-8"
  if ((source.replace "<!DOCTYPE html>" "").splitOn "<!DOCTYPE").length > 1 then
    throw "EPUB reader supports only the simple XHTML doctype"
  parseNamespaceView source

private def required (label value : String) : Except String String :=
  if value.isEmpty then .error ("EPUB missing " ++ label) else .ok value

/-- Pure EPUB 3 reader. The archive, aggregate expansion, number of members and
total spine bytes have independent limits. No member is written to disk. -/
def openBook (bytes : ByteArray) : Except String Book := do
  if bytes.size > maxArchiveBytes then throw "EPUB archive size limit exceeded"
  let archive ← (XProc31.Zip.read bytes maxExpandedBytes 2048).mapError toString
  let mut entries : Std.TreeMap String ByteArray := {}
  for entry in archive.entries do
    if entry.isDirectory then continue
    if !safePath entry.name then throw "EPUB has an invalid member path"
    if (entries.get? entry.name).isSome then throw "EPUB has a duplicate member"
    entries := entries.insert entry.name entry.bytes
  let file := fun (path : String) =>
    match entries.get? path with
    | some bytes => .ok bytes
    | none => .error ("EPUB missing archive member: " ++ path)
  let mime ← file "mimetype"
  if mime != "application/epub+zip".toUTF8 then throw "EPUB mimetype is incorrect"
  if (entries.get? "META-INF/encryption.xml").isSome then throw "Encrypted EPUB resources are unsupported"
  let container ← parse (← file "META-INF/container.xml") maxMetadataBytes
  if !named ocf "container" container then throw "Invalid EPUB container root"
  let some roots := child container ocf "rootfiles" | throw "EPUB container has no rootfiles"
  let some packageFile := (children roots).find? (fun n => named ocf "rootfile" n &&
      attr n "media-type" == "application/oebps-package+xml") | throw "EPUB container has no package document"
  let path ← required "package path" (attr packageFile "full-path")
  let package ← parse (← file path) maxMetadataBytes
  if !named opf "package" package || !(attr package "version").startsWith "3." then
    throw "Expected an EPUB 3 package document"
  let some manifest := child package opf "manifest" | throw "EPUB package has no manifest"
  let some spine := child package opf "spine" | throw "EPUB package has no spine"
  let titleNode := (child package opf "metadata").bind (fun n => child n dc "title")
  let title := (titleNode.map (fun n => String.join ((children n).map rawText))).getD "EPUB publication"
  let mut resources : Array Resource := #[]
  let mut byId : Std.TreeMap String Resource := {}
  for item in children manifest do
    if !named opf "item" item then continue
    let id ← required "manifest id" (attr item "id")
    if (byId.get? id).isSome then throw "EPUB has a duplicate manifest id"
    let some member := resolvePath path (attr item "href") | throw "Unsupported EPUB manifest URL"
    let resource : Resource := ⟨id, member, ← required "manifest media type" (attr item "media-type"), ← file member⟩
    resources := resources.push resource
    byId := byId.insert id resource
  let mut readingOrder : Array Resource := #[]
  let mut total := 0
  for item in children spine do
    if !named opf "itemref" item then continue
    let some resource := byId.get? (attr item "idref") | throw "Unresolved EPUB spine item"
    if resource.mediaType != "application/xhtml+xml" then throw "Only XHTML spine items are supported"
    total := total + resource.bytes.size
    if readingOrder.size >= 512 || total > maxChapterBytes then throw "EPUB reading-order limit exceeded"
    readingOrder := readingOrder.push resource
  if readingOrder.isEmpty then throw "EPUB has an empty reading order"
  return ⟨title, resources, readingOrder⟩

private def escape (s : String) : String :=
  s.replace "&" "&amp;" |>.replace "<" "&lt;" |>.replace ">" "&gt;" |>.replace "\"" "&quot;"

private def chapterId (i : Nat) := "epub-chapter-" ++ toString (i + 1)

private def chapterURL (index : Nat) := "?epubChapter=" ++ toString (index + 1)

private def link (book : Book) (path : String) (href : String) (paged : Bool) : Option String := do
  let fields := href.splitOn "#"
  if fields.length > 2 then none else
  let relative := fields.headD ""
  let target ← if relative.isEmpty then some path else resolvePath path relative
  let index ← book.spine.toList.findIdx? (fun r => r.path == target)
  let fragment ← String.fromUTF8? (WHATWG.URL.percentDecode (fields[1]?.getD "").toUTF8)
  let anchor := "#" ++ chapterId index ++ (if fragment.isEmpty then "" else "-" ++ fragment)
  return if paged && target != path then chapterURL index ++ anchor else anchor

private def raster (media : String) : Bool :=
  ["image/png","image/jpeg","image/gif"].contains media

private def markup : List String :=
  ["article","section","main","div","p","span","h1","h2","h3","h4","h5","h6","pre","code",
   "strong","em","b","i","u","s","sub","sup","small","kbd","samp","blockquote","q",
   "ul","ol","li","dl","dt","dd","table","thead","tbody","tfoot","tr","td","th",
   "caption","figure","figcaption","details","summary","a","br","hr"]

private inductive ReaderTask where
  | visit (depth : Nat) (node : NamespaceNode)
  | close (tag : String)

/-- Render the passive subset with an explicit work list and one output join.
The XHTML input bound and nesting bound also bound the work list traversal. -/
private def renderNodes (book : Book) (resource : Resource) (index : Nat) (paged : Bool)
    (nodes : List NamespaceNode) (imageBudget : Nat) : Except String (String × Nat) := do
  let mut pending := nodes.map (ReaderTask.visit 96)
  let mut output : List String := []
  let mut budget := imageBudget
  for _ in [:2 * resource.bytes.size + 1] do
    match pending with
    | [] => return (String.join output.reverse, budget)
    | .close tag :: rest =>
      pending := rest
      output := ("</" ++ tag ++ ">") :: output
    | .visit depth node :: rest =>
      pending := rest
      if depth == 0 then continue
      match node with
      | .other _ => output := escape (rawText node) :: output
      | .element name _ kids =>
        if name.namespace_ != some xhtml then continue
        let tag := name.localPart
        if ["script","style","iframe","object","embed","template","form","input","button"].contains tag then
          continue
        if tag == "img" then
          let alt := escape (attr node "alt")
          let image := (resolvePath resource.path (attr node "src")).bind fun path =>
            book.manifest.find? (fun r => r.path == path && raster r.mediaType)
          if let some img := image then
            if img.bytes.size > 0 && img.bytes.size <= budget then
              let source := "data:" ++ img.mediaType ++ ";base64," ++ WHATWG.Base64.encode img.bytes
              output := ("<img alt=\"" ++ alt ++ "\" src=\"" ++ source ++ "\">") :: output
              budget := budget - img.bytes.size
              continue
          output := alt :: output
          continue
        let anchor := attr node "id"
        let idAttr := if anchor.isEmpty then "" else " id=\"" ++ escape (chapterId index ++ "-" ++ anchor) ++ "\""
        if ["br","hr"].contains tag then
          output := ("<" ++ tag ++ idAttr ++ ">") :: output
          continue
        if markup.contains tag then
          let href := if tag == "a" then
            ((link book resource.path (attr node "href") paged).map fun u => " href=\"" ++ escape u ++ "\"").getD ""
            else ""
          output := ("<" ++ tag ++ idAttr ++ href ++ ">") :: output
          pending := .close tag :: pending
        pending := kids.foldr (fun child tail => .visit (depth - 1) child :: tail) pending
  throw "EPUB XHTML traversal exceeds input bound"

/-- A reflowable reading view with a generated chapter index and safe links. -/
def Book.readerHtml (book : Book) (chapter : Option Nat := none) : Except String String := do
  if chapter.any (fun index => index >= book.spine.size) then throw "EPUB chapter is out of range"
  let mut sections := ""
  let mut links := ""
  let mut budget := maxInlineImageBytes
  for i in [0:book.spine.size] do
    let resource := book.spine[i]!
    let root ← parse resource.bytes maxChapterBytes
    if !named xhtml "html" root then throw "Invalid EPUB XHTML document"
    let some body := child root xhtml "body" | throw "EPUB XHTML has no body"
    let id := chapterId i
    let name := ((child root xhtml "head").bind (fun n => child n xhtml "title")).map
      (fun n => String.join ((children n).map rawText))
    let label := escape (name.filter (!·.isEmpty) |>.getD ("Section " ++ toString (i + 1)))
    let href := if chapter.isSome then chapterURL i else "#" ++ chapterId i
    links := links ++ "<li><a href=\"" ++ href ++ "\">" ++ label ++ "</a></li>"
    if chapter.any (· != i) then continue
    let (content, left) ← renderNodes book resource i chapter.isSome (children body) budget
    sections := sections ++ "<section id=\"" ++ id ++ "\">" ++ content ++ "</section>"
    budget := left
  let title := escape book.title
  return "<!doctype html><meta charset=\"utf-8\"><title>" ++ title ++ "</title>" ++
    "<style>body{margin:24px;max-width:760px;line-height:1.5}img{max-width:100%}pre{white-space:pre-wrap}section{margin-top:2em}</style>" ++
    "<h1>" ++ title ++ "</h1><nav aria-label=\"Reading order\"><ol>" ++ links ++ "</ol></nav>" ++ sections

/-- The path fold refuses a parent segment at the archive root. -/
theorem segmentStep_root_parent : segmentStep [] ".." = none := rfl

#guard resolvePath "EPUB/text/cover.xhtml" "../media/cover.jpg" == some "EPUB/media/cover.jpg"
#guard resolvePath "book.opf" "../escape.xhtml" == none
#guard resolvePath "book.opf" "%2e%2e/escape.xhtml" == none
#guard resolvePath "book.opf" "http://example.org/a" == none
#guard resolvePath "book.opf" "a%2fb.xhtml" == none


private def fixture : Except String Book := do
  let entry := fun name (text : String) => ({name, bytes := text.toUTF8, method := 0} : XProc31.Zip.Entry)
  let bytes ← (XProc31.Zip.write {entries := [
    entry "mimetype" "application/epub+zip",
    entry "META-INF/container.xml" "<container xmlns=\"urn:oasis:names:tc:opendocument:xmlns:container\"><rootfiles><rootfile full-path=\"EPUB/book.opf\" media-type=\"application/oebps-package+xml\"/></rootfiles></container>",
    entry "EPUB/book.opf" "<package xmlns=\"http://www.idpf.org/2007/opf\" version=\"3.0\"><metadata><title xmlns=\"http://purl.org/dc/elements/1.1/\">Example</title></metadata><manifest><item id=\"a\" href=\"a.xhtml\" media-type=\"application/xhtml+xml\"/><item id=\"b\" href=\"b.xhtml\" media-type=\"application/xhtml+xml\"/></manifest><spine><itemref idref=\"b\"/><itemref idref=\"a\"/></spine></package>",
    entry "EPUB/a.xhtml" "<html xmlns=\"http://www.w3.org/1999/xhtml\"><body><p id=\"code\">B &amp; C</p></body></html>",
    entry "EPUB/b.xhtml" "<html xmlns=\"http://www.w3.org/1999/xhtml\"><body><a href=\"a.xhtml#code\">Read</a><script>secretScriptMarker</script><img src=\"file:///etc/passwd\" alt=\"unavailable\" /></body></html>"]}).mapError toString
  openBook bytes

#guard (fixture.map fun b => (b.title, b.spine.toList.map (·.id))).toOption == some ("Example", ["b","a"])
#guard match fixture.bind (·.readerHtml) with
  | .error _ => false
  | .ok s => (s.splitOn "href=\"#epub-chapter-2-code\"").length == 2 &&
      (s.splitOn "B &amp; C").length == 2 &&
      (s.splitOn "secretScriptMarker").length == 1 && (s.splitOn "file:///").length == 1

#guard match fixture.bind (fun book => book.readerHtml (some 0)) with
  | .error _ => false
  | .ok s => (s.splitOn "href=\"?epubChapter=2#epub-chapter-2-code\"").length == 2 &&
      (s.splitOn "id=\"epub-chapter-2\"").length == 1

#print axioms segmentStep_root_parent

end L4Factoidal.Epub
