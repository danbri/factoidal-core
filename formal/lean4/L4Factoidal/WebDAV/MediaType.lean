/-
L4Factoidal.WebDAV.MediaType — the media type of a resource that a client
writes with no Content-Type.
https://github.com/danbri/factoidal/issues/1122

GLib's WebDAV client (gvfs, the client of GNOME Files) sends PUT with no
Content-Type, and it shows a remote file with the type the server reports
as `DAV:getcontenttype`. Before this module the server stored such a file
as `application/octet-stream`, so a text file saved from GNOME Files read
back as binary (lab run of 2026-10-28,
`tests/webdav-desktop/results/20261028-gvfs-1.54.4/`).

Rule (owner, 2026-10-28, "1 y" to the proposal of issue 1122): when a PUT
(or a LOCK that makes an empty resource, RFC 4918 §9.10.4) has no
Content-Type, or an empty one, the type comes from the extension of the
last segment of the target by the fixed table `extensionTypes`; a name with
no extension, or an extension not in the table, gets
`application/octet-stream`. RFC 9110 §8.3 lets a recipient examine the data
or assume `application/octet-stream` when Content-Type is absent; this
server takes neither the content nor any other header into account.

The extension is the text after the last `.` of the name, in ASCII lower
case (`String.toLower`, which changes only `A`..`Z`). A name with no `.`, a
name that ends with `.`, and a name whose only `.` is its first character
(`.hidden`) have no extension.

A name that starts with `._` is an AppleDouble header file, which macOS
writes beside a file to hold its extended attributes and resource fork on a
volume that cannot store them; its type is `application/applefile` (RFC
1740 §2, the AppleDouble header part), whatever its extension.

The table uses registered media types (IANA) and, for the three link-file
kinds that have none, the names of the freedesktop.org shared-mime-info
database: `application/x-desktop`, `application/x-mswinurl`,
`application/x-webloc`.
-/

namespace L4Factoidal.WebDAV

/-- The media type of a resource with no known type (RFC 9110 §8.3). -/
def defaultMediaType : String := "application/octet-stream"

/-- Extension (ASCII lower case, no `.`) to media type. -/
def extensionTypes : List (String × String) :=
  [ ("txt", "text/plain"), ("text", "text/plain"), ("log", "text/plain"),
    ("md", "text/markdown"), ("markdown", "text/markdown"),
    ("csv", "text/csv"), ("tsv", "text/tab-separated-values"),
    ("html", "text/html"), ("htm", "text/html"), ("xhtml", "application/xhtml+xml"),
    ("css", "text/css"), ("js", "text/javascript"), ("mjs", "text/javascript"),
    ("json", "application/json"), ("jsonld", "application/ld+json"),
    ("xml", "application/xml"), ("yaml", "application/yaml"), ("yml", "application/yaml"),
    ("ics", "text/calendar"), ("vcf", "text/vcard"),
    ("ttl", "text/turtle"), ("nt", "application/n-triples"), ("nq", "application/n-quads"),
    ("trig", "application/trig"), ("rdf", "application/rdf+xml"), ("owl", "application/rdf+xml"),
    ("n3", "text/n3"), ("rq", "application/sparql-query"), ("ru", "application/sparql-update"),
    ("srj", "application/sparql-results+json"), ("srx", "application/sparql-results+xml"),
    ("svg", "image/svg+xml"), ("png", "image/png"), ("jpg", "image/jpeg"), ("jpeg", "image/jpeg"),
    ("gif", "image/gif"), ("webp", "image/webp"), ("avif", "image/avif"),
    ("pdf", "application/pdf"), ("zip", "application/zip"), ("gz", "application/gzip"),
    ("wasm", "application/wasm"),
    ("mp3", "audio/mpeg"), ("wav", "audio/wav"), ("mp4", "video/mp4"), ("webm", "video/webm"),
    ("desktop", "application/x-desktop"), ("url", "application/x-mswinurl"),
    ("webloc", "application/x-webloc") ]

/-- The extension of a file name, in ASCII lower case (module comment). -/
def nameExtension (name : String) : Option String :=
  let parts := name.splitOn "."
  match parts.getLast? with
  | none => none
  | some ext =>
    if parts.length < 2 || ext.isEmpty || (parts.length == 2 && parts.head? == some "") then none
    else some ext.toLower

/-- The type of an AppleDouble header file (RFC 1740 §2). -/
def appleDoubleType : String := "application/applefile"

/-- The media type of a resource named `name` whose writer gave none. -/
def mediaTypeForName (name : String) : String :=
  if name.startsWith "._" then appleDoubleType else
  match nameExtension name with
  | none => defaultMediaType
  | some e => ((extensionTypes.find? (·.1 == e)).map (·.2)).getD defaultMediaType

/-- The type of a segment list: from its last segment (`Path.storagePath`
segments, decoded). -/
def mediaTypeForSegs (segs : List String) : String :=
  mediaTypeForName (segs.getLast?.getD "")

/-- Every answer is the default type, the AppleDouble type or a type of the table. -/
theorem mediaTypeForName_cases (name : String) :
    mediaTypeForName name = defaultMediaType ∨ mediaTypeForName name = appleDoubleType ∨
      ∃ e, (e, mediaTypeForName name) ∈ extensionTypes := by
  unfold mediaTypeForName
  split
  · exact Or.inr (Or.inl rfl)
  · cases hx : nameExtension name with
    | none => exact Or.inl (by simp)
    | some e =>
      cases h : extensionTypes.find? (·.1 == e) with
      | none => exact Or.inl (by simp [h])
      | some p => exact Or.inr (Or.inr ⟨p.1, by simpa [h] using List.mem_of_find?_eq_some h⟩)

/-- A name with no extension that is not an AppleDouble name gets the default type. -/
theorem mediaTypeForName_none (name : String) (ha : name.startsWith "._" = false)
    (h : nameExtension name = none) : mediaTypeForName name = defaultMediaType := by
  simp [mediaTypeForName, ha, h]

/-! ## Checks -/

-- The table: extensions in lower case, no `.`, none listed twice.
#guard extensionTypes.all (fun (e, _) => e == e.toLower && !e.isEmpty && !(e.contains '.'))
#guard (extensionTypes.map (·.1)).eraseDups.length == extensionTypes.length

#guard nameExtension "a.txt" == some "txt"
#guard nameExtension "A.TXT" == some "txt"
#guard nameExtension "a.tar.gz" == some "gz"
#guard nameExtension ".hidden" == none
#guard nameExtension "trailing." == none
#guard nameExtension "no-extension" == none
#guard nameExtension "" == none
#guard nameExtension ".remote_sparql.txt.sb-1234" == some "sb-1234"
#guard nameExtension "café.Md" == some "md"

#guard mediaTypeForName "notes.txt" == "text/plain"
#guard mediaTypeForName "Page.HTML" == "text/html"
#guard mediaTypeForName "data.ttl" == "text/turtle"
#guard mediaTypeForName "open-dashboard.desktop" == "application/x-desktop"
#guard mediaTypeForName "open-dashboard.url" == "application/x-mswinurl"
#guard mediaTypeForName "open-dashboard.webloc" == "application/x-webloc"
#guard mediaTypeForName "image.png" == "image/png"
#guard mediaTypeForName "archive.unknownext" == defaultMediaType
#guard mediaTypeForName ".DS_Store" == defaultMediaType
#guard mediaTypeForName "._notes.txt" == appleDoubleType
#guard mediaTypeForName "._" == appleDoubleType
#guard mediaTypeForSegs ["config", "remote_sparql.txt"] == "text/plain"
#guard mediaTypeForSegs [] == defaultMediaType

end L4Factoidal.WebDAV
