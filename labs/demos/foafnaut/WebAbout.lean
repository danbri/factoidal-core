import WebBuild

/-! about:foafnaut (`foafnaut:about`): which build this is, and the specifications this
repository implements in part.

A browser describing itself is a page a person may trust, so the engine writes all of it:
the layout, the specifications list and every escape. Its own facts (release, commit, build
time) come from `WebBuild`, compiled into it. What only the desktop host knows (its runtime,
the platform, the program's own build record, the engine library's sha256 as the host
measured it) comes in the request as data; the page shows it in its own section, labelled as
reported by the host and not checked by the engine, escaped like any other text. When the
host's record names another release or commit than the engine's, the page says so. -/
namespace WebAbout

/-- HTML text and attribute escaping: `&`, `<`, `>`, `"` and `'`. -/
def escape (s : String) : String :=
  String.join (s.toList.map fun c => match c with
    | '&' => "&amp;" | '<' => "&lt;" | '>' => "&gt;" | '"' => "&quot;" | '\'' => "&#39;"
    | c => c.toString)

#guard escape "<script>alert('x')</script> & \"y\"" ==
  "&lt;script&gt;alert(&#39;x&#39;)&lt;/script&gt; &amp; &quot;y&quot;"
#guard escape "plain 0.36.0" == "plain 0.36.0"

/-- The engine's build facts. -/
structure Engine where
  version : String
  commit : String
  builtAt : String
  dirty : Bool
  release : Bool
  /-- The hygiene ratchet's counts in this build: the engine's lab modules, and the
  L4Factoidal modules they import ("" when not known). -/
  hygieneLab : String := ""
  hygieneFormal : String := ""

/-- This engine's facts, as compiled into it. -/
def engine : Engine := ⟨WebBuild.version,WebBuild.commit,WebBuild.builtAt,WebBuild.dirty,WebBuild.release,
  WebBuild.hygieneLab,WebBuild.hygieneFormal⟩

/-- What the desktop host reports: rows to show, and its own build record's release and
commit (absent when it has none, as when run from source). -/
structure Host where
  rows : List (String × String) := []
  version : Option String := none
  commit : Option String := none

private def orUnknown (s : String) : String := if s.isEmpty then "unknown" else s

def kind (e : Engine) : String := if e.release then "release build" else "development build"

/-- The engine's answer to `foafnaut --version`. -/
def versionLine (e : Engine) : String :=
  s!"foafnaut {orUnknown e.version} ({kind e}), commit {orUnknown e.commit}" ++
    (if e.dirty then " (with uncommitted changes)" else "") ++ s!", built {orUnknown e.builtAt}"

/-- The line that says the host's build record and the engine disagree, or none. A host
commit matches when the engine's full commit starts with it (a short commit). A host that
gives no record has nothing to disagree with. -/
def mismatch (e : Engine) (h : Host) : Option String :=
  let commitDiffers := match h.commit with
    | some c => !c.isEmpty && !e.commit.startsWith c
    | none => false
  let versionDiffers := match h.version with
    | some v => !v.isEmpty && v != e.version
    | none => false
  if commitDiffers || versionDiffers then
    some s!"The desktop program's build record (release {orUnknown (h.version.getD "")}, commit {orUnknown (h.commit.getD "")}) does not match this engine (release {orUnknown e.version}, commit {orUnknown e.commit}): the program and the engine come from different builds."
  else none

private def sample : Engine := ⟨"0.36.0","abc123def4567890","2026-11-11T18:00:00Z",false,true,"",""⟩
#guard mismatch sample {commit := some "abc123def",version := some "0.36.0"} == none
#guard mismatch sample {} == none
#guard (mismatch sample {commit := some "fff000"}).isSome
#guard (mismatch sample {version := some "0.35.1",commit := some "abc123"}).isSome
#guard versionLine sample == "foafnaut 0.36.0 (release build), commit abc123def4567890, built 2026-11-11T18:00:00Z"

/-- Specifications this repository implements in part, A to Z by short name: name, link,
and the body when it is not the W3C. Each was checked against the code
(formal/lean4/L4Factoidal, labs/demos/foafnaut) on 2026-11-11. A name is listed when code
for it exists, not when it is complete. -/
def specs : List (String × String × String) :=
  [("Controlled Identifiers","https://www.w3.org/TR/cid-1.0/",""),
   ("CSS","https://www.w3.org/Style/CSS/specs.en.html",""),
   ("CSV on the Web","https://www.w3.org/TR/tabular-data-model/",""),
   ("Data Cube","https://www.w3.org/TR/vocab-data-cube/",""),
   ("Data Integrity","https://www.w3.org/TR/vc-data-integrity/",""),
   ("DOM","https://dom.spec.whatwg.org/","WHATWG"),
   ("ECMAScript","https://tc39.es/ecma262/","Ecma"),
   ("Encoding","https://encoding.spec.whatwg.org/","WHATWG"),
   ("Fetch","https://fetch.spec.whatwg.org/","WHATWG"),
   ("GRDDL","https://www.w3.org/TR/grddl/",""),
   ("HTML","https://html.spec.whatwg.org/","WHATWG"),
   ("JSON-LD","https://www.w3.org/TR/json-ld11/",""),
   ("Linked Web Storage","https://www.w3.org/groups/wg/lws/",""),
   ("MathML","https://www.w3.org/TR/mathml-core/",""),
   ("Namespaces in XML","https://www.w3.org/TR/xml-names/",""),
   ("N-Quads","https://www.w3.org/TR/n-quads/",""),
   ("N-Triples","https://www.w3.org/TR/n-triples/",""),
   ("OWL","https://www.w3.org/TR/owl2-overview/",""),
   ("PNG","https://www.w3.org/TR/png-3/",""),
   ("Pointer Events","https://www.w3.org/TR/pointerevents3/",""),
   ("R2RML","https://www.w3.org/TR/r2rml/",""),
   ("RDF","https://www.w3.org/TR/rdf11-concepts/",""),
   ("RDF Canonicalization","https://www.w3.org/TR/rdf-canon/",""),
   ("RDF Schema","https://www.w3.org/TR/rdf11-schema/",""),
   ("RDF/XML","https://www.w3.org/TR/rdf-syntax-grammar/",""),
   ("RIF","https://www.w3.org/TR/rif-overview/",""),
   ("SHACL","https://www.w3.org/TR/shacl/",""),
   ("SMIL","https://www.w3.org/TR/smil/",""),
   ("SPARQL","https://www.w3.org/TR/sparql11-overview/",""),
   ("SVG","https://www.w3.org/TR/SVG2/",""),
   ("TriG","https://www.w3.org/TR/trig/",""),
   ("Turtle","https://www.w3.org/TR/turtle/",""),
   ("UI Events","https://www.w3.org/TR/uievents/",""),
   ("URL","https://url.spec.whatwg.org/","WHATWG"),
   ("Verifiable Credentials","https://www.w3.org/TR/vc-data-model-2.0/",""),
   ("Web Annotation","https://www.w3.org/TR/annotation-model/",""),
   ("WebAssembly","https://www.w3.org/TR/wasm-core-2/",""),
   ("WebGPU","https://www.w3.org/TR/webgpu/",""),
   ("WGSL","https://www.w3.org/TR/WGSL/",""),
   ("XForms","https://www.w3.org/TR/xforms11/",""),
   ("XML","https://www.w3.org/TR/xml/",""),
   ("XML Canonicalization","https://www.w3.org/TR/xml-c14n11/",""),
   ("XML Encryption","https://www.w3.org/TR/xmlenc-core1/",""),
   ("XMLHttpRequest","https://xhr.spec.whatwg.org/","WHATWG"),
   ("XML Schema","https://www.w3.org/TR/xmlschema11-1/",""),
   ("XML Signature","https://www.w3.org/TR/xmldsig-core1/",""),
   ("XPath","https://www.w3.org/TR/xpath-31/",""),
   ("XPointer","https://www.w3.org/TR/xptr-framework/",""),
   ("XQuery","https://www.w3.org/TR/xquery-31/",""),
   ("XQuery and XPath Full Text","https://www.w3.org/TR/xpath-full-text-30/",""),
   ("XQuery Update Facility","https://www.w3.org/TR/xquery-update-30/",""),
   ("XSLT","https://www.w3.org/TR/xslt-30/","")]

/-- The sort key of a name: lower case, letters and digits only (as a reader sorts). -/
def sortKey (name : String) : String :=
  String.ofList ((name.toList.filter Char.isAlphanum).map Char.toLower)

-- A to Z, no name twice, every link https.
#guard (specs.zip specs.tail).all fun (a,b) => decide (sortKey a.1 < sortKey b.1)
#guard specs.all fun (_,url,_) => url.startsWith "https://"

/-- The release page of a build on danbri/factoidal-builds (the darwin-arm64 package). -/
def releaseURL (e : Engine) : Option String :=
  if e.commit.length < 12 then none
  else some s!"https://github.com/danbri/factoidal-builds/releases/tag/build-{String.ofList (e.commit.toList.take 12)}-foafnaut-darwin-arm64"

private def row (k v : String) : String := s!"<tr><th>{escape k}</th><td>{v}</td></tr>"

private def style : String :=
  "body{margin:24px;font-size:15px;line-height:22px;color:#203040;background:white}" ++
  "h1{margin:0 0 12px;font-size:24px;line-height:32px;color:#184078}" ++
  "h2{margin:24px 0 8px;font-size:18px;line-height:26px;color:#184078}" ++
  "th{text-align:left;white-space:nowrap;padding:4px 18px 4px 0;font-weight:normal;color:#5b6876;vertical-align:top}" ++
  "td{padding:4px 0;overflow-wrap:anywhere}ul{margin:0;padding-left:20px}li{margin:2px 0}.body{color:#5b6876}" ++
  ".warn{padding:8px 12px;border:2px solid #b03030;color:#801818;background:#fff0f0}.note{color:#5b6876}"

/-- The page: the engine's facts, a line when the host's record disagrees, the host's
report in its own section, and the specifications. -/
def page (e : Engine) (h : Host) : String :=
  let version := orUnknown e.version
  let engineRows :=
    row "Release" (escape s!"{version} ({kind e})") ++
    row "Commit" (escape (orUnknown e.commit) ++ (if e.dirty then " (with uncommitted changes)" else "")) ++
    row "Built" (escape (orUnknown e.builtAt) ++ " UTC") ++
    (match releaseURL e with
      | some url => row "Release page" s!"<a href=\"{escape url}\">build-{escape (String.ofList (e.commit.toList.take 12))} on factoidal-builds</a>"
      | none => "") ++
    (if e.hygieneLab.isEmpty then "" else row "Hygiene, engine modules" (escape e.hygieneLab)) ++
    (if e.hygieneFormal.isEmpty then "" else row "Hygiene, library modules" (escape e.hygieneFormal))
  let warning := match mismatch e h with
    | some line => s!"<p class=\"warn\">{escape line}</p>"
    | none => ""
  let hostRows := String.join (h.rows.map fun (k,v) => row k (escape v))
  let hostSection := if h.rows.isEmpty then "" else
    "<h2>Reported by the desktop program</h2><p class=\"note\">The program that loaded the engine says this. The engine shows it as given and does not check it.</p><table>" ++
      hostRows ++ "</table>"
  let list := String.join (specs.map fun (name,url,body) =>
    s!"<li><a href=\"{escape url}\">{escape name}</a>" ++
      (if body.isEmpty then "" else s!" <span class=\"body\">({escape body})</span>") ++ "</li>")
  "<!doctype html><html lang=\"en\"><head><meta charset=\"utf-8\"><title>About Foafnaut</title><style>" ++ style ++
    "</style></head><body>" ++ s!"<h1>Foafnaut {escape version}</h1>" ++ warning ++
    "<h2>This engine</h2><p class=\"note\">Compiled into the built-in engine when it was built.</p><table>" ++ engineRows ++ "</table>" ++
    hostSection ++
    "<h2>Specifications</h2><p>Implemented in part: the built-in engine has code for each of these, and none is complete.</p><ul>" ++
    list ++ "</ul></body></html>"

-- Host text is escaped; a mismatch is said; the list is there.
#guard ((page sample {rows := [("Runtime","<b>x</b>")]}).splitOn "&lt;b&gt;x&lt;/b&gt;").length == 2
#guard ((page sample {rows := [("Runtime","<b>x</b>")]}).splitOn "<b>x").length == 1
#guard ((page sample {commit := some "fff000"}).splitOn "does not match this engine").length == 2
#guard ((page sample {commit := some "abc123"}).splitOn "does not match").length == 1
#guard ((page sample {}).splitOn "<li>").length == specs.length+1
#guard ((page sample {}).splitOn "Reported by the desktop program").length == 1

end WebAbout
