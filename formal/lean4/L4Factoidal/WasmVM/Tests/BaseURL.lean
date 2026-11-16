import L4Factoidal.WasmVM.Hosts.DomOps

/-! Original fixtures for HTML frozen bases and WPT url/a-element{,-origin}{,-xhtml}.
These exercise the script command and query boundary without running a page interpreter. -/
namespace L4Factoidal.WasmVM.Tests.BaseURL
open L4Factoidal.DOM
open L4Factoidal.WasmVM.Hosts.Dom

private def page : State :=
  { dom := parseHtmlDocument "<!doctype html><head></head><body><a href='../item?q=one two#f'></a><img src='photo.png'><form></form></body>"
    url := "https://example.test/dir/page.html" }

private def node (s : State) (name : String) : Nat :=
  ((s.dom.treeOrder 0).find? fun n => Dom.isHtmlElement (s.dom.get n) name).getD 0

private def run (s : State) (c : Command) : State :=
  match (exec c).run s with | .ok (_, s) => s | .error _ => s

private def query (s : State) (n op : Nat) (q : String := "") : String :=
  match (domOp s n op q).2 with | .ok r => r | .error e => s!"error:{e}"

private def reflected (s : State) (n : Nat) (iface prop : String) : String :=
  let r := Reflect.table.findIdx? fun r => r.iface == iface && r.idl == prop
  query s n 160 (r.map toString |>.getD "missing")

private def base (s : State) (href : Option String) (before : Option Nat := none) : State × Nat := Id.run do
  let n := s.dom.size
  let mut s := run s (.createElement "base" n)
  if let some h := href then s := run s (.setAttribute n "href" h)
  s := run s (.insertBefore (node s "head") n before)
  return (s, n)

#guard query page (node page "a") 164 == page.url
private def one := base page (some "https://other.test/assets/")
#guard query one.1 (node one.1 "a") 164 == "https://other.test/assets/"
#guard reflected one.1 (node one.1 "img") "HTMLImageElement" "src" == "https://other.test/assets/photo.png"
-- Empty and missing form action use the document URL, not its base URL.
#guard reflected one.1 (node one.1 "form") "HTMLFormElement" "action" == page.url
#guard reflected (run one.1 (.setAttribute (node one.1 "form") "action" "")) (node one.1 "form") "HTMLFormElement" "action" == page.url

-- A detached node retains its owner document's base (the WPT a-element pattern).
private def detached := run one.1 (.removeChild (node one.1 "body") (node one.1 "a"))
#guard query detached (node one.1 "a") 164 == "https://other.test/assets/"

private def two := base one.1 (some "https://second.test/")
#guard query two.1 0 164 == "https://other.test/assets/"
#guard query (run two.1 (.removeAttribute one.2 "href")) 0 164 == "https://second.test/"
#guard query (run two.1 (.removeChild (node two.1 "head") one.2)) 0 164 == "https://second.test/"
#guard query (run two.1 (.insertBefore (node two.1 "head") two.2 (some one.2))) 0 164 == "https://second.test/"
#guard query (base two.1 (some "../early/") (some one.2)).1 0 164 == "https://example.test/early/"
#guard query (run two.1 (.setAttribute one.2 "href" "relative/")) 0 164 == "https://example.test/dir/relative/"

-- Invalid first bases do not fall through to the second base.
#guard ["data:text/plain,x", "javascript:1", "http://[broken"].all fun bad =>
  query (run two.1 (.setAttribute one.2 "href" bad)) 0 164 == page.url
#guard query (run two.1 (.setAttribute one.2 "href" "")) 0 164 == page.url

-- Frozen bases survive a history URL change, including when no getter preceded it.
private def relative := base page (some "assets/")
-- (as `DomOps` op 197, the only change of the page's URL: the bases are tracked first)
private def history := { relative.1.ensureBases with url := "https://example.test/new/page.html" }
#guard query history 0 164 == "https://example.test/dir/assets/"
#guard query (run history (.setAttribute relative.2 "href" "assets/")) 0 164 == "https://example.test/new/assets/"
#guard query (run history (.appendChild (node history "head") relative.2)) 0 164 == "https://example.test/new/assets/"
-- HTMLBaseElement.href uses fallback at read time, including a missing href.
#guard reflected history relative.2 "HTMLBaseElement" "href" == "https://example.test/new/assets/"
#guard reflected (base page none).1 (base page none).2 "HTMLBaseElement" "href" == page.url

-- Nodes in template contents and shadow trees do not establish document bases.
private def hidden : State :=
  { page with dom := parseHtmlDocument "<template><base href='https://hidden.test/'></template><body><a></a>" }
#guard query hidden 0 164 == page.url
private def xhtml : State :=
  { page with dom := xmlDocument "application/xhtml+xml" "<html xmlns='http://www.w3.org/1999/xhtml'><head><base href='https://xml.test/'/></head><body><a href='a'/></body></html>" }
#guard query xhtml (node xhtml "a") 164 == "https://xml.test/"
private def foreign : State :=
  { page with dom := xmlDocument "application/xml" "<html><base href='https://foreign.test/'/><a/></html>" }
#guard query foreign 0 164 == page.url

-- Captured inheritance survives parent base changes and iframe removal.
private def framed : State :=
  connectFrames { one.1 with dom := (one.1.dom.createElement 0 "iframe").1 |> fun d =>
      (d.appendChild (node one.1 "body") one.1.dom.size).1, framing := true } #[0]
private def frameDoc := (framed.frames[0]!).2
#guard query framed frameDoc 164 == "https://other.test/assets/"
private def changedParent := run framed (.setAttribute one.2 "href" "https://later.test/")
#guard query changedParent frameDoc 164 == "https://other.test/assets/"
#guard query (run changedParent (.removeChild (node changedParent "body") framed.frames[0]!.1)) frameDoc 164 == "https://other.test/assets/"
private def srcdoc := attachDocument (run framed (.setAttribute framed.frames[0]!.1 "srcdoc" "<a href='x'>")) framed.frames[0]!.1 "<base href='sub/'><a href='x'>"
#guard query srcdoc.1 (srcdoc.2.getD 0) 164 == "https://other.test/assets/sub/"

-- CSP is checked at freeze time; disallowed schemes never become document bases.
#guard BaseURL.freeze { url := page.url, policies := L4Factoidal.Net.CspPolicy.parseList "base-uri 'self'" } "https://other.test/" == page.url
#guard BaseURL.freeze { url := page.url, policies := L4Factoidal.Net.CspPolicy.parseList "default-src 'none'" } "https://other.test/" == "https://other.test/"
#guard BaseURL.fallback { url := "about:blank?x#y", aboutBase := some page.url } == page.url
#guard BaseURL.fallback { url := "about:srcdoc#x", aboutBase := some page.url } == page.url
-- Reflection is checked for every URL row (all reflected src/href/cite/data/action rows).
#guard Reflect.table.all fun row => match row.kind with
  | .url _ =>
    if row.iface == "HTMLBaseElement" then true else
    let n := one.1.dom.size
    let s := run one.1 (.createElement "img" n)
    let s := run s (.setAttribute n row.content "asset")
    reflected s n row.iface row.idl == "https://other.test/assets/asset"
  | _ => true

-- Synthetic and adopted documents resolve against the new owner, not document 0.
private def otherDoc := run one.1 (.createNode 10 "" one.1.dom.size)
private def otherId := one.1.dom.size
private def otherBase := otherDoc.dom.size
private def other := Id.run do
  let mut s := run otherDoc (.createNode (3 + 16 * otherId) "base" otherBase)
  s := run s (.setAttribute otherBase "href" "https://synthetic.test/")
  let head := ((s.dom.treeOrder otherId).find? fun n => Dom.isHtmlElement (s.dom.get n) "head").getD 0
  return run s (.appendChild head otherBase)
#guard query other otherId 164 == "https://synthetic.test/"
#guard query (run other (.adoptNode (node one.1 "a") otherId)) (node one.1 "a") 164 == "https://synthetic.test/"
#guard query (run other (.removeAttribute otherBase "href")) otherId 164 == "about:blank"
#guard query (run history (.setAttributeNS relative.2 "" "href" "assets/")) 0 164 == "https://example.test/new/assets/"
#guard query (run history (.removeAttributeNS relative.2 "" "href")) 0 164 == history.url
#guard reflected (run history (.setAttribute relative.2 "href" "http://[bad")) relative.2 "HTMLBaseElement" "href" == "http://[bad"
#guard BaseURL.freeze { url := page.url, encoding := .windows_1252 } "?c=é" == "https://example.test/dir/page.html?c=%E9"
#guard BaseURL.fallback { url := "about:srcdoc#x?y", aboutBase := some page.url } == page.url
private def encodedFrame := attachDocument (framed.noteFrameEncoding framed.frames[0]!.1 "windows-1252") framed.frames[0]!.1 "<base href='?c=é'>"
#guard query encodedFrame.1 (encodedFrame.2.getD 0) 164 == "https://other.test/assets/?c=%E9"
#guard BaseURL.freeze { url := "about:srcdoc", aboutBase := some "https://cdn.test/", policyURL := some page.url, policies := L4Factoidal.Net.CspPolicy.parseList "base-uri 'self'" } "https://example.test/allowed/" == "https://example.test/allowed/"
private def shadowPage : State := { page with dom := parseHtmlDocument "<div id='host'></div>" }
private def shadowed := Id.run do
  let root := shadowPage.dom.size
  let host := (shadowPage.dom.getElementById 0 "host").getD 0
  let mut s := run shadowPage (.attachShadow host 0 root)
  let b := s.dom.size
  s := run s (.createElement "base" b)
  s := run s (.setAttribute b "href" "https://shadow.test/")
  return run s (.appendChild root b)
#guard (shadowed.dom.get shadowPage.dom.size).shadowInit.isSome
#guard query shadowed 0 164 == page.url
private def manyAppendsUntracked := Id.run do
  let mut s := page
  for _ in [0:20] do
    let n := s.dom.size
    s := run s (.createElement "base" n)
    s := run s (.setAttribute n "href" "https://x.test/")
    s := run s (.appendChild (node page "body") n)
  return s
#guard query manyAppendsUntracked 0 164 == "https://x.test/"
private def encodedDom := parseHtmlDocument "<meta charset=windows-1252><body></body>"
-- (as a session's start: the parser's nodes are those below the arena's size then)
private def encodedPage : State := { page with dom := encodedDom, bases := { parsed := some encodedDom.size } }
#guard query (base encodedPage (some "?c=é")).1 0 164 == "https://example.test/dir/page.html?c=%E9"
-- The encoding is captured at the first use of a base (here a `baseURI` read); later
-- script changes to the text do not change it.
private def used := (domOp encodedPage 0 164 "").1
#guard used.bases.live
private def changedEncodingText := run used (.setTextContent (node encodedPage "body") "é")
-- A page that uses no base pays nothing at mutations: its bases stay untracked.
#guard !(run encodedPage (.setTextContent (node encodedPage "body") "é")).bases.live
#guard !manyAppendsUntracked.bases.live
#guard query (base changedEncodingText (some "?c=é")).1 0 164 == "https://example.test/dir/page.html?c=%E9"
private def refusedFrame := attachDocument { framed with commandLimit := 0 } framed.frames[0]!.1 "<base href='/new/'>"
#guard refusedFrame.2.isNone && refusedFrame.1.frames == framed.frames && refusedFrame.1.dom.size == framed.dom.size
-- Gated re-selection (`BaseURL.State.affected`): removals name the removed node, and a
-- change that moves no base keeps the selection without a tree walk.
private def wrapped : State :=
  { page with dom := parseHtmlDocument "<body><div id='w'><base href='https://inner.test/'></div><base href='https://outer.test/'><p id='p'></p></body>" }
private def wrapper := (wrapped.dom.getElementById 0 "w").getD 0
private def para := (wrapped.dom.getElementById 0 "p").getD 0
#guard query wrapped 0 164 == "https://inner.test/"
-- removing an ancestor of the selected base selects the next one
#guard query (run wrapped (.removeChild (node wrapped "body") wrapper)) 0 164 == "https://outer.test/"
-- textContent on the body removes both bases
#guard query (run wrapped (.setTextContent (node wrapped "body") "x")) 0 164 == page.url
-- moving a base-free node keeps the selection; appending many nodes keeps it
private def manyAppends := Id.run do
  let mut s := wrapped
  for _ in [0:50] do
    let n := s.dom.size
    s := run s (.createElement "i" n)
    s := run s (.appendChild para n)
  return s
#guard query manyAppends 0 164 == "https://inner.test/"
-- a base made detached changes nothing until it is inserted before the selected one
private def early := Id.run do
  let n := wrapped.dom.size
  let mut s := run wrapped (.createElement "base" n)
  s := run s (.setAttribute n "href" "https://early.test/")
  return (s, n)
#guard query early.1 0 164 == "https://inner.test/"
#guard query (run early.1 (.insertBefore (node early.1 "body") early.2 (some wrapper))) 0 164 == "https://early.test/"
-- removing a base that is not selected keeps the selected one
private def outer := ((wrapped.dom.treeOrder 0).filter (fun n => Dom.isHtmlElement (wrapped.dom.get n) "base"))[1]!
private def noOuter := run wrapped (.removeChild (node wrapped "body") outer)
#guard query noOuter 0 164 == "https://inner.test/"
-- (and the removal took place: without the wrapper too, the fallback)
#guard query (run noOuter (.removeChild (node wrapped "body") wrapper)) 0 164 == page.url
end L4Factoidal.WasmVM.Tests.BaseURL
