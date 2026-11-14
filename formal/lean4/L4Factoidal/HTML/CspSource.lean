/-
L4Factoidal.HTML.CspSource — a document's Content Security Policy from its markup and the
scripts of the document it lets run (HTML §4.2.5.3 `meta http-equiv=content-security-policy`;
CSP §4.2.2 "should element's inline type behavior be blocked", §4.1.1 for the fetch of an
external script).

`metaText`: the policies a document's `meta` elements deliver, for `Net.Xhr.cspOf`.
`filterScripts`: of the classic scripts the embedder gathered for a document (each a node
and its text: an external script's text is the response's), those the policy lets run, and
the violations of the others; a `meta` policy governs the scripts after it in tree order. The decision for each is `Net.Xhr.cspRequest` (an external
script: `script-src-elem` by its URL and nonce, parser-inserted) or `Net.Xhr.cspInline` (an
inline one: by its nonce or the digest of its text), the same functions the prelude's ops
ask for scripts made later, so a script is judged by one rule however it came.

Known limits: a `meta` counts when it is a child of a `head` element at the time the
embedder starts the document (one that a script adds later is not enforced); the scripts
of frames' documents are not filtered here.
-/
import L4Factoidal.DOM.Forms
import L4Factoidal.Net.Xhr

namespace L4Factoidal.HTML.CspSource
open L4Factoidal.DOM
open L4Factoidal.Net

/-- A `meta http-equiv=content-security-policy` that is a child of a `head` element. -/
def isCspMeta (d : Dom) (k : NodeId) : Bool :=
  Forms.isHtml d k ["meta"] &&
    (Forms.attr? d k "http-equiv").map Dom.asciiLower == some "content-security-policy" &&
    ((d.get k).parent.any fun p => Forms.isHtml d p ["head"])

/-- The `content` of each such `meta` of document `doc`, in tree order, joined with commas (a
serialized policy list: CSP §2.2.2): the policies the document's markup delivers. -/
def metaText (d : Dom) (doc : Nat) : String :=
  ",".intercalate ((d.treeOrder doc).toList.filterMap fun k => if isCspMeta d k then Forms.attr? d k "content" else none)

/-- The classic scripts of `scripts` (node, text) that the document's policy lets run, and
the violation records of the rest (`Net.Xhr.report`). The policy of a script is the
response's (`header`, `reportOnly`: the fields the embedder gave) and that of each `meta`
before it in tree order: a `meta` governs what the parser meets after it, not the scripts
already run (HTML §4.2.5.3). A script with a `src` attribute is an external one, checked by
its URL against `base`. `page`: the document's origin for `'self'`. -/
def filterScripts (header reportOnly : String) (page : PageFetch.Page) (d : Dom) (base : String)
    (scripts : Array (Nat × String)) : Array (Nat × String) × Array String :=
  let s0 : Xhr.State := { page, csp := Xhr.cspOf header reportOnly "" }
  if s0.csp.isEmpty && (metaText d 0).isEmpty then (scripts, #[]) else
  let (s, blocked) := (d.treeOrder 0).foldl (fun (acc : Xhr.State × Array Nat) (k : NodeId) =>
    if isCspMeta d k then
      match Forms.attr? d k "content" with
      | some c => ({ acc.1 with csp := acc.1.csp ++ Xhr.cspOf "" "" c }, acc.2)
      | none => acc
    else if !Forms.isHtml d k ["script"] then acc
    else match scripts.find? fun (ks : Nat × String) => ks.1 == k with
      | none => acc
      | some ks =>
        let nonce := (Forms.attr? d k "nonce").getD ""
        let (s, no) := match Forms.attr? d k "src" with
          | some href =>
            let abs := ((WHATWG.URL.parseUrl href (some base)).map fun (u : WHATWG.URL.Url) => u.serialize).getD href
            Xhr.cspRequest acc.1 "script-src-elem" abs false nonce true k
          | none => Xhr.cspInline acc.1 true true nonce ks.2 k
        (s, if no then acc.2.push k else acc.2)) (s0, #[])
  (scripts.filter fun (ks : Nat × String) => !blocked.contains ks.1, s.violations)

/-! ## Checks -/

private def el (lname : String) (attrs : List (String × String)) (parent : Option NodeId) (kids : List NodeId) : Node :=
  { type := .element, ns := some htmlNS, lname, parent, kids := kids.toArray,
    attrs := (attrs.map fun (k, v) => ({ lname := k, value := v } : Attr)).toArray }

/-- Document 0 > head (1) [meta CSP (2), script src=/a.js (3), script src=http://b.example/b.js (4),
script inline (5), script nonce=n1 inline (6)], body (7) [meta CSP (8): not in head]. -/
private def tree : Dom :=
  { nodes := #[
      { type := .document, kids := #[1, 7] },
      el "head" [] (some 0) [2, 3, 4, 5, 6],
      el "meta" [("http-equiv", "Content-Security-Policy"), ("content", "script-src 'self' 'nonce-n1'")] (some 1) [],
      el "script" [("src", "/a.js")] (some 1) [],
      el "script" [("src", "http://b.example/b.js")] (some 1) [],
      el "script" [] (some 1) [],
      el "script" [("nonce", "n1")] (some 1) [],
      el "body" [] (some 0) [8],
      el "meta" [("http-equiv", "content-security-policy"), ("content", "img-src 'none'")] (some 7) []] }

private def pg : PageFetch.Page := PageFetch.Page.ofUrl "http://a.example/dir/page.html"
private def all : Array (Nat × String) := #[(3, "a()"), (4, "b()"), (5, "c()"), (6, "d()")]

#guard metaText tree 0 == "script-src 'self' 'nonce-n1'"
private def page1 : String := "http://a.example/dir/page.html"
-- the same-origin script and the inline script with the nonce run; the other two do not
#guard (filterScripts "" "" pg tree page1 all).1.map (·.1) == #[3, 6]
#guard (filterScripts "" "" pg tree page1 all).2.toList ==
  ["script-src-elem\x00http://b.example/b.js\x00script-src 'self' 'nonce-n1'\x00enforce\x004\x00",
   "script-src-elem\x00inline\x00script-src 'self' 'nonce-n1'\x00enforce\x005\x00"]
-- the response's policy and the meta's both hold
#guard (filterScripts "script-src 'nonce-n1'" "" pg tree page1 all).1.map (·.1) == #[6]
-- no policy: every script, nothing to report; a report-only policy: every script, and reports
#guard (filterScripts "" "" pg { tree with nodes := tree.nodes.set! 2 (el "meta" [] (some 1) []) } page1 all).1.size == 4
#guard (filterScripts "" "script-src 'none'" pg { tree with nodes := tree.nodes.set! 2 (el "meta" [] (some 1) []) } page1 all).1.size == 4
#guard (filterScripts "" "script-src 'none'" pg { tree with nodes := tree.nodes.set! 2 (el "meta" [] (some 1) []) } page1 all).2.size == 4
-- a meta governs only the scripts after it: here it is the last child of head, and the four
-- scripts before it all run (the page of a WPT test: testharness.js first, then the policy)
private def late : Dom := { tree with nodes := (tree.nodes.set! 1 (el "head" [] (some 0) [3, 4, 5, 6, 2])) }
#guard (filterScripts "" "" pg late page1 all).1.size == 4 && (filterScripts "" "" pg late page1 all).2.isEmpty

end L4Factoidal.HTML.CspSource
