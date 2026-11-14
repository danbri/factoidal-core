/-
L4Factoidal.HTML.ReferrerSource — which URL and which referrer policy a document gives the
requests its scripts make (Referrer Policy §8.3 "determine request's referrer" steps 1 to
3; HTML §4.2.5.1 `meta name=referrer`; HTML §7.3.1.3 policy containers).

A request whose referrer is "client" names its document's URL, and its policy, when it has
none of its own, is the document's. `Net.Xhr` holds both for the session's own document as
the embedder gave them (`State.client`, `State.policy`); this file answers for any document
of the realm, the page's or a same-origin frame's (`node_query` 173, `Hosts.DomOps`):

* The URL: the document's own when it came from `http` or `https`. An `iframe srcdoc`
  document names its container's document (§8.3 step 3, repeated). Any other document
  (`about:blank`, a `blob:` or `data:` document) names none, and its requests carry no
  referrer.
* The policy: the last `meta name=referrer` of the document, in tree order, whose content is
  a policy (`metaPolicy`); else the `Referrer-Policy` field of the document's response, as
  the embedder gave it for the frame; else, for a document with no response of its own
  (`srcdoc`), its container's.

Known limit: `metaPolicy` reads the tree as it is when the request is made. HTML sets the
policy when a `meta` is inserted or changed and never takes it back, so a page that removes
its `meta` and then makes a request gets the policy before the `meta` here, where a browser
keeps the `meta`'s. That sends at most what the earlier policy allowed.
-/
import L4Factoidal.DOM.Forms
import L4Factoidal.Net.ReferrerPolicy

namespace L4Factoidal.HTML.ReferrerSource
open L4Factoidal.DOM
open L4Factoidal.Net (ReferrerPolicy.Policy)

/-- The referrer policy that the `meta name=referrer` elements of document `doc` give: the
last one in tree order whose `content` is a policy or a legacy keyword
(`ReferrerPolicy.Policy.ofMeta`); `none` when there is none. -/
def metaPolicy (d : Dom) (doc : Nat) : Option ReferrerPolicy.Policy :=
  (d.treeOrder doc).foldl (fun acc k =>
    if Forms.isHtml d k ["meta"] && (Forms.attr? d k "name").map Dom.asciiLower == some "referrer" then
      match (Forms.attr? d k "content").bind ReferrerPolicy.Policy.ofMeta with
      | some p => some p
      | none => acc
    else acc) none

/-- The answer for document `doc` (0: the page's): the URL its requests name as their
referrer, U+0000, and the token of its policy; the URL `about:blank` is "no referrer" (never
empty, so a caller that got an answer always names a client), an empty token "the session's
own policy". `frames`: each frame element with its document;
`docURLs`: the URL of each frame document that came from one; `framePolicies`: the
`Referrer-Policy` field of each frame's response, by frame element. A document that is not
the page's and not a frame's names nothing. -/
def answer (d : Dom) (pageUrl : String) (frames : Array (Nat × Nat)) (docURLs framePolicies : Array (Nat × String))
    (doc : Nat) : String := Id.run do
  let mut cur := doc
  let mut pol : Option ReferrerPolicy.Policy := none
  for _ in [0:16] do
    if pol.isNone then pol := metaPolicy d cur
    if cur == 0 then return pageUrl ++ "\x00" ++ ((pol.map (·.token)).getD "")
    match frames.find? (·.2 == cur) with
    | none => return "about:blank\x00" ++ ((pol.map (·.token)).getD "")
    | some (el, _) =>
      let url := ((docURLs.find? (·.1 == cur)).map (·.2)).getD ""
      if url.startsWith "http:" || url.startsWith "https:" then
        let own := (ReferrerPolicy.Policy.ofHeader (((framePolicies.find? (·.1 == el)).map (·.2)).getD "")).getD .default
        return url ++ "\x00" ++ (pol.getD own).token
      else if (Forms.attr? d el "srcdoc").isSome then cur := (d.get el).doc
      else return "about:blank\x00" ++ ((pol.map (·.token)).getD "")
  return "about:blank\x00"

/-! ## Checks (`#guard` is a test; the documents of WPT referrer-policy/gen `top.meta`,
`iframe.meta`, `iframe.http-rp`, `srcdoc-inherit.meta` and `srcdoc.meta`) -/

private def el (lname : String) (attrs : List (String × String)) (parent : Option NodeId) (kids : List NodeId)
    (doc : NodeId := 0) : Node :=
  { type := .element, ns := some htmlNS, lname, parent, kids := kids.toArray, doc,
    attrs := (attrs.map fun (k, v) => ({ lname := k, value := v } : Attr)).toArray }

/-- Document 0 > meta name=Referrer content=origin (1), meta name=referrer content=bogus (2),
iframe (3) whose document is 4 > meta name=referrer content=never (5); iframe srcdoc (6)
whose document is 7 (no meta); iframe (8) whose document is 9 (no meta). -/
private def tree : Dom :=
  { nodes := #[
      { type := .document, kids := #[1, 2, 3, 6, 8] },
      el "meta" [("name", "Referrer"), ("content", "origin")] (some 0) [],
      el "meta" [("name", "referrer"), ("content", "bogus")] (some 0) [],
      el "iframe" [] (some 0) [],
      { type := .document, kids := #[5], doc := 4 },
      el "meta" [("name", "referrer"), ("content", "never")] (some 4) [] 4,
      el "iframe" [("srcdoc", "x")] (some 0) [],
      { type := .document, kids := #[], doc := 7 },
      el "iframe" [] (some 0) [],
      { type := .document, kids := #[], doc := 9 }] }

private def frames : Array (Nat × Nat) := #[(3, 4), (6, 7), (8, 9)]
private def urls : Array (Nat × String) := #[(4, "http://a.example/frame.html"), (9, "http://a.example/other.html")]
private def top : String := "http://a.example/top.html"

-- the last meta that names a policy wins; a content that is not a policy changes nothing
#guard metaPolicy tree 0 == some .origin
#guard metaPolicy tree 4 == some .noReferrer && metaPolicy tree 7 == none
#guard answer tree top frames urls #[] 0 == "http://a.example/top.html\x00origin"
-- a frame's document: its own URL, its own meta, else its response's field, else the default
#guard answer tree top frames urls #[] 4 == "http://a.example/frame.html\x00no-referrer"
#guard answer tree top frames urls #[(8, "unsafe-url")] 9 == "http://a.example/other.html\x00unsafe-url"
#guard answer tree top frames urls #[] 9 == "http://a.example/other.html\x00strict-origin-when-cross-origin"
-- a srcdoc document names its container's document and inherits its policy
#guard answer tree top frames urls #[] 7 == "http://a.example/top.html\x00origin"
-- a frame document with no URL of its own (about:blank) and a document that is no frame's: none
#guard answer tree top #[(3, 4), (6, 7), (8, 9)] #[] #[] 9 == "about:blank\x00"
#guard answer tree top #[] urls #[] 4 == "about:blank\x00no-referrer"

end L4Factoidal.HTML.ReferrerSource
