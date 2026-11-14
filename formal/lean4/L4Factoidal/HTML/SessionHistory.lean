/-
L4Factoidal.HTML.SessionHistory — the session history of a page, as far as one document
goes (HTML §7.4): `history.pushState` and `replaceState` ("shared history push/replace state
steps", "URL and history update steps"), navigation to a fragment (§7.4.2.3.3), and
`history.go`, `back` and `forward` among the entries of the document ("traverse the
history by a delta").

A history is a list of entries and the index of the current one; an entry is a URL and the
page's key for the state it stored. The page keeps the stored states (they are its values);
which entry is current, what a push removes, and whether a URL may be written into the
address are decided here (`answer`, node_query 197).

The security decision is `canRewrite` ("can have its URL rewritten", §7.4.6.3): a document
may give itself only a URL of its own origin; `canRewrite_origin` proves that scheme,
credentials, host and port stay.

Limits: every entry belongs to the one document of the session (a navigation to another
document starts another session), so a traversal never leaves the page.
-/
import L4Factoidal.WHATWG.URL.Parser

namespace L4Factoidal.HTML.SessionHistory
open L4Factoidal.WHATWG.URL

/-- A session history entry: its URL (serialized) and the page's key for its state (0: no
state, null). -/
structure Entry where
  url : String
  state : Nat := 0
  deriving Repr, BEq, DecidableEq, Inhabited

/-- The entries of a document and the index of the current one. -/
structure History where
  entries : List Entry
  index : Nat := 0
  deriving Repr, BEq, Inhabited

/-- The index names an entry. -/
def History.valid (h : History) : Prop := h.index < h.entries.length

def History.init (url : String) : History := { entries := [{ url }] }

def History.current (h : History) : Entry := h.entries.getD h.index default

/-- A new entry after the current one; the entries after it go. -/
def History.push (h : History) (e : Entry) : History :=
  { entries := h.entries.take (h.index + 1) ++ [e], index := (h.entries.take (h.index + 1)).length }

/-- The current entry replaced. -/
def History.replace (h : History) (e : Entry) : History :=
  { h with entries := h.entries.set h.index e }

/-- The history after a traversal by `delta`, or none when there is no such entry. -/
def History.traverse (h : History) (delta : Int) : Option History :=
  if 0 ≤ (h.index : Int) + delta ∧ ((h.index : Int) + delta).toNat < h.entries.length then
    some { h with index := ((h.index : Int) + delta).toNat }
  else none

/-! ## "Can have its URL rewritten" (§7.4.6.3) -/

/-- Whether a document with the URL `doc` may take the URL `target` without a navigation:
the same scheme, credentials, host and port; any path, query and fragment for http and
https; the same path for `file:`; only another fragment for every other scheme. -/
def sameParts (doc target : Url) : Bool :=
  doc.scheme == target.scheme && doc.username == target.username && doc.password == target.password &&
    doc.host == target.host && doc.port == target.port

def canRewrite (doc target : Url) : Bool :=
  sameParts doc target &&
    (if target.scheme == "http" || target.scheme == "https" then true
     else if target.scheme == "file" then doc.path == target.path
     else doc.path == target.path && doc.query == target.query)

/-- "Shared history push/replace state steps", the URL: `url` (none: the document keeps
its URL) parsed against the document's URL, when the document may take it. -/
def newURL (docURL : String) (url : Option String) : Option String :=
  match url with
  | none => some docURL
  | some u =>
    match parseUrl docURL none, parseUrl u (some docURL) with
    | some d, some t => if canRewrite d t then some t.serialize else none
    | _, _ => none

def fragmentOf (url : String) : Option String := (parseUrl url none).bind (·.fragment)

/-- A navigation to `url` stays in the document: the URLs are equal up to the fragment and
`url` has a fragment (§7.4.2.2 "navigate" step for fragment navigations). -/
def isFragmentNavigation (docURL url : String) : Bool :=
  match parseUrl docURL none, parseUrl url none with
  | some d, some t => t.fragment.isSome && d.serialize true == t.serialize true
  | _, _ => false

/-! ## Wire (node_query 197)

A history is its index, U+0002, and its entries separated by U+0002, each its state key,
U+0001, its URL. A serialized URL has no character below U+0020. -/

def wire (h : History) : String :=
  "\x02".intercalate (toString h.index :: h.entries.map fun e => toString e.state ++ "\x01" ++ e.url)

def parse (w : String) : History :=
  match w.splitOn "\x02" with
  | i :: es =>
    { index := i.toNat?.getD 0,
      entries := es.map fun e =>
        match e.splitOn "\x01" with
        | s :: rest => { url := "\x01".intercalate rest, state := s.toNat?.getD 0 }
        | [] => { url := "" } }
  | [] => { entries := [] }

/-- What the page is told after a change: "K", the current URL, U+0003, its state key,
U+0003, "1" when the fragment changed, U+0003, the number of entries, U+0003, the history. -/
def told (old : String) (h : History) : String :=
  let e := h.current
  "K" ++ "\x03".intercalate [e.url, toString e.state, (if fragmentOf old != fragmentOf e.url then "1" else "0"),
    toString h.entries.length, wire h]

/-- node_query 197: `q` is an operation, U+0000, a history (as `wire`; "" for none yet) and
arguments. "init", the document's URL. "push" and "replace": the history, the URL argument
("" with a fourth field "0" for none), "1" or "0" whether a URL was given, the state key:
answers `told`, or "S" when the URL does not parse or may not be written (a
"SecurityError"). "fragment": the history and a URL: `told` after a push with no state when
the URL is a fragment navigation, else "" (not a navigation inside the document). "go":
the history and a delta: `told`, or "" when there is no such entry. -/
def answer (q : String) : String :=
  match q.splitOn "\x00" with
  | ["init", url] => wire (History.init url)
  | [op, w, url, given, state] =>
    let h := parse w
    let doc := h.current.url
    if op == "push" || op == "replace" then
      match newURL doc (if given == "1" then some url else none) with
      | none => "S"
      | some u =>
        let e : Entry := { url := u, state := state.toNat?.getD 0 }
        told doc (if op == "push" then h.push e else h.replace e)
    else ""
  | ["fragment", w, url] =>
    let h := parse w
    let doc := h.current.url
    if isFragmentNavigation doc url then
      match parseUrl url none with
      | some t => told doc (h.push { url := t.serialize })
      | none => ""
    else ""
  | ["go", w, delta] =>
    let h := parse w
    match delta.toInt?.bind h.traverse with
    | some h' => told h.current.url h'
    | none => ""
  | _ => ""

/-! ## What is proved -/

/-- Safety (kind: a policy decision refuses what it must). Says: a URL that a document may
give itself has the document's scheme, credentials, host and port: `pushState` cannot make
the address show another origin. -/
theorem canRewrite_origin (doc target : Url) (h : canRewrite doc target = true) :
    doc.scheme = target.scheme ∧ doc.username = target.username ∧ doc.password = target.password ∧
      doc.host = target.host ∧ doc.port = target.port := by
  unfold canRewrite at h
  have hp : sameParts doc target = true := (Bool.and_eq_true _ _ ▸ h).1
  unfold sameParts at hp
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨hp.1.1.1.1, hp.1.1.1.2, hp.1.1.2, hp.1.2, hp.2⟩

/-- Says: a document may always keep its own URL. -/
theorem canRewrite_refl (u : Url) : canRewrite u u = true := by
  unfold canRewrite sameParts
  simp

/-- Says: after a push the index names the new entry, which is the last. -/
theorem push_valid (h : History) (e : Entry) : (h.push e).valid := by
  unfold History.valid History.push
  simp

theorem push_current (h : History) (e : Entry) : (h.push e).current = e := by
  unfold History.current History.push
  simp [List.getD]

/-- Says: a push leaves the entries up to the current one and adds one: nothing after the
new entry remains (the forward entries go). -/
theorem push_length (h : History) (e : Entry) (hv : h.valid) : (h.push e).entries.length = h.index + 2 := by
  unfold History.valid at hv
  unfold History.push
  simp only [List.length_append, List.length_take, List.length_cons, List.length_nil]
  omega

/-- Says: a replace keeps the number of entries and the index. -/
theorem replace_valid (h : History) (e : Entry) (hv : h.valid) : (h.replace e).valid := by
  unfold History.valid History.replace at *
  simpa using hv

theorem replace_current (h : History) (e : Entry) (hv : h.valid) : (h.replace e).current = e := by
  unfold History.valid at hv
  unfold History.current History.replace
  simp [List.getD, hv]

/-- Says: a traversal that happens lands on an entry. -/
theorem traverse_valid (h : History) (delta : Int) (h' : History) (ht : h.traverse delta = some h') : h'.valid := by
  unfold History.traverse at ht
  split at ht
  · rename_i hc
    cases ht
    exact hc.2
  · cases ht

/-- Says: a traversal changes only the index. -/
theorem traverse_entries (h : History) (delta : Int) (h' : History) (ht : h.traverse delta = some h') :
    h'.entries = h.entries := by
  unfold History.traverse at ht
  split at ht
  · cases ht; rfl
  · cases ht

/-- Says: `go(0)` stays where it is. -/
theorem traverse_zero (h : History) (hv : h.valid) : h.traverse 0 = some h := by
  unfold History.valid at hv
  unfold History.traverse
  simp [hv]

/-- Says: `back()` after a push is the entry that was current. -/
theorem push_back (h : History) (e : Entry) (hv : h.valid) :
    ((h.push e).traverse (-1)).map (·.current) = some h.current := by
  unfold History.valid at hv
  have hlen : (h.entries.take (h.index + 1)).length = h.index + 1 := by
    simp only [List.length_take]; omega
  unfold History.traverse History.push History.current
  simp only [hlen]
  have h1 : (0 : Int) ≤ ((h.index + 1 : Nat) : Int) + -1 := by omega
  have h2 : (((h.index + 1 : Nat) : Int) + -1).toNat = h.index := by omega
  simp only [List.length_append, hlen, List.length_cons, List.length_nil, h2]
  have h3 : (0 : Int) ≤ ((h.index + 1 : Nat) : Int) + -1 ∧ h.index < h.index + 1 + (0 + 1) := ⟨h1, by omega⟩
  rw [if_pos h3]
  simp only [Option.map_some, List.getD_eq_getElem?_getD, Option.some.injEq]
  rw [List.getElem?_append_left (by rw [hlen]; omega), List.getElem?_take_of_lt (by omega)]

/-! ## Tests -/

private def url (s : String) : Url := (parseUrl s none).getD {}

#guard canRewrite (url "https://example.com/a?b#c") (url "https://example.com/x/y?z#w")
#guard !canRewrite (url "https://example.com/a") (url "https://example.org/a")
#guard !canRewrite (url "https://example.com/a") (url "http://example.com/a")
#guard !canRewrite (url "https://example.com/a") (url "https://example.com:8443/a")
#guard !canRewrite (url "https://example.com/a") (url "https://user@example.com/a")
#guard canRewrite (url "file:///a/b") (url "file:///a/b?q#f") && !canRewrite (url "file:///a/b") (url "file:///a/c")
#guard canRewrite (url "data:text/html,x") (url "data:text/html,x#f") && !canRewrite (url "data:text/html,x") (url "data:text/html,y")
#guard canRewrite (url "about:blank") (url "about:blank#x") && !canRewrite (url "about:blank") (url "about:srcdoc")
#guard newURL "https://example.com/dir/page.html" (some "other?x=1") == some "https://example.com/dir/other?x=1"
#guard newURL "https://example.com/dir/page.html" (some "https://evil.example/") == none
#guard newURL "https://example.com/dir/page.html" none == some "https://example.com/dir/page.html"
#guard newURL "https://example.com/dir/page.html" (some "") == some "https://example.com/dir/page.html"
#guard newURL "https://example.com/" (some "http://[") == none
#guard isFragmentNavigation "https://example.com/a?b" "https://example.com/a?b#c" && !isFragmentNavigation "https://example.com/a" "https://example.com/b#c"
#guard !isFragmentNavigation "https://example.com/a#x" "https://example.com/a"
private def h3 : History := ((History.init "https://e.test/").push { url := "https://e.test/1", state := 1 }).push { url := "https://e.test/2", state := 2 }
#guard h3.index == 2 && h3.entries.length == 3 && h3.current.url == "https://e.test/2"
#guard (h3.traverse (-1)).map (·.current.url) == some "https://e.test/1" && h3.traverse 1 == none && h3.traverse (-3) == none
#guard ((h3.traverse (-2)).map fun h => (h.push { url := "https://e.test/n" }).entries.length) == some 2
#guard parse (wire h3) == h3 && parse (wire (History.init "about:blank")) == History.init "about:blank"
#guard answer "init\x00https://e.test/" == "0\x020\x01https://e.test/"
#guard answer ("push\x00" ++ wire (History.init "https://e.test/") ++ "\x00/a#f\x001\x007") ==
  "Khttps://e.test/a#f\x037\x031\x032\x03" ++ wire ((History.init "https://e.test/").push { url := "https://e.test/a#f", state := 7 })
#guard answer ("push\x00" ++ wire (History.init "https://e.test/") ++ "\x00https://other.test/\x001\x007") == "S"
#guard answer ("replace\x00" ++ wire h3 ++ "\x00\x000\x009") ==
  "Khttps://e.test/2\x039\x030\x033\x03" ++ wire (h3.replace { url := "https://e.test/2", state := 9 })
#guard answer ("go\x00" ++ wire h3 ++ "\x00-2") == "Khttps://e.test/\x030\x030\x033\x03" ++ wire { h3 with index := 0 }
#guard answer ("go\x00" ++ wire h3 ++ "\x001") == "" && answer ("go\x00" ++ wire h3 ++ "\x00x") == ""
#guard answer ("fragment\x00" ++ wire (History.init "https://e.test/p") ++ "\x00https://e.test/p#top") ==
  "Khttps://e.test/p#top\x030\x031\x032\x03" ++ wire ((History.init "https://e.test/p").push { url := "https://e.test/p#top" })
#guard answer ("fragment\x00" ++ wire (History.init "https://e.test/p") ++ "\x00https://e.test/q#top") == ""

end L4Factoidal.HTML.SessionHistory
