/-
HTML §2.4.3 and §4.2.3: document base URLs and the frozen base URL.
The script host calls `update` at mutations, before history changes, and on first use.
Only newly allocated nodes are inspected on the path without base elements. Tree walks
are bounded by Dom.treeOrder's arena-size fuel; cached entries are bounded by the
number of documents containing base elements. No shadow or template contents are walked.
-/
import L4Factoidal.DOM.Arena
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.Net.CspPolicy

namespace L4Factoidal.DOM.BaseURL
open L4Factoidal.WHATWG

structure Context where
  url : String := "about:blank"
  aboutBase : Option String := none
  encoding : Encoding.Encoding := .utf_8
  policies : List L4Factoidal.Net.CspPolicy.Policy := []
  policyURL : Option String := none

/-- The fallback uses the captured creator base only for about:blank/about:srcdoc. -/
def fallback (c : Context) : String :=
  let beforeFragment := (c.url.splitOn "#").headD ""
  let path := (beforeFragment.splitOn "?").headD ""
  if path == "about:blank" || (path == "about:srcdoc" && !(beforeFragment.contains '?')) then
    c.aboutBase.getD c.url
  else c.url

def parse (text base : String) (enc : Encoding.Encoding) : Option URL.Url := do
  let b ← (URL.basicParse base).toOption
  (URL.basicParse text (some b) none none enc).toOption

/-- HTMLBaseElement.href also uses fallback, including when href is absent. -/
def baseHref (c : Context) (value : Option String) : String :=
  let text := value.getD ""
  ((parse text (fallback c) c.encoding).map (·.href)).getD text

/-- Set the frozen base URL; CSP base-uri has no default-src fallback. -/
def freeze (c : Context) (href : String) : String :=
  let fb := fallback c
  match parse href fb c.encoding with
  | none => fb
  | some u =>
    let asCsp := fun (v : URL.Url) =>
      ({ scheme := v.scheme, host := v.hostname, port := v.port, path := v.pathname } : L4Factoidal.Net.Csp.Url)
    let origin := ((URL.parseUrl (c.policyURL.getD c.url)).map asCsp).getD { scheme := "", host := "" }
    if u.scheme == "data" || u.scheme == "javascript" ||
        L4Factoidal.Net.CspPolicy.blocksRequest c.policies "base-uri" origin (asCsp u) then fb
    else u.href

def href? (d : Dom) (n : NodeId) : Option String :=
  if Dom.isHtmlElement (d.get n) "base" then d.getAttributeNS? n none "href" else none

/-- First base-with-href in document tree order; an invalid URL still wins selection. -/
def first (d : Dom) (doc : NodeId) : Option NodeId :=
  (d.treeOrder doc false).find? fun n => (href? d n).isSome

structure Frozen where
  doc : NodeId
  node : NodeId
  href : String
  url : String
  deriving Inhabited

/-- Events that can change selection or re-freeze the current element. -/
inductive Change where
  | none
  | tree (moved : Array NodeId := #[])
  | href (node : NodeId)
  deriving Inhabited

def Change.forces (d : Dom) (node : NodeId) : Change → Bool
  | .none => false
  | .href n => n == node
  | .tree moved => moved.any fun n => d.isInclusiveAncestor n node

/-- Retain a frozen value until selection, href, or an explicit mutation changes it. -/
def select (d : Dom) (doc : NodeId) (c : Context) (old : Option Frozen) (change : Change) : Option Frozen := do
  let node ← first d doc
  let href := (href? d node).getD ""
  match old with
  | some f =>
    if f.node == node && f.href == href && !change.forces d node then return f
    else return { doc, node, href, url := freeze c href }
  | none => return { doc, node, href, url := freeze c href }

structure State where
  /-- Arena nodes already inspected for newly allocated base elements. -/
  seen : Nat := 0
  candidates : Array NodeId := #[]
  frozen : Array Frozen := #[]
  /-- Creator bases survive removal of the frame and later parent base changes. -/
  about : Array (NodeId × String) := #[]
  deriving Inhabited

/-- Refresh after an operation. With no bases, no document-tree walk or URL parse runs.
Unrelated attribute and text writes do not revisit existing base elements. -/
def update (s : State) (d : Dom) (context : NodeId → Context) (change : Change := .none) : State := Id.run do
  if s.seen == d.size then
    if s.candidates.isEmpty then return s
    match change with
    | .none => return s
    | _ => pure ()
  let mut candidates := s.candidates
  for n in [s.seen:d.size] do
    if Dom.isHtmlElement (d.get n) "base" then candidates := candidates.push n
  let added := candidates.size != s.candidates.size
  let s := { s with seen := d.size, candidates }
  if candidates.isEmpty then return s
  if !added then
    match change with
    | .none => return s
    | .href n => if !Dom.isHtmlElement (d.get n) "base" then return s
    | .tree _ => pure ()
  let mut docs := s.frozen.map (·.doc)
  for n in candidates do
    let doc := (d.get n).doc
    if !docs.contains doc then docs := docs.push doc
  let mut frozen := #[]
  for doc in docs do
    if let some f := select d doc (context doc) (s.frozen.find? (·.doc == doc)) change then
      frozen := frozen.push f
  return { s with frozen }

/-- Constant-time in the document size once mutations have maintained `frozen`. -/
def value (s : State) (doc : NodeId) (c : Context) : String :=
  ((s.frozen.find? (·.doc == doc)).map (·.url)).getD (fallback c)

/-- Kind: selection invariant. Says: without a base-with-href in tree order, selection
returns none, regardless of any old frozen value. Does not say: that all DOM adapters
call select after mutations, or that the URL parser is conformant. -/
theorem select_none (d : Dom) (doc : NodeId) (c : Context) (old : Option Frozen) (ch : Change)
    (h : ∀ n ∈ d.treeOrder doc false, (href? d n).isSome = false) :
    select d doc c old ch = none := by
  have hf : first d doc = none := Array.find?_eq_none.mpr (by simpa using h)
  simp [select, hf]

/-- Kind: document-base invariant. Says: with no base-with-href in tree order,
the selected document base equals fallback. Does not say: that the mutation adapter
maintains its cache; those transitions are tested at the script command boundary. -/
theorem selected_no_base (d : Dom) (doc : NodeId) (c : Context) (old : Option Frozen) (ch : Change)
    (h : ∀ n ∈ d.treeOrder doc false, (href? d n).isSome = false) :
    ((select d doc c old ch).map (·.url)).getD (fallback c) = fallback c := by
  rw [select_none d doc c old ch h]
  rfl

/-- Kind: fallback invariant. Says: a document with no cached frozen entry returns its
fallback base. Does not say: that the cache matches every mutation (tested separately). -/
theorem value_no_base (s : State) (doc : NodeId) (c : Context)
    (h : ∀ f ∈ s.frozen, (f.doc == doc) = false) : value s doc c = fallback c := by
  have hf : s.frozen.find? (·.doc == doc) = none := Array.find?_eq_none.mpr (by simpa using h)
  simp [value, hf]

/-- Kind: fallback invariant. Says: an ordinary document uses its URL, even if a creator
base was supplied. Does not say: anything about about:blank or about:srcdoc. -/
theorem fallback_document (c : Context)
    (h : (((c.url.splitOn "#").headD "").splitOn "?").headD "" ≠ "about:blank")
    (h' : (((c.url.splitOn "#").headD "").splitOn "?").headD "" ≠ "about:srcdoc") :
    fallback c = c.url := by
  simp_all [fallback]

#print axioms select_none
#print axioms selected_no_base
#print axioms value_no_base
#print axioms fallback_document
end L4Factoidal.DOM.BaseURL
