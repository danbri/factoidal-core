/-
L4Factoidal.Net.CspPolicy — Content Security Policy as a page's policy (CSP Level 3,
https://w3c.github.io/webappsec-csp/): §2.2 parsing a serialized policy and a policy list,
§2.3.1 source expressions with the keyword, nonce and hash sources, §6.8.3 the directive
fallback lists, §6.7.1.1 the script directives' pre-request check, §6.7.2 URL matching
(`Net.Csp`), §6.7.3 "does element match source list for type and source" for inline scripts
and styles, and `eval`. Every enforcement point of the engine asks one of the three
questions of this file (`blocksRequest`, `blocksInline`, `blocksEval`) and gets, with the
answer, the violations to report (`violationsRequest` and its two siblings).

## Decisions

* A list of policies is a conjunction: a request, an inline block or `eval` goes ahead only
  when no enforced policy objects (`blocksRequest_append`: adding a policy never allows what
  was blocked). A report-only policy never blocks; it only adds to the violations.
* A policy with no directive for a kind (after the fallback list) does not restrict it.
* Hash sources are checked with the engine's SHA-2 from HACL* (`Crypto.WebHacl.hashFast`,
  through `Net.Integrity`'s algorithms); the digest function is an argument so that the
  `#guard`s run on the specification's SHA-2. Nothing is hashed by code of this file.
* A nonce matches only when the element's nonce is not empty and equals a nonce source
  exactly (case-sensitive).
* `'unsafe-inline'` counts only when the list has no nonce source and no hash source, and for
  scripts no `'strict-dynamic'` (§6.7.3.2): a policy written for nonces is not weakened by a
  fallback meant for old browsers.
* With `'strict-dynamic'`, host and scheme sources of a script directive are not read: a
  script that the parser did not insert is allowed, a parser-inserted one needs a nonce.
* A source expression that does not parse is skipped (it allows nothing).
-/
import L4Factoidal.Net.Csp
import L4Factoidal.Net.Integrity

namespace L4Factoidal.Net.CspPolicy
open L4Factoidal.Net.Csp
open L4Factoidal.Crypto.WebHacl (HashAlg)
open L4Factoidal.WHATWG

/-- A source expression that is not a URL matcher (§2.3.1). -/
inductive Keyword where
  | unsafeInline
  | unsafeEval
  | strictDynamic
  | unsafeHashes
  | wasmUnsafeEval
  | reportSample
  | nonce (value : String)
  /-- A hash source: its algorithm and the bytes of its value (`none`: not base64, so it
  matches nothing). -/
  | hash (alg : HashAlg) (digest : Option ByteArray)
  deriving Inhabited

/-- One directive: its name (lower case), the URL matchers and the keywords of its value,
and the value's tokens as written (`report-uri`, `sandbox`). -/
structure Directive where
  name : String
  sources : List Source := []
  keywords : List Keyword := []
  values : List String := []
  deriving Inhabited

/-- One policy: its directives (the first of each name), its disposition, and its text. -/
structure Policy where
  directives : List Directive := []
  reportOnly : Bool := false
  text : String := ""
  deriving Inhabited

/-! ## Parsing (§2.2.1, §2.2.2, §2.3.1) -/

/-- The tokens of a directive: split on ASCII whitespace, empty ones dropped. -/
def tokens (s : String) : List String :=
  ((s.split fun c => c == ' ' || c == '\t' || c == '\n' || c == '\x0c' || c == '\r').toList.map (·.toString)).filter (!·.isEmpty)

/-- A keyword, nonce or hash source; `none` for any other token. -/
def keywordOf (t : String) : Option Keyword :=
  let l := lower t
  if !(l.startsWith "'" && l.endsWith "'" && l.length ≥ 2) then none else
  let inner := ((t.drop 1).dropEnd 1).toString
  match lower inner with
  | "unsafe-inline" => some .unsafeInline
  | "unsafe-eval" => some .unsafeEval
  | "strict-dynamic" => some .strictDynamic
  | "unsafe-hashes" => some .unsafeHashes
  | "wasm-unsafe-eval" => some .wasmUnsafeEval
  | "report-sample" => some .reportSample
  | li =>
    if li.startsWith "nonce-" then
      let v := (inner.drop 6).toString
      if v.isEmpty then none else some (.nonce v)
    else match Integrity.entryOf inner with
      | some (a, d) => some (.hash a d)
      | none => none

/-- A host character of a host source (§2.3.1 `host-char`). -/
def hostChar (c : Char) : Bool := c.isAlphanum || c == '-'

/-- `host[:port][/path]` of a host source, with `scheme` already taken; `none` when the host
or the port is not of the grammar. -/
def hostSource (scheme : Option String) (rest : String) : Option Source :=
  let cs := rest.toList
  let hostPort := String.ofList (cs.takeWhile (· != '/'))
  let pathCs := cs.dropWhile (· != '/')
  let path := if pathCs.isEmpty then none else some (String.ofList pathCs)
  let (host, port) : String × Option String :=
    match hostPort.splitOn ":" with
    | [h] => (h, none)
    | [h, p] => (h, some p)
    | _ => ("", some "bad")
  let portPart : Option PortPart :=
    match port with
    | none => some .absent
    | some "*" => some .any
    | some p => if !p.isEmpty && p.all Char.isDigit then (p.toNat?.map PortPart.num) else none
  let labelsOk := fun (h : String) => !h.isEmpty && (h.splitOn ".").all fun l => !l.isEmpty && l.all hostChar
  match portPart with
  | none => none
  | some pp =>
    if host == "*" then some (.host scheme "" true pp path)
    else if host.startsWith "*." then
      let h := (host.drop 1).toString
      if labelsOk (h.drop 1).toString then some (.host scheme h true pp path) else none
    else if labelsOk host then some (.host scheme host false pp path) else none

/-- A scheme of the grammar: a letter, then letters, digits, `+`, `-`, `.`. -/
def schemeOk (s : String) : Bool :=
  match s.toList with
  | c :: cs => c.isAlpha && cs.all fun d => d.isAlphanum || d == '+' || d == '-' || d == '.'
  | [] => false

/-- A URL matcher of a source list: `'none'`, `'self'`, `*`, a scheme source or a host
source; `none` for a keyword, nonce or hash source and for a token that is not a source. -/
def sourceOf (t : String) : Option Source :=
  let l := lower t
  if l == "'none'" then some .none_
  else if l == "'self'" then some .self
  else if t == "*" then some .star
  else if t.startsWith "'" then none
  else if t.endsWith ":" && schemeOk (t.dropEnd 1).toString then some (.scheme (lower (t.dropEnd 1).toString))
  else match t.splitOn "://" with
    | [rest] => hostSource none rest
    | [s, rest] => if schemeOk s then hostSource (some (lower s)) rest else none
    | _ => none

/-- One directive from its tokens (the first is its name). -/
def directiveOf (ts : List String) : Option Directive :=
  match ts with
  | [] => none
  | n :: vs => some { name := lower n, sources := vs.filterMap sourceOf, keywords := vs.filterMap keywordOf, values := vs }

/-- §2.2.1 "parse a serialized CSP": the directives between `;`, the first of each name. -/
def parsePolicy (text : String) (reportOnly : Bool := false) : Policy :=
  let ds := (text.splitOn ";").foldl (fun (acc : List Directive) part =>
    match directiveOf (tokens part) with
    | some d => if acc.any (·.name == d.name) then acc else acc ++ [d]
    | none => acc) []
  { directives := ds, reportOnly, text := text.trimAscii.toString }

/-- §2.2.2 "parse a serialized CSP list": the policies between `,` (a header's fields joined
with commas); a policy with no directive is dropped. -/
def parseList (header : String) (reportOnly : Bool := false) : List Policy :=
  ((header.splitOn ",").map fun t => parsePolicy t reportOnly).filter (!·.directives.isEmpty)

/-! ## The directive that governs (§6.8.3) -/

/-- The fallback list of a directive name: itself first. -/
def fallbacks (name : String) : List String :=
  match name with
  | "script-src-elem" => ["script-src-elem", "script-src", "default-src"]
  | "script-src-attr" => ["script-src-attr", "script-src", "default-src"]
  | "style-src-elem" => ["style-src-elem", "style-src", "default-src"]
  | "style-src-attr" => ["style-src-attr", "style-src", "default-src"]
  | "worker-src" => ["worker-src", "child-src", "script-src", "default-src"]
  | "frame-src" => ["frame-src", "child-src", "default-src"]
  | "script-src" | "style-src" | "child-src" | "connect-src" | "font-src" | "img-src" | "manifest-src" | "media-src" |
    "object-src" | "prefetch-src" => [name, "default-src"]
  | _ => [name]

/-- The directive of `p` that governs `name`: the first of the fallback list that `p` has. -/
def Policy.directiveFor (p : Policy) (name : String) : Option Directive :=
  (fallbacks name).findSome? fun n => p.directives.find? (·.name == n)

/-! ## The three questions -/

def Directive.hasNonce (d : Directive) (nonce : String) : Bool :=
  !nonce.isEmpty && d.keywords.any fun k => match k with
    | .nonce v => v == nonce
    | _ => false

def Directive.has (d : Directive) (f : Keyword → Bool) : Bool := d.keywords.any f

def isStrictDynamic : Keyword → Bool
  | .strictDynamic => true
  | _ => false

def isNonceOrHash : Keyword → Bool
  | .nonce _ => true
  | .hash _ _ => true
  | _ => false

/-- A script-like directive name (the pre-request check of §6.7.1.1 applies). -/
def scriptLike (name : String) : Bool :=
  name == "script-src-elem" || name == "script-src" || name == "worker-src"

/-- Does the directive allow a request of kind `name` to `u`: a matching nonce; under
`'strict-dynamic'` (script kinds) every script the parser did not insert; else the URL
sources (`Net.Csp.allows`). -/
def Directive.allowsRequest (d : Directive) (name : String) (origin u : Url) (redirected : Bool) (nonce : String)
    (parserInserted : Bool) : Bool :=
  d.hasNonce nonce ||
    (if scriptLike name && d.has isStrictDynamic then !parserInserted else allows d.sources origin u redirected)

/-- §6.7.3.2 "does a source list allow all inline behavior for type": `'unsafe-inline'`, no
nonce or hash source, and for scripts no `'strict-dynamic'`. -/
def Directive.allowsAllInline (d : Directive) (script : Bool) : Bool :=
  d.has (fun k => match k with | .unsafeInline => true | _ => false) && !d.has isNonceOrHash &&
    !(script && d.has isStrictDynamic)

/-- A hash source of the directive is the digest of `source`. -/
def Directive.hashMatches (hash : HashAlg → ByteArray → ByteArray) (d : Directive) (source : ByteArray) : Bool :=
  d.keywords.any fun k => match k with
    | .hash a (some v) => decide (v = hash a source)
    | _ => false

/-- §6.7.3 "does element match source list for type and source". `element`: a `script` or
`style` element (a nonce counts, and hashes count); else an event handler or `style`
attribute (hashes count only with `'unsafe-hashes'`). -/
def Directive.allowsInline (hash : HashAlg → ByteArray → ByteArray) (d : Directive) (script element : Bool)
    (nonce : String) (source : ByteArray) : Bool :=
  d.allowsAllInline script || (element && d.hasNonce nonce) ||
    ((element || d.has (fun k => match k with | .unsafeHashes => true | _ => false)) && d.hashMatches hash source)

/-- The directive name for an inline block: a `script` or `style` element, or an attribute. -/
def inlineName (script element : Bool) : String :=
  if script then (if element then "script-src-elem" else "script-src-attr")
  else (if element then "style-src-elem" else "style-src-attr")

/-- The policies of `ps` that a request of kind `name` to `u` violates. -/
def violationsRequest (ps : List Policy) (name : String) (origin u : Url) (redirected : Bool := false)
    (nonce : String := "") (parserInserted : Bool := false) : List Policy :=
  ps.filter fun p => match p.directiveFor name with
    | none => false
    | some d => !d.allowsRequest name origin u redirected nonce parserInserted

/-- The policies an inline script or style violates. -/
def violationsInline (hash : HashAlg → ByteArray → ByteArray) (ps : List Policy) (script element : Bool)
    (nonce : String) (source : ByteArray) : List Policy :=
  ps.filter fun p => match p.directiveFor (inlineName script element) with
    | none => false
    | some d => !d.allowsInline hash script element nonce source

/-- The policies that `eval` and its kin violate (§6.1.11.3 script-src's pre-eval check:
`'unsafe-eval'` of the directive that governs `script-src`). -/
def violationsEval (ps : List Policy) : List Policy :=
  ps.filter fun p => match p.directiveFor "script-src" with
    | none => false
    | some d => !d.has (fun k => match k with | .unsafeEval => true | _ => false)

/-- Is it blocked: some enforced policy is violated. -/
def enforced (vs : List Policy) : Bool := vs.any (!·.reportOnly)

def blocksRequest (ps : List Policy) (name : String) (origin u : Url) (redirected : Bool := false)
    (nonce : String := "") (parserInserted : Bool := false) : Bool :=
  enforced (violationsRequest ps name origin u redirected nonce parserInserted)

def blocksInline (hash : HashAlg → ByteArray → ByteArray) (ps : List Policy) (script element : Bool)
    (nonce : String) (source : ByteArray) : Bool :=
  enforced (violationsInline hash ps script element nonce source)

def blocksEval (ps : List Policy) : Bool := enforced (violationsEval ps)

/-! ## Theorems -/

/-- Kind: security theorem (policies only restrict). Says: with more policies a request that
was blocked stays blocked: the block of two lists together is the block of either. Adding a
policy (a second header, a `meta`) never allows what the first forbade. -/
theorem blocksRequest_append (ps qs : List Policy) (name : String) (origin u : Url) (r : Bool) (nonce : String)
    (pi : Bool) :
    blocksRequest (ps ++ qs) name origin u r nonce pi =
      (blocksRequest ps name origin u r nonce pi || blocksRequest qs name origin u r nonce pi) := by
  simp [blocksRequest, enforced, violationsRequest, List.filter_append, List.any_append]

/-- Kind: security theorem (policies only restrict, inline). Says: the same for inline scripts
and styles. -/
theorem blocksInline_append (hash : HashAlg → ByteArray → ByteArray) (ps qs : List Policy) (script element : Bool)
    (nonce : String) (source : ByteArray) :
    blocksInline hash (ps ++ qs) script element nonce source =
      (blocksInline hash ps script element nonce source || blocksInline hash qs script element nonce source) := by
  simp [blocksInline, enforced, violationsInline, List.filter_append, List.any_append]

/-- Kind: policy theorem. Says: a report-only policy never blocks a request. -/
theorem reportOnly_never_blocks (p : Policy) (h : p.reportOnly = true) (name : String) (origin u : Url) (r : Bool)
    (nonce : String) (pi : Bool) : blocksRequest [p] name origin u r nonce pi = false := by
  simp [blocksRequest, enforced, violationsRequest, List.filter]
  split <;> simp [h]

/-- Kind: policy theorem (monotone source lists, at the directive). Says: for a directive
that is not under `'strict-dynamic'`, adding source expressions never blocks a request it
allowed. Does not say: the same of inline blocks, where adding a nonce or a hash source turns
`'unsafe-inline'` off (`allowsAllInline`), by the standard's design. -/
theorem allowsRequest_mono (d : Directive) (more : List Source) (name : String) (origin u : Url) (r : Bool)
    (nonce : String) (pi : Bool) (h : d.allowsRequest name origin u r nonce pi = true) :
    ({ d with sources := d.sources ++ more } : Directive).allowsRequest name origin u r nonce pi = true := by
  unfold Directive.allowsRequest at *
  simp only [Bool.or_eq_true] at *
  rcases h with h | h
  · exact Or.inl h
  · right
    show (if (scriptLike name && d.has isStrictDynamic) = true then !pi else allows (d.sources ++ more) origin u r) = true
    by_cases hs : (scriptLike name && d.has isStrictDynamic) = true
    · rw [if_pos hs] at h
      rw [if_pos hs]
      exact h
    · rw [if_neg hs] at h
      rw [if_neg hs]
      exact allows_mono_append _ _ _ _ _ h

/-- Kind: security theorem (inline). Says: an inline script or style that a directive allows
is allowed for one of three reasons only: the list allows all inline (`'unsafe-inline'` with
no nonce, hash or, for scripts, `'strict-dynamic'`); the element carries a nonce of the
list; or its text has a digest of the list. Nothing else lets an inline block run. -/
theorem allowsInline_cases (hash : HashAlg → ByteArray → ByteArray) (d : Directive) (script element : Bool)
    (nonce : String) (source : ByteArray) (h : d.allowsInline hash script element nonce source = true) :
    d.allowsAllInline script = true ∨ (element = true ∧ d.hasNonce nonce = true) ∨ d.hashMatches hash source = true := by
  unfold Directive.allowsInline at h
  simp only [Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (h | h) | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h.2)

/-- Kind: security theorem (nonces). Says: a nonce match needs a nonce that is not empty: an
element with no nonce never matches a nonce source. -/
theorem hasNonce_nonempty (d : Directive) (h : d.hasNonce "" = true) : False := by
  simp [Directive.hasNonce] at h

/-- Kind: security theorem (hash sources). Says: a hash match means that some hash source of
the directive is exactly the digest of the text under its algorithm. -/
theorem hashMatches_digest (hash : HashAlg → ByteArray → ByteArray) (d : Directive) (source : ByteArray)
    (h : d.hashMatches hash source = true) : ∃ a v, v = hash a source ∧ ∃ k ∈ d.keywords, k = Keyword.hash a (some v) := by
  unfold Directive.hashMatches at h
  rw [List.any_eq_true] at h
  obtain ⟨k, hk, hv⟩ := h
  cases k with
  | hash a dg =>
    cases dg with
    | none => simp at hv
    | some v => exact ⟨a, v, by simpa using hv, _, hk, rfl⟩
  | _ => simp at hv

/-! ## Checks (CSP §2.2, §2.3 and WPT content-security-policy cases) -/

private def spec (a : HashAlg) (b : ByteArray) : ByteArray := a.pure.run b
private def page : Url := { scheme := "https", host := "example.com" }
private def loc (s h : String) (path : String := "/") : Url := { scheme := s, host := h, path }
private def pol (t : String) : List Policy := parseList t

#guard (parsePolicy "script-src 'self' https://cdn.example; img-src *; SCRIPT-SRC 'none'").directives.map (·.name) == ["script-src", "img-src"]
#guard (parseList "default-src 'self', img-src *,  ").length == 2
#guard !blocksRequest (pol "script-src 'self'") "script-src-elem" page (loc "https" "example.com" "/a.js")
#guard blocksRequest (pol "script-src 'self'") "script-src-elem" page (loc "https" "evil.test" "/a.js")
#guard blocksRequest (pol "default-src 'none'") "connect-src" page (loc "https" "example.com")
#guard !blocksRequest (pol "img-src 'none'") "connect-src" page (loc "https" "evil.test")
-- two policies: both must allow
#guard blocksRequest (pol "connect-src *, connect-src 'self'") "connect-src" page (loc "https" "evil.test")
-- report-only: never blocks, but is a violation to report
#guard !blocksRequest (parseList "connect-src 'none'" true) "connect-src" page (loc "https" "example.com")
#guard (violationsRequest (parseList "connect-src 'none'" true) "connect-src" page (loc "https" "example.com")).length == 1
-- worker-src falls back to child-src, script-src, default-src (WPT gen/*/worker-src-*, script-src-*)
#guard blocksRequest (pol "script-src 'none'") "worker-src" page (loc "https" "example.com" "/w.js")
#guard !blocksRequest (pol "script-src 'none'; worker-src 'self'") "worker-src" page (loc "https" "example.com" "/w.js")
#guard blocksRequest (pol "child-src 'none'; script-src *") "worker-src" page (loc "https" "example.com" "/w.js")
-- host sources: wildcard, port, path, scheme
#guard !blocksRequest (pol "img-src *.example.com:* https://cdn.test/img/") "img-src" page (loc "https" "a.example.com")
#guard blocksRequest (pol "img-src *.example.com") "img-src" page (loc "https" "example.com")
#guard !blocksRequest (pol "img-src https://cdn.test/img/") "img-src" page (loc "https" "cdn.test" "/img/a.png")
#guard blocksRequest (pol "img-src https://cdn.test/img/") "img-src" page (loc "https" "cdn.test" "/js/a.js")
#guard !blocksRequest (pol "img-src https:") "img-src" page (loc "https" "x.test") && blocksRequest (pol "img-src https:") "img-src" page (loc "data" "")
#guard !blocksRequest (pol "img-src data:") "img-src" page (loc "data" "")
-- a source that does not parse allows nothing; a nonce lets a request through
#guard blocksRequest (pol "script-src ht!tp://x") "script-src-elem" page (loc "https" "x")
#guard !blocksRequest (pol "script-src 'nonce-abc'") "script-src-elem" page (loc "https" "evil.test") false "abc"
#guard blocksRequest (pol "script-src 'nonce-abc'") "script-src-elem" page (loc "https" "evil.test") false "ABC"
#guard blocksRequest (pol "script-src 'nonce-abc'") "script-src-elem" page (loc "https" "evil.test") false ""
-- strict-dynamic: host sources are not read; a script not inserted by the parser runs
#guard blocksRequest (pol "script-src 'strict-dynamic' 'nonce-abc' https:") "script-src-elem" page (loc "https" "x.test") false "" true
#guard !blocksRequest (pol "script-src 'strict-dynamic' 'nonce-abc' https:") "script-src-elem" page (loc "https" "x.test") false "" false
-- inline: 'unsafe-inline'; a nonce or a hash in the list turns it off; a hash of the text
#guard !blocksInline spec (pol "script-src 'unsafe-inline'") true true "" "alert(1)".toUTF8
#guard blocksInline spec (pol "script-src 'self'") true true "" "alert(1)".toUTF8
#guard blocksInline spec (pol "script-src 'unsafe-inline' 'nonce-abc'") true true "" "alert(1)".toUTF8
#guard !blocksInline spec (pol "script-src 'unsafe-inline' 'nonce-abc'") true true "abc" "alert(1)".toUTF8
#guard !blocksInline spec (pol "default-src 'none'; style-src 'unsafe-inline'") false true "" "p{}".toUTF8
#guard blocksInline spec (pol "default-src 'none'; style-src 'unsafe-inline'") true true "" "x".toUTF8
-- CSP §8.3 example: the SHA-256 of `alert('Hello, world.');`
#guard !blocksInline spec (pol "script-src 'sha256-qznLcsROx4GACP2dm0UCKCzCG+HiZ1guq6ZZDob/Tng='") true true "" "alert('Hello, world.');".toUTF8
#guard blocksInline spec (pol "script-src 'sha256-qznLcsROx4GACP2dm0UCKCzCG+HiZ1guq6ZZDob/Tng='") true true "" "alert('Hello, world!');".toUTF8
-- an event handler attribute: a hash counts only with 'unsafe-hashes'; a nonce never
#guard blocksInline spec (pol "script-src 'sha256-qznLcsROx4GACP2dm0UCKCzCG+HiZ1guq6ZZDob/Tng='") true false "" "alert('Hello, world.');".toUTF8
#guard !blocksInline spec (pol "script-src 'unsafe-hashes' 'sha256-qznLcsROx4GACP2dm0UCKCzCG+HiZ1guq6ZZDob/Tng='") true false "" "alert('Hello, world.');".toUTF8
#guard blocksInline spec (pol "script-src 'nonce-abc'") true false "abc" "x".toUTF8
-- script-src-attr and style-src-elem are read before their fallbacks
#guard !blocksInline spec (pol "script-src 'none'; script-src-attr 'unsafe-inline'") true false "" "x".toUTF8
#guard blocksInline spec (pol "style-src 'unsafe-inline'; style-src-elem 'none'") false true "" "x".toUTF8
-- eval
#guard blocksEval (pol "script-src 'self'") && !blocksEval (pol "script-src 'self' 'unsafe-eval'")
#guard blocksEval (pol "default-src 'self'") && !blocksEval (pol "img-src 'none'")

end L4Factoidal.Net.CspPolicy
