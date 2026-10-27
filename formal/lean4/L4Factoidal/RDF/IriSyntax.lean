/-
L4Factoidal.RDF.IriSyntax — is a string an ABSOLUTE IRI (RFC 3987) or an
absolute URI (RFC 3986)?

Spec: RFC 3987 section 2.2 (the IRI ABNF) and RFC 3986 section 3 (URI).
RML-Core's term generation rules (rule 2 and 3) ask exactly this
question of every value a template or reference produces under
`rml:IRI` and `rml:URI`, and raise a data error when the answer is no.

The tree's `RDF.isIri` is a different and weaker test (non-empty, has a
colon) that the term constructors need as a type invariant. It accepts
`http://example.com/Juan Daniel`, which has a space, and RML must not
turn that into a term.

## What is checked

    absolute-IRI = scheme ":" ihier-part [ "?" iquery ]
    IRI          = absolute-IRI [ "#" ifragment ]

The checker takes the IRI production (fragment allowed), since RML
produces `http://example.com/a#b`. The authority is checked as
`[ iuserinfo "@" ] ihost [ ":" port ]` with `ihost` an IP-literal in
brackets, or any run of `iunreserved / pct-encoded / sub-delims`. An
IPv4 address is a special case of the last, so it needs no production of
its own. The path, query and fragment are checked character by
character against `ipchar`, `iprivate` and `pct-encoded`.

## What is not checked

IPv6 and IPvFuture literals are accepted as any run of hexadecimal
digits, colons, dots and the IPvFuture characters between the brackets;
RFC 3986's `IPv6address` has a case split on the position of `::` that
no RML test exercises. Nothing is normalised and nothing is resolved.
-/

namespace L4Factoidal.RDF

private def isAlpha (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

private def isDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def isHex (c : Char) : Bool :=
  isDigit c || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

/-- RFC 3986 `unreserved`. -/
private def isUnreservedAscii (c : Char) : Bool :=
  isAlpha c || isDigit c || c == '-' || c == '.' || c == '_' || c == '~'

/-- RFC 3987 `ucschar`, the non-ASCII half of `iunreserved`. -/
def isUcsChar (c : Char) : Bool :=
  let n := c.toNat
  (0xA0 ≤ n && n ≤ 0xD7FF) || (0xF900 ≤ n && n ≤ 0xFDCF) ||
  (0xFDF0 ≤ n && n ≤ 0xFFEF) ||
  (0x10000 ≤ n && n ≤ 0x1FFFD) || (0x20000 ≤ n && n ≤ 0x2FFFD) ||
  (0x30000 ≤ n && n ≤ 0x3FFFD) || (0x40000 ≤ n && n ≤ 0x4FFFD) ||
  (0x50000 ≤ n && n ≤ 0x5FFFD) || (0x60000 ≤ n && n ≤ 0x6FFFD) ||
  (0x70000 ≤ n && n ≤ 0x7FFFD) || (0x80000 ≤ n && n ≤ 0x8FFFD) ||
  (0x90000 ≤ n && n ≤ 0x9FFFD) || (0xA0000 ≤ n && n ≤ 0xAFFFD) ||
  (0xB0000 ≤ n && n ≤ 0xBFFFD) || (0xC0000 ≤ n && n ≤ 0xCFFFD) ||
  (0xD0000 ≤ n && n ≤ 0xDFFFD) || (0xE1000 ≤ n && n ≤ 0xEFFFD)

/-- RFC 3987 `iprivate`, allowed in the query only. -/
def isIPrivate (c : Char) : Bool :=
  let n := c.toNat
  (0xE000 ≤ n && n ≤ 0xF8FF) || (0xF0000 ≤ n && n ≤ 0xFFFFD) ||
  (0x100000 ≤ n && n ≤ 0x10FFFD)

private def isSubDelim (c : Char) : Bool :=
  c == '!' || c == '$' || c == '&' || c == '\'' || c == '(' || c == ')' ||
  c == '*' || c == '+' || c == ',' || c == ';' || c == '='

/-- Scan a run of characters accepted by `ok`, where `%` must start a
    `pct-encoded` triple. `true` iff the whole list is consumed. -/
private def scanRun (ok : Char → Bool) : List Char → Bool
  | [] => true
  | '%' :: a :: b :: rest => isHex a && isHex b && scanRun ok rest
  | '%' :: _ => false
  | c :: rest => ok c && scanRun ok rest
termination_by cs => cs.length

/-- `iunreserved / sub-delims`, the part of `ipchar` that needs no
    extra punctuation. -/
private def isIPcharBase (c : Char) : Bool :=
  isUnreservedAscii c || isUcsChar c || isSubDelim c

private def isIPchar (c : Char) : Bool := isIPcharBase c || c == ':' || c == '@'

/-- A path: `/`-separated segments of `ipchar`. -/
private def pathOk (cs : List Char) : Bool :=
  scanRun (fun c => isIPchar c || c == '/') cs

private def queryOk (cs : List Char) : Bool :=
  scanRun (fun c => isIPchar c || isIPrivate c || c == '/' || c == '?') cs

private def fragmentOk (cs : List Char) : Bool :=
  scanRun (fun c => isIPchar c || c == '/' || c == '?') cs

/-- `iuserinfo = *( iunreserved / pct-encoded / sub-delims / ":" )`. -/
private def userinfoOk (cs : List Char) : Bool :=
  scanRun (fun c => isIPcharBase c || c == ':') cs

private def hostOk (cs : List Char) : Bool :=
  match cs with
  | '[' :: rest =>
      (match rest.reverse with
       | ']' :: inner =>
           !inner.isEmpty &&
             inner.all (fun c => isHex c || c == ':' || c == '.' || c == 'v' ||
                                  c == 'V' || isUnreservedAscii c || isSubDelim c)
       | _ => false)
  | _ => scanRun isIPcharBase cs

/-- `iauthority = [ iuserinfo "@" ] ihost [ ":" port ]`. -/
private def authorityOk (cs : List Char) : Bool :=
  let (userinfo, hostPort) :=
    match cs.findIdx? (· == '@') with
    | some i => (some (cs.take i), cs.drop (i + 1))
    | none   => (none, cs)
  let userOk := match userinfo with | some u => userinfoOk u | none => true
  -- A port follows the LAST colon that lies outside a bracketed host.
  let (host, port) :=
    match hostPort with
    | '[' :: _ =>
        (match hostPort.findIdx? (· == ']') with
         | some i =>
             let after := hostPort.drop (i + 1)
             (hostPort.take (i + 1),
              match after with | ':' :: p => some p | _ => none)
         | none => (hostPort, none))
    | _ =>
        (match hostPort.reverse.findIdx? (· == ':') with
         | some k =>
             let i := hostPort.length - 1 - k
             (hostPort.take i, some (hostPort.drop (i + 1)))
         | none => (hostPort, none))
  let portOk := match port with | some p => p.all isDigit | none => true
  let trailingOk :=
    match hostPort with
    | '[' :: _ =>
        (match hostPort.findIdx? (· == ']') with
         | some i => (match hostPort.drop (i + 1) with
                      | [] => true
                      | ':' :: _ => true
                      | _ => false)
         | none => false)
    | _ => true
  userOk && hostOk host && portOk && trailingOk

/-- Split a list at the first occurrence of `sep`: the part before, and
    the part after (without the separator). -/
private def splitFirst (sep : Char) (cs : List Char) : List Char × Option (List Char) :=
  match cs.findIdx? (· == sep) with
  | some i => (cs.take i, some (cs.drop (i + 1)))
  | none   => (cs, none)

/-- `scheme = ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )`. -/
private def schemeOk (cs : List Char) : Bool :=
  match cs with
  | c :: rest => isAlpha c &&
      rest.all (fun d => isAlpha d || isDigit d || d == '+' || d == '-' || d == '.')
  | [] => false

/-- The hierarchical part: `"//" iauthority ipath-abempty`, or a path
    that does not start with `//`. -/
private def hierPartOk (cs : List Char) : Bool :=
  match cs with
  | '/' :: '/' :: rest =>
      let (auth, path) :=
        match rest.findIdx? (· == '/') with
        | some i => (rest.take i, rest.drop i)
        | none   => (rest, [])
      authorityOk auth && pathOk path
  | _ => pathOk cs

/-- Is `s` an absolute IRI (RFC 3987 section 2.2), optionally followed by
    a fragment? The empty string, a relative reference, and any string
    holding a space, a control character or one of `<>"{}|\^` and the
    backtick are not. -/
def isAbsoluteIri (s : String) : Bool :=
  let cs := s.toList
  let (beforeFrag, frag) := splitFirst '#' cs
  let fragOk := match frag with | some f => fragmentOk f | none => true
  let (beforeQuery, query) := splitFirst '?' beforeFrag
  let queryOk' := match query with | some q => queryOk q | none => true
  match splitFirst ':' beforeQuery with
  | (scheme, some hier) => schemeOk scheme && hierPartOk hier && queryOk' && fragOk
  | (_, none) => false

/-- The rest of an `http://` or `https://` IRI in its common shape: RFC 3986
    `unreserved` characters and `/`, and at most one `#`. One pass over the
    string, no allocation. -/
def plainTailOk (r : Substring) : Bool :=
  (r.foldl (fun (st : Bool × Bool) c =>
     if !st.1 then st
     else if isUnreservedAscii c || c == '/' then st
     else if c == '#' && !st.2 then (true, true)
     else (false, st.2)) (true, false)).1

/-- `http://` or `https://`, then `plainTailOk`. Every such string is an
    absolute IRI: the scheme is `http` or `https`, the authority is a reg-name
    of unreserved characters (or empty), the path holds segments of unreserved
    characters, and the fragment, after the one `#`, holds unreserved
    characters and `/` (RFC 3987 section 2.2). The `#guard`s below check
    `isAbsoluteIri` on such strings. -/
def isPlainHttpIri (s : String) : Bool :=
  if s.startsWith "https://" then plainTailOk (s.toSubstring.drop 8)
  else if s.startsWith "http://" then plainTailOk (s.toSubstring.drop 7)
  else false

/-- `isAbsoluteIri`, with `isPlainHttpIri` first: the engine's one IRI check
    on its hot paths (the readers and the dataset check of the ops). Most
    IRIs of real data are in the plain shape and take one pass; the others
    take the full check. -/
def isAbsoluteIriFast (s : String) : Bool :=
  isPlainHttpIri s || isAbsoluteIri s

/-- Is `s` an RFC 3987 `irelative-ref` (section 2.2)?

    irelative-ref  = irelative-part [ "?" iquery ] [ "#" ifragment ]
    irelative-part = "//" iauthority ipath-abempty / ipath-absolute
                   / ipath-noscheme / ipath-empty
    ipath-noscheme = isegment-nz-nc *( "/" isegment )

    `isegment-nz-nc` has no `:`, so the first segment of a relative path holds
    no colon: `a_b:c` (whose `a_b` is not a scheme, section 3.1 of RFC 3986) and
    `:foo` are neither IRIs nor relative references
    (https://github.com/danbri/factoidal/issues/1057). -/
def isRelativeIriRef (s : String) : Bool :=
  let cs := s.toList
  let (beforeFrag, frag) := splitFirst '#' cs
  let fragOk := match frag with | some f => fragmentOk f | none => true
  let (beforeQuery, query) := splitFirst '?' beforeFrag
  let queryOk' := match query with | some q => queryOk q | none => true
  !((beforeQuery.takeWhile (· != '/')).contains ':') && hierPartOk beforeQuery && queryOk' && fragOk

/-- RFC 3987 `IRI-reference = IRI / irelative-ref`: what a Turtle or TriG
    IRIREF may hold before it is resolved against the base. -/
def isIriReference (s : String) : Bool :=
  isAbsoluteIri s || isRelativeIriRef s

/-- Is `s` an absolute URI (RFC 3986 section 3)? An absolute URI is an
    absolute IRI with no character beyond ASCII. -/
def isAbsoluteUri (s : String) : Bool :=
  s.toList.all (fun c => c.toNat < 128) && isAbsoluteIri s

/-! ## Build-time checks

Each production gets an accepting and a rejecting case. A checker that
returned `true` for everything, or `false` for everything, fails here. -/

-- Ordinary IRIs.
#guard isAbsoluteIri "http://example.com/"
#guard isAbsoluteIri "http://example.com/Person/Bob%2FCharles"
#guard isAbsoluteIri "http://example.com/a/b?q=1&r=2#frag"
#guard isAbsoluteIri "https://user:pw@example.com:8080/p"
#guard isAbsoluteIri "urn:isbn:0451450523"
#guard isAbsoluteIri "mailto:a@b.example"
#guard isAbsoluteIri "http://[2001:db8::1]:80/x"
-- Non-ASCII is allowed in an IRI (ucschar) and not in a URI.
#guard isAbsoluteIri "http://data.example.com/author/Zoë%20Krüger"
#guard !isAbsoluteUri "http://data.example.com/author/Zoë%20Krüger"
#guard isAbsoluteUri "http://data.example.com/author/Zo%C3%AB%20Kr%C3%BCger"
-- iprivate is allowed in the query and not in the path.
#guard isAbsoluteIri ("http://e.org/a?" ++ String.singleton (Char.ofNat 0xE000))
#guard !isAbsoluteIri ("http://e.org/a" ++ String.singleton (Char.ofNat 0xE000))

-- The datum of RMLTC0019b: a name with a space is not an IRI, with or
-- without a base in front of it.
#guard !isAbsoluteIri "http://example.com/Juan Daniel"
#guard !isAbsoluteIri "Juan Daniel"
-- A relative reference is not absolute.
#guard !isAbsoluteIri "Carlos"
#guard !isAbsoluteIri "/a/b"
#guard !isAbsoluteIri "//example.com/a"
#guard !isAbsoluteIri ""
-- Scheme rules.
#guard !isAbsoluteIri "1http://example.com/"
#guard !isAbsoluteIri ":foo"
#guard !isAbsoluteIri "ht tp://example.com/"
-- Forbidden characters and a malformed percent escape.
#guard !isAbsoluteIri "http://example.com/a<b"
#guard !isAbsoluteIri "http://example.com/a\"b"
#guard !isAbsoluteIri "http://example.com/a{b}"
#guard !isAbsoluteIri "http://example.com/a|b"
#guard !isAbsoluteIri "http://example.com/a\\b"
#guard !isAbsoluteIri "http://example.com/a%2"
#guard !isAbsoluteIri "http://example.com/a%zz"
-- A second `#` is not allowed in a fragment, and a space is not either.
#guard !isAbsoluteIri "http://example.com/a#b#c"
#guard !isAbsoluteIri "http://example.com/a#b c"
-- Authority rules: a non-numeric port, an unbalanced bracket.
#guard !isAbsoluteIri "http://example.com:80a/"
#guard !isAbsoluteIri "http://[2001:db8::1/x"
-- https://github.com/danbri/factoidal/issues/1057: a scheme with `_`, a port
-- that is not digits, a leading colon, and an unclosed IP literal.
#guard !isAbsoluteIri "a_b:c"
#guard !isAbsoluteIri "entity.beeldbank_leiden_person:A.E._Stuur."
#guard !isAbsoluteIri "http://www:example.org/"
#guard !isAbsoluteIri "1a:foo"
#guard !isAbsoluteIri "http://[::1/"
#guard !isAbsoluteIri "http://a.org/d{|^}-e"
#guard !isAbsoluteIri "http://a/abc##def"
#guard isAbsoluteIri "http://a/abc#def"
#guard isAbsoluteIri "scheme:!$%25&'()*+,-./0123456789:/@ABCDEFGHIJKLMNOPQRSTUVWXYZ_abcdefghijklmnopqrstuvwxyz~?#"
-- Relative references (RFC 3987 irelative-ref).
#guard isRelativeIriRef ""
#guard isRelativeIriRef "#frag"
#guard isRelativeIriRef "?q=1"
#guard isRelativeIriRef "a/b:c"
#guard isRelativeIriRef "../up"
#guard isRelativeIriRef "/a:b"
#guard isRelativeIriRef "//example.org/a"
#guard !isRelativeIriRef "a_b:c"
#guard !isRelativeIriRef ":foo"
#guard !isRelativeIriRef "a%zz"
#guard !isRelativeIriRef "//www:x/"
#guard !isRelativeIriRef "a b"
#guard isIriReference "http://e.org/a" && isIriReference "a" && !isIriReference "a_b:c"
-- The fast path: every plain http(s) IRI is an absolute IRI, and the fast check
-- refuses what the full check refuses.
private def plainSamples : List String :=
  [ "http://example.org/", "https://example.org/a/b-c_d.e~f", "http://a/ns#name",
    "http://a/ns#frag/x", "http://", "https:///x", "http://xmlns.com/foaf/0.1/name",
    "http://www.w3.org/1999/02/22-rdf-syntax-ns#type" ]
#guard plainSamples.all isPlainHttpIri
#guard plainSamples.all isAbsoluteIri
#guard !isPlainHttpIri "http://a/b#c#d" && !isPlainHttpIri "http://a:80/" && !isPlainHttpIri "urn:x"
#guard !isPlainHttpIri "http://a/%41" && !isPlainHttpIri "http://a/b c" && !isPlainHttpIri "http://a/{x}"
#guard isAbsoluteIriFast "http://a:80/" && isAbsoluteIriFast "urn:x:y" && isAbsoluteIriFast "http://a/%41"
#guard !isAbsoluteIriFast "http://www:example.org/" && !isAbsoluteIriFast "a_b:c" && !isAbsoluteIriFast "http://a/b#c#d"
#guard !isAbsoluteIriFast "http://a.org/d{|^}-e" && !isAbsoluteIriFast "http://a/%zz"

end L4Factoidal.RDF
