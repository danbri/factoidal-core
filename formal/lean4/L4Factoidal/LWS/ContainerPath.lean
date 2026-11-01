/-
L4Factoidal.LWS.ContainerPath — which URLs a host may send a request to,
when its authority (a credential, a selected pod) is one HTTP(S) container.

Issues: https://github.com/danbri/factoidal/issues/1127 (where credentials go:
a token scope needs a path-segment boundary) and row C3 of
`docs/designissues/2026-10-28-feature-combination-safety.md`. Record of the
JavaScript checks this module replaces:
`docs/20261031-lws-reader-path-confinement.md`.

Until 0.28.0 these decisions were JavaScript (`npm/factoidal/lib/sbm11-lws.mjs`
`containerUrl`/`resourceUrl`, `docs/web/hub/data-compositor/pod-storage.mjs`
`httpUrl`/`rootUrl`/`within`/`rootedPath`): an iron rule 7 violation
(anti-pattern 36). The hosts now call the pure op `lwsPath`
(`Wasm/Ops/LwsPath.lean`), which answers with the functions below.

URLs are read with the URL Standard parser of this tree
(`L4Factoidal.WHATWG.URL.parseUrl`, the parser of `new URL(input)`).

## The decisions

- `containerOf url canonical`: an absolute `http` or `https` URL, with no
  username or password, no query and no fragment (an empty `?` or `#` is a
  query or a fragment too). Without `canonical` the answer is the URL's
  serialization with `/` appended when its path does not end with `/` (the
  LWS reader). With `canonical` (the compositor's pod root) the input must
  have no character U+0000 to U+0020 and no backslash, must be its own
  serialization, must have no `%2F`, `%5C`, `%2E` or `%25` in its path, and
  must end with `/`; the answer is the input.
- `resourceIn container path`: `path` is a raw relative path (a file name, or
  names joined by `/`), never a URL reference. It is refused when it has a
  scheme, an empty, `.` or `..` segment, a backslash, `?`, `#` or a control
  character (U+0000 to U+001F, U+007F), or `%2F`, `%5C`, `%3F` or `%23`, in
  the text or in any text that repeated percent-decoding gives; or when it
  has more than 4096 UTF-16 code units. The answer is the container followed
  by the segments, each encoded as `encodeURIComponent` encodes it
  (ECMA-262 §19.2.6.5), and is given only when it parses, has the
  container's origin, and starts with the container (`underAtSegment`).
- `segmentIn root name`: one name (the compositor's "new filename"): as
  `resourceIn`, and also no `/`, no `%`, and no white space at either end
  (the characters ECMA-262 `String.prototype.trim` removes).
- `within root url canonical`: `root` is a container (`containerOf`), `url`
  passes the same checks (except the final `/`), has the root's origin, and
  starts with the root.

`underAtSegment root url` is the segment boundary: `root` ends with `/` and
is a prefix of `url`. So `https://s.example/alice-other/` is never within
`https://s.example/alice/` (`within_sibling_refused`).

`coversAtSegment` is the token scope of the LWS client
(`LWS.Client.TokenEntry.covers`): a prefix that ends with `/`, or that the
URL continues with `/`, `?` or `#`, or that is the whole URL.

## Theorems

- `resourceIn_under`: an answer of `resourceIn` has the container's origin
  and is under the container at a segment boundary.
- `segmentIn_under`: the same for `segmentIn`.
- `within_under`: when `within` accepts, the URL is under the root at a
  segment boundary; `within_canonical_under` states it for the input texts.
- `within_sibling_refused`: `within "https://s.example/alice/"
  "https://s.example/alice-other/" true` refuses (`within` with
  `canonical := false` too: `within_sibling_refused_lenient`).
- `coversAtSegment_prefix`, `coversAtSegment_sibling`: the token scope is a
  prefix, and `https://s.example/alice` does not cover
  `https://s.example/alice-other/x`.

## Assumes

The host sends the request to the URL the answer gives, unchanged, and does
not follow a redirect with the credential (the Node transport uses fetch
`redirect: 'error'`; `docs/20261031-lws-reader-path-confinement.md`). That
the server maps a URL under the container to a resource of the container is
the server's semantics (LWS 1.0 §Containers), not a fact this module proves.
-/
import L4Factoidal.WHATWG.URL.Parser

namespace L4Factoidal.LWS.ContainerPath

open L4Factoidal.WHATWG.URL

/-- The largest raw path, in UTF-16 code units (the JavaScript `length`). -/
def maxPathLength : Nat := 4096

/-! ## The segment boundary -/

/-- `url` is under `root` at a segment boundary: `root` ends with `/` and is
a prefix of `url`. -/
def UnderAtSegment (root url : String) : Prop :=
  root.toList.getLast? = some '/' ∧ root.toList <+: url.toList

/-- The decision of `UnderAtSegment`. -/
def underAtSegment (root url : String) : Bool :=
  root.toList.getLast? == some '/' && root.toList.isPrefixOf url.toList

theorem underAtSegment_iff (root url : String) :
    underAtSegment root url = true ↔ UnderAtSegment root url := by
  simp [underAtSegment, UnderAtSegment, List.isPrefixOf_iff_prefix]

/-- A root that ends with `/` holds every URL it prefixes. -/
theorem underAtSegment_append (root rest : String)
    (h : root.toList.getLast? = some '/') : underAtSegment root (root ++ rest) = true := by
  rw [underAtSegment_iff]
  refine ⟨h, ?_⟩
  rw [String.toList_append]
  exact List.prefix_append _ _

/-- The token scope of the LWS client: `root` is not empty, is a prefix of
`url`, and either ends with `/` or is followed in `url` by nothing, `/`,
`?` or `#`. -/
def coversAtSegment (root url : String) : Bool :=
  root != "" && root.toList.isPrefixOf url.toList &&
    (root.toList.getLast? == some '/' ||
      match (url.toList.drop root.toList.length).head? with
      | none => true
      | some c => c == '/' || c == '?' || c == '#')

theorem coversAtSegment_prefix {root url : String} (h : coversAtSegment root url = true) :
    root ≠ "" ∧ root.toList <+: url.toList := by
  simp only [coversAtSegment, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact ⟨h.1.1, (List.isPrefixOf_iff_prefix).1 h.1.2⟩

/-- A storage root without its final `/` does not cover a sibling whose
name continues it. -/
theorem coversAtSegment_sibling :
    coversAtSegment "https://s.example/alice" "https://s.example/alice-other/x" = false := by
  decide

theorem coversAtSegment_sibling_slash :
    coversAtSegment "https://s.example/alice/" "https://s.example/alice-other/x" = false := by
  decide

#guard coversAtSegment "https://s.example/alice" "https://s.example/alice/x"
#guard coversAtSegment "https://s.example/alice" "https://s.example/alice"
#guard coversAtSegment "https://s.example/ep" "https://s.example/ep?x=1"
#guard coversAtSegment "https://s.example/alice/" "https://s.example/alice/x"
#guard !coversAtSegment "" "https://s.example/alice/x"

/-! ## Characters -/

private def isAsciiAlphaC (c : Char) : Bool := ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')
private def isAsciiDigitC (c : Char) : Bool := '0' ≤ c && c ≤ '9'

/-- A control character: U+0000 to U+001F, or U+007F. -/
def isControl (c : Char) : Bool := c.toNat ≤ 0x1F || c.toNat == 0x7F

/-- The characters ECMA-262 `String.prototype.trim` removes (WhiteSpace and
LineTerminator, ECMA-262 §12.2 and §12.3; Zs as of Unicode 15). -/
def isJsTrimSpace (c : Char) : Bool :=
  let n := c.toNat
  n == 0x09 || n == 0x0A || n == 0x0B || n == 0x0C || n == 0x0D || n == 0x20 ||
  n == 0xA0 || n == 0x1680 || (0x2000 ≤ n && n ≤ 0x200A) || n == 0x2028 || n == 0x2029 ||
  n == 0x202F || n == 0x205F || n == 0x3000 || n == 0xFEFF

/-- The length of a text in UTF-16 code units. -/
def utf16Length (s : String) : Nat :=
  s.foldl (fun n c => n + if c.toNat > 0xFFFF then 2 else 1) 0

private def hexDigit? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else none

/-- One pass of percent-decoding: each `%` and two hexadecimal digits becomes
the character with that code (a value below 256), left to right, as
`s.replace(/%([a-f0-9]{2})/gi, …)` with `String.fromCharCode`. -/
def decodeOnceAux : List Char → List Char → List Char
  | acc, '%' :: a :: b :: rest =>
      match hexDigit? a, hexDigit? b with
      | some x, some y => decodeOnceAux (Char.ofNat (16 * x + y) :: acc) rest
      | _, _ => decodeOnceAux ('%' :: acc) (a :: b :: rest)
  | acc, c :: rest => decodeOnceAux (c :: acc) rest
  | acc, [] => acc.reverse

def decodeOnce (cs : List Char) : List Char := decodeOnceAux [] cs

#guard String.ofList (decodeOnce "%252e%2E/x%zz".toList) == "%2e./x%zz"

/-- Does `cs` contain `%` followed by the two hexadecimal digits of `code`
(either case)? -/
def hasEncoded (code : Nat) : List Char → Bool
  | '%' :: a :: b :: rest =>
      (hexDigit? a == some (code / 16) && hexDigit? b == some (code % 16)) ||
        hasEncoded code (a :: b :: rest)
  | _ :: rest => hasEncoded code rest
  | [] => false

/-- A scheme at the start: an ASCII letter, then letters, digits, `+`, `-`
or `.`, then `:` (`/^[a-z][a-z0-9+.-]*:/i`). -/
def startsWithScheme : List Char → Bool
  | c :: rest =>
      isAsciiAlphaC c &&
        (let tail := rest.dropWhile (fun d => isAsciiAlphaC d || isAsciiDigitC d ||
          d == '+' || d == '-' || d == '.')
         tail.head? == some ':')
  | [] => false

/-- The structural refusals of one form of a raw path. -/
def structuralFault (cs : List Char) : Option String :=
  if startsWithScheme cs then some "the path has a URL scheme"
  else if cs.any (fun c => c == '\\' || c == '?' || c == '#' || isControl c) then
    some "the path has a backslash, '?', '#' or a control character"
  else if ((String.ofList cs).splitOn "/").any (fun p => p == "" || p == "." || p == "..") then
    some "the path has an empty, '.' or '..' segment"
  else if hasEncoded 0x2F cs || hasEncoded 0x5C cs || hasEncoded 0x3F cs || hasEncoded 0x23 cs then
    some "the path has an encoded '/', '\\', '?' or '#'"
  else none

/-- Check the path, then each text that percent-decoding gives, until a pass
changes nothing. A pass that changes the text shortens it, so `fuel` (the
length plus one) is enough; when it runs out the path is refused. -/
def checkDecoded : Nat → List Char → Option String
  | 0, _ => some "the path has too many levels of percent-encoding"
  | fuel + 1, cs =>
      match structuralFault cs with
      | some e => some e
      | none =>
          let next := decodeOnce cs
          if next == cs then none else checkDecoded fuel next

/-- The refusal of a raw relative path, if any. -/
def rawPathFault (path : String) : Option String :=
  if path.isEmpty then some "the path is empty"
  else if utf16Length path > maxPathLength then
    some s!"the path is longer than {maxPathLength} UTF-16 code units"
  else checkDecoded (path.length + 1) path.toList

/-! ## Encoding -/

/-- The characters `encodeURIComponent` leaves as they are (ECMA-262
§19.2.6.5: uriAlpha, DecimalDigit, uriMark). -/
def isUriUnreserved (c : Char) : Bool :=
  isAsciiAlphaC c || isAsciiDigitC c ||
    c == '-' || c == '_' || c == '.' || c == '!' || c == '~' || c == '*' ||
    c == '\'' || c == '(' || c == ')'

/-- `encodeURIComponent` of a text: every other character as `%XX` of its
UTF-8 bytes, upper-case hexadecimal. -/
def encodeComponent (s : String) : String :=
  s.foldl (fun acc c =>
    if isUriUnreserved c then acc.push c
    else (String.singleton c).toUTF8.foldl (fun a b => a ++ percentEncodeByte b) acc) ""

#guard encodeComponent "a b/é%.nt" == "a%20b%2F%C3%A9%25.nt"
#guard encodeComponent "x!~*'()-_." == "x!~*'()-_."

/-- Each segment of a path encoded, joined by `/`. -/
def encodePath (path : String) : String :=
  "/".intercalate ((path.splitOn "/").map encodeComponent)

/-! ## URLs -/

/-- The origin of a URL text, when it parses. -/
def originOf (s : String) : Option String := (parseUrl s).map Url.origin

/-- The checks of an HTTP(S) target that do not depend on the mode. -/
def httpFault (u : Url) : Option String :=
  if !(u.scheme == "http" || u.scheme == "https") then some "the URL is not http or https"
  else if u.host.isNone then some "the URL has no host"
  else if u.includesCredentials then some "the URL has a username or password"
  else if u.query.isSome || u.fragment.isSome then some "the URL has a query or a fragment"
  else none

/-- The further checks of a canonical target (the input text itself). -/
def canonicalFault (input : String) (u : Url) : Option String :=
  if input.any (fun c => c.toNat ≤ 0x20 || c == '\\') then
    some "the URL has white space, a control character or a backslash"
  else if u.href != input then some "the URL is not its own serialization"
  else
    let p := u.pathname.toList
    if hasEncoded 0x2F p || hasEncoded 0x5C p || hasEncoded 0x2E p || hasEncoded 0x25 p then
      some "the URL path has an encoded '/', '\\', '.' or '%'"
    else none

/-- An HTTP(S) target URL: the text to request. With `canonical` it is the
input; otherwise the serialization of the parsed input. -/
def target (input : String) (canonical : Bool) : Except String String :=
  match parseUrl input with
  | none => .error "the URL is not an absolute URL"
  | some u =>
    match httpFault u with
    | some e => .error e
    | none =>
      if canonical then
        match canonicalFault input u with
        | some e => .error e
        | none => .ok input
      else .ok u.href

/-- A container URL: a target whose path ends with `/` (see the module
note: without `canonical` a `/` is appended when missing). -/
def containerOf (input : String) (canonical : Bool) : Except String String :=
  match target input canonical with
  | .error e => .error e
  | .ok t =>
    if t.toList.getLast? == some '/' then .ok t
    else if canonical then .error "the container URL does not end with '/'"
    else .ok (t ++ "/")

/-- Accept `href` only when it has the origin of `root` and is under `root`
at a segment boundary. -/
def guardUnder (root href : String) : Except String String :=
  if (originOf root).isSome && originOf href == originOf root && underAtSegment root href then
    .ok href
  else .error "the URL is not inside the container"

theorem guardUnder_ok {root href x : String} (h : guardUnder root href = .ok x) :
    x = href ∧ originOf x = originOf root ∧ UnderAtSegment root x := by
  unfold guardUnder at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    cases h
    exact ⟨rfl, hc.1.2, (underAtSegment_iff _ _).1 hc.2⟩
  · cases h

/-- `within root url canonical`: the URL to request, when `url` is inside
the container `root`. -/
def within (root url : String) (canonical : Bool) : Except String String :=
  match containerOf root canonical with
  | .error e => .error e
  | .ok r =>
    match target url canonical with
    | .error e => .error e
    | .ok t => guardUnder r t

/-- `resourceIn container path`: the URL of the raw relative path `path`
inside the container (the LWS reader of an SBM11 generation). -/
def resourceIn (container path : String) : Except String String :=
  match containerOf container false with
  | .error e => .error e
  | .ok c =>
    match rawPathFault path with
    | some e => .error e
    | none =>
      match target (c ++ encodePath path) false with
      | .error e => .error e
      | .ok t => guardUnder c t

/-- The refusal of one name, if any (`segmentIn`). -/
def nameFault (name : String) : Option String :=
  match rawPathFault name with
  | some e => some e
  | none =>
    if name.any (fun c => c == '/' || c == '%') then some "the name has '/' or '%'"
    else if (name.toList.head?.map isJsTrimSpace).getD false ||
        (name.toList.getLast?.map isJsTrimSpace).getD false then
      some "the name has white space at one end"
    else none

/-- `segmentIn root name`: the URL of one name inside the canonical
container `root` (the compositor's new pipeline file). -/
def segmentIn (root name : String) : Except String String :=
  match containerOf root true with
  | .error e => .error e
  | .ok r =>
    match nameFault name with
    | some e => .error e
    | none =>
      match target (r ++ encodeComponent name) true with
      | .error e => .error e
      | .ok t => guardUnder r t

/-! ## Theorems -/

/-- **An answer of `resourceIn` is inside the container**: it has the
container's origin and the container (with its final `/`) is a prefix. -/
theorem resourceIn_under {container path x : String} (h : resourceIn container path = .ok x) :
    ∃ c, containerOf container false = .ok c ∧ originOf x = originOf c ∧ UnderAtSegment c x := by
  unfold resourceIn at h
  split at h
  · cases h
  · rename_i c hc
    split at h
    · cases h
    · split at h
      · cases h
      · obtain ⟨_, ho, hu⟩ := guardUnder_ok h
        exact ⟨c, hc, ho, hu⟩

/-- **An answer of `segmentIn` is inside the root.** -/
theorem segmentIn_under {root name x : String} (h : segmentIn root name = .ok x) :
    ∃ r, containerOf root true = .ok r ∧ originOf x = originOf r ∧ UnderAtSegment r x := by
  unfold segmentIn at h
  split at h
  · cases h
  · rename_i r hr
    split at h
    · cases h
    · split at h
      · cases h
      · obtain ⟨_, ho, hu⟩ := guardUnder_ok h
        exact ⟨r, hr, ho, hu⟩

/-- **When `within` accepts, the URL is inside the root.** -/
theorem within_under {root url x : String} {canonical : Bool}
    (h : within root url canonical = .ok x) :
    ∃ r, containerOf root canonical = .ok r ∧ originOf x = originOf r ∧ UnderAtSegment r x := by
  unfold within at h
  split at h
  · cases h
  · rename_i r hr
    split at h
    · cases h
    · obtain ⟨_, ho, hu⟩ := guardUnder_ok h
      exact ⟨r, hr, ho, hu⟩

theorem target_canonical {input t : String} (h : target input true = .ok t) : t = input := by
  unfold target at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [ite_true] at h
      split at h
      · cases h
      · cases h; rfl

theorem containerOf_canonical {input c : String} (h : containerOf input true = .ok c) :
    c = input := by
  unfold containerOf at h
  split at h
  · cases h
  · rename_i t ht
    split at h
    · cases h; exact target_canonical ht
    · simp at h

theorem within_canonical_target {root url x : String} (h : within root url true = .ok x) :
    x = url := by
  unfold within at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i t ht
      exact (guardUnder_ok h).1.trans (target_canonical ht)

/-- **Canonical `within` compares the texts given**: the root text is a
prefix of the URL text and ends with `/`. -/
theorem within_canonical_under {root url x : String} (h : within root url true = .ok x) :
    x = url ∧ UnderAtSegment root url := by
  have hx := within_canonical_target h
  obtain ⟨r, hr, _, hu⟩ := within_under h
  have := containerOf_canonical hr
  subst this; subst hx
  exact ⟨rfl, hu⟩

/-- **A sibling whose name continues the root's last segment is not within
the root.** -/
theorem within_sibling_refused (x : String) :
    within "https://s.example/alice/" "https://s.example/alice-other/" true ≠ .ok x := by
  intro h
  have := (within_canonical_under h).2
  have hb : underAtSegment "https://s.example/alice/" "https://s.example/alice-other/" = false := by
    decide
  rw [← underAtSegment_iff] at this
  rw [this] at hb
  cases hb

-- Without `canonical`, the sibling is refused too (checked by evaluation).
#guard !(within "https://s.example/alice/" "https://s.example/alice-other/" false).toBool
#guard !(within "https://s.example/alice/" "https://s.example/alice-other/" true).toBool
#guard (within "https://s.example/alice/" "https://s.example/alice/x.json" true).toOption == some "https://s.example/alice/x.json"

/-! ## Cases of the 0.28.0 JavaScript tests -/

#guard (containerOf "https://storage.invalid/container" false).toOption == some "https://storage.invalid/container/"
#guard [ "https://storage.invalid/container?token=secret", "https://storage.invalid/container/#fragment",
    "https://storage.invalid/container/?", "https://storage.invalid/container/#",
    "https://user:secret@storage.invalid/container/", "file:///private/", "data:text/plain,x",
    "not an absolute URL" ].all fun b => !(containerOf b false).toBool
#guard [ "//attacker.invalid/steal", "/private", "https://attacker.invalid/steal",
    "../private", "gen/../../private", ".", "..", "gen/./CURRENT",
    "gen\\private", "\\attacker.invalid\\private", "gen//CURRENT", "",
    "%2e%2e/private", "gen/%2E%2e/private", "%252e%252e/private",
    "gen%2fprivate", "gen%252fprivate", "%2f%2fattacker.invalid/steal",
    "gen%5cprivate", "file?token=x", "file#fragment", "file%3ftoken=x", "file%23fragment",
    "nul\x00file", "line\nfile", "file%00" ].all fun f =>
      !(resourceIn "https://storage.invalid/container/" f).toBool
#guard [ ("CURRENT", "CURRENT"), ("gen/manifest.sbm11", "gen/manifest.sbm11"),
    ("a b/é.nt", "a%20b/%C3%A9.nt"), ("100%.bin", "100%25.bin"),
    ("literal%20name.nt", "literal%2520name.nt") ].all fun (f, e) =>
      (resourceIn "https://storage.invalid/container" f).toOption == some ("https://storage.invalid/container/" ++ e)
#guard !(resourceIn "https://storage.invalid/container/" (String.ofList (List.replicate 4097 'a'))).toBool
#guard (resourceIn "https://storage.invalid/container/" (String.ofList (List.replicate 4096 'a'))).toBool
#guard ["../x", "a/b", "a\\b", "%2e", "a?x", "a#x", ".", "..", "\x01", " a", "a ", "a%b"].all fun n =>
  !(segmentIn "https://pod.example/alice/" n).toBool
#guard (segmentIn "https://pod.example/alice/" "résumé.json").toOption == some "https://pod.example/alice/r%C3%A9sum%C3%A9.json"
#guard ["https://pod.example/alice2/x", "https://elsewhere.example/x", "https://pod.example/alice/../x",
    "https://pod.example/alice/%2e%2e/x", "https://pod.example/alice/%252e/x",
    "https://pod.example/alice/x?token=x", "https://pod.example/alice/x#fragment",
    "https://user:pass@pod.example/alice/x", "https://pod.example/alice/a\\x"].all fun u =>
  !(within "https://pod.example/alice/" u true).toBool
#guard !(containerOf "https://pod.example/alice/no-slash" true).toBool
#guard !(containerOf "https://bad.example/pod/?secret=bad" true).toBool

end L4Factoidal.LWS.ContainerPath
