import L4Factoidal.Encoding.Hex
import L4Factoidal.Syntax.FileIri

/- RFC 3986 resource-path identity, not a URL, query decoder or RDF IRI
   canonicalizer. No production authorization/storage consumer is connected.
   Literal reserved pchars remain distinct from escaped reserved bytes.
   Canonical results carry checked scanner fixed-point evidence; this proves
   public API idempotence, not completeness of admission for every RFC URI. -/
namespace L4Factoidal.HTTP.ResourcePath

/-- RFC 3986 section 2.3 ASCII unreserved characters. -/
def unreserved (c : Char) : Bool :=
  ('A' ≤ c && c ≤ 'Z') || ('a' ≤ c && c ≤ 'z') ||
  ('0' ≤ c && c ≤ '9') || "-._~".toList.contains c

/-- Scan once. The decoded bytes validate UTF-8; only unreserved escapes
   are decoded in the returned URI spelling. A retained `%25` is never rescanned
   as a new escape in this scan. Encoded path separators/NUL are refused. -/
def scan : List Char → String → ByteArray → Option (String × ByteArray)
  | [], out, bytes => some (out,bytes)
  | '%' :: a :: b :: rest, out, bytes => do
    let hi ← L4Factoidal.Encoding.Hex.digitValue a
    let lo ← L4Factoidal.Encoding.Hex.digitValue b
    let value := hi*16+lo
    if value == 0 || value == 47 || value == 92 then none else
      let c := Char.ofNat value
      let out := if unreserved c then out.push c else
        ((out.push '%').push (L4Factoidal.Syntax.upperHexDigit hi)).push (L4Factoidal.Syntax.upperHexDigit lo)
      scan rest out (bytes.push (UInt8.ofNat value))
  | '%' :: _, _, _ => none
  | c :: rest, out, bytes =>
    if c.toNat < 128 && L4Factoidal.Syntax.isFileIriPathChar c then
      scan rest (out.push c) (bytes.push (UInt8.ofNat c.toNat))
    else none

/-- Absolute, nonempty segments except the root or a final collection slash;
   dot segments are refused instead of removed. The caller passes bytes decoded
   exactly once, so escaped unreserved dots cannot bypass this check. -/
inductive SegmentState where
  | empty | dot | dotdot | ordinary
  deriving DecidableEq
private def advance (state : SegmentState) (c : Char) : SegmentState :=
  if c == '.' then match state with
    | .empty => .dot | .dot => .dotdot | _ => .ordinary
  else .ordinary
private def checkSegments : List Char → SegmentState → Bool
  | [], state => state == .empty || state == .ordinary
  | '/' :: rest, state => state == .ordinary && checkSegments rest .empty
  | c :: rest, state => checkSegments rest (advance state c)
def validDecoded (path : String) : Bool :=
  match path.toList with
  | '/' :: rest => checkSegments rest .empty
  | _ => false

/-- Syntax, strict UTF-8 and traversal admission plus one normalization scan.
   Query/fragment input and raw spaces/non-ASCII are not URI path spellings;
   transports must percent-encode them before this boundary. -/
def core (input : String) : Option String := do
  let (out,bytes) ← scan input.toList "" ByteArray.empty
  let decoded ← String.fromUTF8? bytes
  if validDecoded decoded then some out else none

structure CanonicalPath where
  value : String
  stable : core value = some value

/-- A second *validation* scan checks canonicality. It does not recursively
   decode the returned URI or silently replace it with a second result. -/
def normalize (input : String) : Option CanonicalPath :=
  match core input with
  | none => none
  | some value => if h : core value = some value then some ⟨value,h⟩ else none

/-- String boundary for callers without dependent result types. -/
def normalizeText (input : String) : Option String :=
  (normalize input).map (·.value)

theorem normalize_value (input : String) (result : CanonicalPath)
    (accepted : normalize input = some result) : core input = some result.value := by
  unfold normalize at accepted
  cases h : core input with
  | none => simp [h] at accepted
  | some value =>
    simp only [h] at accepted
    split at accepted
    · cases accepted; rfl
    · contradiction

theorem normalize_fixed (result : CanonicalPath) : normalize result.value = some result := by
  simp only [normalize,result.stable]
  split
  · rfl
  · contradiction

theorem normalize_idempotent (input : String) (result : CanonicalPath)
    (_ : normalize input = some result) : normalize result.value = some result :=
  normalize_fixed result

theorem normalizeText_idempotent (input output : String)
    (accepted : normalizeText input = some output) : normalizeText output = some output := by
  unfold normalizeText at accepted
  cases h : normalize input with
  | none => simp [h] at accepted
  | some result =>
    simp only [h,Option.map_some,Option.some.injEq] at accepted
    subst output
    simp [normalizeText,normalize_fixed result]

theorem same_scan (a b : String)
    (h : scan a.toList "" ByteArray.empty = scan b.toList "" ByteArray.empty) :
    normalizeText a = normalizeText b := by
  have eqCore : core a = core b := by unfold core; rw [h]
  unfold normalizeText normalize
  rw [eqCore]

private theorem utf8_roundtrip (s : String) : String.fromUTF8? s.toByteArray = some s := by
  simp only [String.fromUTF8?,dif_pos s.isValidUTF8]
  rfl

theorem core_of_scan (input output decoded : String)
    (scanned : scan input.toList "" ByteArray.empty = some (output,decoded.toUTF8))
    (valid : validDecoded decoded = true) : core input = some output := by
  simp [core,scanned,utf8_roundtrip,valid]

theorem normalizeText_of_core (input output : String)
    (scanned : core input = some output) (stable : core output = some output) :
    normalizeText input = some output := by
  simp [normalizeText,normalize,scanned,stable]

private theorem raw_colon : core "/colon:name" = some "/colon:name" :=
  core_of_scan _ _ "/colon:name" (by decide) (by decide)
private theorem escaped_colon : core "/colon%3Aname" = some "/colon%3Aname" :=
  core_of_scan _ _ "/colon:name" (by decide) (by decide)
private theorem escaped_percent : core "/colon%253Aname" = some "/colon%253Aname" :=
  core_of_scan _ _ "/colon%3Aname" (by decide) (by decide)

-- Kernel checked concrete URI-identity/distinction properties, not native_decide.
theorem unreserved_a_identity : normalizeText "/a" = normalizeText "/%61" := same_scan _ _ (by decide)
theorem escaped_colon_case_identity : normalizeText "/colon%3Aname" = normalizeText "/colon%3aname" := same_scan _ _ (by decide)
theorem reserved_colon_distinct : normalizeText "/colon:name" ≠ normalizeText "/colon%3Aname" := by
  rw [normalizeText_of_core _ _ raw_colon raw_colon,
      normalizeText_of_core _ _ escaped_colon escaped_colon]
  decide
theorem escaped_percent_distinct : normalizeText "/colon%253Aname" ≠ normalizeText "/colon%3Aname" := by
  rw [normalizeText_of_core _ _ escaped_percent escaped_percent,
      normalizeText_of_core _ _ escaped_colon escaped_colon]
  decide

end L4Factoidal.HTTP.ResourcePath
