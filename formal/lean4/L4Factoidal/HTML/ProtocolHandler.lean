/-
L4Factoidal.HTML.ProtocolHandler — `navigator.registerProtocolHandler` and
`unregisterProtocolHandler` (HTML §8.9.1.3 "custom scheme handlers"): the "normalize
protocol handler parameters" steps that decide whether a page may ask for a handler.

The scheme is lowercased (ASCII only) and must be a safelisted scheme or `web+` followed by
one or more ASCII lower alphas (else a "SecurityError"); the URL must contain `%s` (else a
"SyntaxError"), parse against the document's URL (else a "SyntaxError"), and be an HTTP(S)
URL of the document's origin (else a "SecurityError"). The order of the checks is the
spec's: a bad scheme wins over a bad URL.

This browser keeps no handlers: a call that passes the checks does nothing more (the spec
lets a user agent ignore a registration).
-/
import L4Factoidal.WHATWG.URL.Parser

namespace L4Factoidal.HTML.ProtocolHandler
open L4Factoidal.WHATWG.URL

/-- HTML §8.9.1.3: the safelisted schemes. -/
def safelisted : List String :=
  ["bitcoin", "ftp", "ftps", "geo", "im", "irc", "ircs", "magnet", "mailto", "matrix", "mms",
   "news", "nntp", "openpgp4fpr", "sftp", "sip", "sms", "smsto", "ssh", "tel", "urn", "webcal",
   "wtai", "xmpp"]

def asciiLowerChar (c : Char) : Char := if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

def asciiLower (s : String) : String := s.map asciiLowerChar

def isLowerAlpha (c : Char) : Bool := 'a' ≤ c && c ≤ 'z'

/-- A `web+` scheme: `web+` and one or more ASCII lower alphas. -/
def webPlus (s : String) : Bool :=
  match s.toList with
  | 'w' :: 'e' :: 'b' :: '+' :: rest => !rest.isEmpty && rest.all isLowerAlpha
  | _ => false

/-- Step 2: the scheme (already lowercased) may have a handler. -/
def schemeAllowed (lower : String) : Bool := safelisted.contains lower || webPlus lower

inductive Outcome where
  | ok (scheme url : String)
  | securityError
  | syntaxError
  deriving Repr, BEq, DecidableEq

/-- Step 6: an HTTP(S) URL of the document's (tuple) origin. -/
def sameOriginHttp (docURL : String) (u : Url) : Bool :=
  (u.scheme == "http" || u.scheme == "https") &&
    match parseUrl docURL none with
    | some d => d.origin != "null" && d.origin == u.origin
    | none => false

/-- "Normalize protocol handler parameters" for a document whose URL is `docURL`. -/
def normalize (docURL scheme url : String) : Outcome :=
  if !schemeAllowed (asciiLower scheme) then .securityError
  else if (url.splitOn "%s").length < 2 then .syntaxError
  else match parseUrl url (some docURL) with
    | none => .syntaxError
    | some u => if sameOriginHttp docURL u then .ok (asciiLower scheme) u.serialize else .securityError

/-- node_query 198: `q` is the document's URL, U+0000, the scheme, U+0000, the URL; "" when
the call may go on, "S" for a "SecurityError", "Y" for a "SyntaxError". -/
def answer (q : String) : String :=
  match q.splitOn "\x00" with
  | doc :: scheme :: rest =>
    match normalize doc scheme ("\x00".intercalate rest) with
    | .ok _ _ => ""
    | .securityError => "S"
    | .syntaxError => "Y"
  | _ => "Y"

/-! ## What is proved -/

/-- Safety (a policy decision refuses what it must). Says: a scheme that is neither
safelisted nor `web+` never passes, whatever the URL. -/
theorem refused_scheme (doc scheme url : String) (h : schemeAllowed (asciiLower scheme) = false) :
    normalize doc scheme url = .securityError := by
  unfold normalize
  simp [h]

/-- Safety. Says: a registration that passes names the lowercased scheme, which is allowed,
and a URL of the HTTP(S) schemes. -/
theorem ok_sound (doc scheme url s u : String) (h : normalize doc scheme url = .ok s u) :
    s = asciiLower scheme ∧ schemeAllowed s = true := by
  unfold normalize at h
  by_cases ha : schemeAllowed (asciiLower scheme) = true
  · rw [if_neg (by simp [ha])] at h
    by_cases hp : (url.splitOn "%s").length < 2
    · rw [if_pos hp] at h; cases h
    · rw [if_neg hp] at h
      cases hu : parseUrl url (some doc) with
      | none => rw [hu] at h; cases h
      | some v =>
        rw [hu] at h; simp only at h
        by_cases hs : sameOriginHttp doc v = true
        · rw [if_pos hs] at h; cases h; exact ⟨rfl, ha⟩
        · rw [if_neg hs] at h; cases h
  · rw [if_pos (by simpa using ha)] at h; cases h

/-- Says: a URL without `%s` is refused (when the scheme is allowed, as a "SyntaxError"). -/
theorem needs_placeholder (doc scheme url : String) (h : (url.splitOn "%s").length < 2) :
    ∀ s u, normalize doc scheme url ≠ .ok s u := by
  intro s u
  unfold normalize
  by_cases ha : schemeAllowed (asciiLower scheme) = true
  · rw [if_neg (by simp [ha]), if_pos h]; simp
  · rw [if_pos (by simpa using ha)]; simp

/-- Says: what passes is an HTTP(S) URL of the document's origin. -/
theorem ok_same_origin (doc scheme url s u : String) (h : normalize doc scheme url = .ok s u) :
    ∃ v, parseUrl url (some doc) = some v ∧ sameOriginHttp doc v = true ∧ u = v.serialize := by
  unfold normalize at h
  by_cases ha : schemeAllowed (asciiLower scheme) = true
  · rw [if_neg (by simp [ha])] at h
    by_cases hp : (url.splitOn "%s").length < 2
    · rw [if_pos hp] at h; cases h
    · rw [if_neg hp] at h
      cases hu : parseUrl url (some doc) with
      | none => rw [hu] at h; cases h
      | some v =>
        rw [hu] at h; simp only at h
        by_cases hs : sameOriginHttp doc v = true
        · rw [if_pos hs] at h; cases h; exact ⟨v, rfl, hs, rfl⟩
        · rw [if_neg hs] at h; cases h
  · rw [if_pos (by simpa using ha)] at h; cases h

/-! ## Tests (html/webappapis/system-state-and-capabilities/the-navigator-object/protocol.https.html) -/

private def doc := "https://web-platform.test:8443/html/protocol.https.html"
#guard ["%s", "foo/%s", "%s" ++ doc, doc ++ "/%s", doc ++ "#%s", doc ++ "?foo=%s&bar", doc ++ "/%s/foo/%s/",
  "https://web-platform.test:8443/%s"].all fun u => normalize doc "tel" u matches .ok "tel" _
#guard ["", "%S", doc, doc ++ "/%", doc ++ "/%a", "http://example.com", "https://test:test/"].all
  fun u => normalize doc "mailto" u == .syntaxError && normalize doc "x" u == .securityError
#guard ["http://%s.com", "http://[v8.:::]//url=%s", "https://web-platform.test:%s8443/x"].all
  fun u => normalize doc "mailto" u == .syntaxError
#guard ["http://example.com/%s", "https://example.com/%s", "mailto:%s@example.com", "mailto:%s",
  "foo://web-platform.test:8443/%s", "http://web-platform.test:8443/%s"].all
  fun u => normalize doc "mailto" u == .securityError
#guard ["about", "blob", "http", "javascript", "unrecognized", "mаilto", "mailto:", "web+", "web+1",
  "web+namewithtrailingspace ", "web+préfixewithaccent", "web+\u212Aelvinsign", "web+dots.are.forbidden",
  "fweb+oo", "tel:sip"].all fun s => normalize doc s "https://test:test/" == .securityError
#guard ["bitcoin", "BitcoIn", "TEL", "WebCAL", "web+myprotocol", "WEB+seeabove", "WeB+SeEaBoVe",
  "web+abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ"].all fun s => normalize doc s (doc ++ "/%s") matches .ok _ _
#guard answer (doc ++ "\x00tel\x00%s") == "" && answer (doc ++ "\x00tel\x00x") == "Y" && answer (doc ++ "\x00x\x00%s") == "S"

end L4Factoidal.HTML.ProtocolHandler
