/-
L4Factoidal.Net.Integrity — Subresource Integrity
(https://w3c.github.io/webappsec-subresource-integrity/): §3.3.2 "parse metadata", §3.3.3
"get the strongest metadata from set", §3.3.4 "do bytes match metadataList", as `fetch`'s
`integrity` and the `integrity` attribute use them.

## Decisions

* The digests are the engine's SHA-2 from HACL* (`Crypto.WebHacl.hashFast`); nothing is
  computed by code of this file. The check takes the hash as an argument (`okWith`) so that
  the `#guard`s below can run on the specification's SHA-2 at build time.
* Algorithms: `sha256`, `sha384`, `sha512`, by ASCII case-insensitive name. Any other token
  is skipped, as the standard says, so a list that names only unknown algorithms is "no
  metadata" and matches. `sha1` and `md5` are not algorithms here.
* A value is compared as bytes: the expected text is read as base64 or base64url, with or
  without padding (as browsers read it; WPT fetch/api/basic/integrity.sub.any.js). A value
  that is not base64 matches nothing.
* A response that the page may not read (opaque) never matches a non-empty metadata list:
  the engine does not tell a page whether another origin's bytes have a given digest.

## What is proved

`okWith_strongest`: when the list names a known algorithm, the check holds only if the body's
digest under the strongest named algorithm equals a value listed for that algorithm: a weaker
digest that matches is not enough. `okWith_empty`: no metadata matches every body.
-/
import L4Factoidal.Crypto.WebHacl
import L4Factoidal.WHATWG.Base64

namespace L4Factoidal.Net.Integrity
open L4Factoidal.Crypto.WebHacl (HashAlg)
open L4Factoidal.WHATWG

/-- ASCII lower case. -/
def lower (s : String) : String :=
  s.map fun c => if 'A' ≤ c ∧ c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- The algorithm of a token's prefix. -/
def algOf (name : String) : Option HashAlg :=
  match lower name with
  | "sha256" => some .sha256
  | "sha384" => some .sha384
  | "sha512" => some .sha512
  | _ => none

/-- The strength order of the algorithms (§3.3.3: SHA-512 over SHA-384 over SHA-256). -/
def strength : HashAlg → Nat
  | .sha1 => 0
  | .sha256 => 1
  | .sha384 => 2
  | .sha512 => 3

/-- One token `alg-value[?options]` as its algorithm and the bytes of its value; `none` for
an unknown algorithm or a token with no `-`. A value that is not base64 is kept as `none`
bytes: it is a named algorithm that matches nothing. -/
def entryOf (token : String) : Option (HashAlg × Option ByteArray) :=
  match token.splitOn "-" with
  | name :: rest@(_ :: _) =>
    match algOf name with
    | none => none
    | some a =>
      -- the value is all after the first `-` (base64url values have their own), up to `?`
      let value := (("-".intercalate rest).splitOn "?").headD ""
      let std := value.map fun c => if c == '-' then '+' else if c == '_' then '/' else c
      some (a, Base64.decode std)
  | _ => none

/-- §3.3.2 "parse metadata": the tokens of the text (split on ASCII whitespace) that name a
known algorithm. -/
def parse (metadata : String) : List (HashAlg × Option ByteArray) :=
  ((metadata.split fun c => c == ' ' || c == '\t' || c == '\n' || c == '\x0c' || c == '\r').toList.map (·.toString)).filterMap entryOf

/-- The strongest algorithm a list names (§3.3.3). -/
def strongest (entries : List (HashAlg × Option ByteArray)) : Option HashAlg :=
  entries.foldl (fun best e => match best with
    | none => some e.1
    | some b => if strength e.1 > strength b then some e.1 else some b) none

/-- §3.3.4 "do bytes match metadataList" with `hash` as the digest function: no metadata
matches; else the body's digest under the strongest named algorithm is one of the values
listed for it. -/
def okWith (hash : HashAlg → ByteArray → ByteArray) (metadata : String) (body : ByteArray) : Bool :=
  let entries := parse metadata
  match strongest entries with
  | none => true
  | some a =>
    let digest := hash a body
    entries.any fun e => decide (e.1 = a) && decide (e.2 = some digest)

/-- The check the engine makes: with HACL*'s SHA-2. -/
def ok (metadata : String) (body : ByteArray) : Bool := okWith L4Factoidal.Crypto.WebHacl.hashFast metadata body

/-- The check for a response of `tainting` (`basic`, `cors`, `opaque`): an opaque response
matches only "no metadata". -/
def okFor (metadata : String) (tainting : String) (body : ByteArray) : Bool :=
  if (strongest (parse metadata)).isNone then true
  else tainting != "opaque" && tainting != "opaqueredirect" && ok metadata body

/-! ## Theorems -/

/-- Kind: lemma. Says: a list with no known algorithm matches every body. -/
theorem okWith_empty (hash : HashAlg → ByteArray → ByteArray) (metadata : String) (body : ByteArray)
    (h : strongest (parse metadata) = none) : okWith hash metadata body = true := by
  simp [okWith, h]

/-- Kind: security theorem (integrity). Says: when the metadata names a known algorithm, the
check holds only if some listed value of the strongest named algorithm is exactly the
body's digest under that algorithm: a body that matches only a weaker digest, or a value
that is not base64, does not pass. Does not say: that `hash` is SHA-2 (the engine passes
HACL*'s, `ok`), nor anything of metadata with no known algorithm (`okWith_empty`). -/
theorem okWith_strongest (hash : HashAlg → ByteArray → ByteArray) (metadata : String) (body : ByteArray)
    (a : HashAlg) (hs : strongest (parse metadata) = some a) (h : okWith hash metadata body = true) :
    ∃ e ∈ parse metadata, e.1 = a ∧ e.2 = some (hash a body) := by
  simp only [okWith, hs, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨e, he, h1, h2⟩ := h
  exact ⟨e, he, h1, h2⟩

/-- Kind: security theorem (opaque responses). Says: for a response the page may not read,
the check holds only when the metadata names no known algorithm: a page learns nothing of
another origin's bytes from an integrity check. -/
theorem okFor_opaque (metadata : String) (body : ByteArray) (h : okFor metadata "opaque" body = true) :
    strongest (parse metadata) = none := by
  unfold okFor at h
  split at h
  · rename_i hn
    simpa using hn
  · simp at h

/-! ## Checks (WPT fetch/api/basic/integrity.sub.any.js; the body is fetch/api/resources/top.txt) -/

private def spec (a : HashAlg) (b : ByteArray) : ByteArray := a.pure.run b
private def top : ByteArray := "top".toUTF8
private def topSha256 : String := "sha256-KHIDZcXnR2oBHk9DrAA+5fFiR6JjudYjqoXtMR1zvzk="
private def topSha384 : String := "sha384-MgZYnnAzPM/MjhqfOIMfQK5qcFvGZsGLzx4Phd7/A8fHTqqLqXqKo8cNzY3xEPTL"
private def topSha512 : String := "sha512-D6yns0qxG0E7+TwkevZ4Jt5t7Iy3ugmAajG/dlf6Pado1JqTyneKXICDiqFIkLMRExgtvg8PlxbKTkYfRejSOg=="
private def invalidSha256 : String := "sha256-dKUcPOn/AlUjWIwcHeHNqYXPlvyGiq+2dWOdFcE+24I="
private def invalidSha512 : String := "sha512-oUceBRNxPxnY60g/VtPCj2syT4wo4EZh2CgYdWy9veW8+OsReTXoh7dizMGZafvx9+QhMS39L/gIkxnPIn41Zg=="

#guard okWith spec "" top
#guard okWith spec topSha256 top && okWith spec topSha384 top && okWith spec topSha512 top
-- missing padding, base64url, base64url without padding
#guard okWith spec "sha512-D6yns0qxG0E7+TwkevZ4Jt5t7Iy3ugmAajG/dlf6Pado1JqTyneKXICDiqFIkLMRExgtvg8PlxbKTkYfRejSOg" top
#guard okWith spec "sha512-D6yns0qxG0E7-TwkevZ4Jt5t7Iy3ugmAajG_dlf6Pado1JqTyneKXICDiqFIkLMRExgtvg8PlxbKTkYfRejSOg==" top
#guard okWith spec "sha512-D6yns0qxG0E7-TwkevZ4Jt5t7Iy3ugmAajG_dlf6Pado1JqTyneKXICDiqFIkLMRExgtvg8PlxbKTkYfRejSOg" top
#guard !okWith spec invalidSha256 top
-- "valid stronger than invalid", "invalid stronger than valid", "invalid as strong as valid"
#guard okWith spec (invalidSha256 ++ " " ++ topSha384) top
#guard !okWith spec (invalidSha512 ++ " " ++ topSha384) top
#guard okWith spec (invalidSha512 ++ " " ++ topSha512) top
#guard okWith spec (topSha384 ++ " " ++ topSha512) top
#guard !okWith spec (invalidSha256 ++ " " ++ invalidSha512) top
-- unknown algorithms are skipped; options after `?` are not part of the value
#guard okWith spec "md5-abc sha1-abc foo" top && okWith spec (topSha256 ++ "?opt=1") top
#guard okWith spec "SHA256-KHIDZcXnR2oBHk9DrAA+5fFiR6JjudYjqoXtMR1zvzk=" top
#guard !okWith spec "sha256-!!!" top
#guard (parse "sha256-abc  sha512-def\tfoo-x").length == 2

end L4Factoidal.Net.Integrity
