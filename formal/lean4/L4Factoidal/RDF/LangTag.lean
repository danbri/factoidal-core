/-
L4Factoidal.RDF.LangTag — BCP 47 language-tag WELL-FORMEDNESS.

Spec: RFC 5646 "Tags for Identifying Languages", section 2.1 (the ABNF),
with the grandfathered tags of section 2.2.8. RDF 1.1 Concepts section
3.3 requires the language tag of a literal to be well-formed under
BCP 47; RML-Core (term generation rules, rule 5) raises a data error
when a language map yields a tag that is not.

This module decides WELL-FORMEDNESS only, which is the ABNF. It does not
consult the IANA registry, so `qaa-Qaaa-QM-x-private` and an unassigned
but well-formed `abc` pass, as RFC 5646 section 2.2.9 says they should.

## Why a deterministic walk is enough

The ABNF is ambiguous only where two productions could accept the same
subtag. They cannot: an `extlang` is exactly three letters and a
`region` is two letters or three digits; a `script` is four letters and
a `variant` of four characters starts with a digit; an `extension`
subtag follows a singleton and a `variant` never does. So each subtag
has one possible production and the walk below never backtracks.
-/

namespace L4Factoidal.RDF

private def isAsciiAlpha (c : Char) : Bool :=
  ('a' ≤ c && c ≤ 'z') || ('A' ≤ c && c ≤ 'Z')

private def isAsciiDigit (c : Char) : Bool := '0' ≤ c && c ≤ '9'

private def isAsciiAlnum (c : Char) : Bool := isAsciiAlpha c || isAsciiDigit c

private def allAlpha (s : String) : Bool := s.toList.all isAsciiAlpha
private def allDigit (s : String) : Bool := s.toList.all isAsciiDigit
private def allAlnum (s : String) : Bool := s.toList.all isAsciiAlnum

/-- A subtag is one to eight ASCII letters or digits. -/
private def isSubtag (s : String) : Bool := s.length ≥ 1 && s.length ≤ 8 && allAlnum s

/-- RFC 5646 section 2.2.8: the seventeen irregular and nine regular
    grandfathered tags, compared case-insensitively. -/
def grandfatheredTags : List String :=
  [ "en-gb-oed", "i-ami", "i-bnn", "i-default", "i-enochian", "i-hak"
  , "i-klingon", "i-lux", "i-mingo", "i-navajo", "i-pwn", "i-tao", "i-tay"
  , "i-tsu", "sgn-be-fr", "sgn-be-nl", "sgn-ch-de"
  , "art-lojban", "cel-gaulish", "no-bok", "no-nyn", "zh-guoyu", "zh-hakka"
  , "zh-min", "zh-min-nan", "zh-xiang" ]

/-- `privateuse = "x" 1*("-" (1*8alphanum))`, given the subtags AFTER the
    `x`. -/
private def privateUseTail (rest : List String) : Bool :=
  !rest.isEmpty && rest.all isSubtag

/-- `extension = singleton 1*("-" (2*8alphanum))` repeated, then an
    optional `privateuse`. `rest` starts at a subtag that is already known
    to be a singleton other than `x`, or at `x`, or is empty. -/
private def extensionsAndPrivate : Nat → List String → Bool
  | 0, _ => false
  | _, [] => true
  | fuel + 1, s :: rest =>
      if s.toLower == "x" then privateUseTail rest
      else if s.length == 1 && isAsciiAlnum (s.toList.headD ' ') then
        -- one or more extension subtags of length 2..8, then the next
        -- singleton (or the end)
        let body := rest.takeWhile (fun t => t.length ≥ 2)
        let after := rest.dropWhile (fun t => t.length ≥ 2)
        !body.isEmpty && body.all isSubtag && extensionsAndPrivate fuel after
      else false

/-- `variant = 5*8alphanum / (DIGIT 3alphanum)`. -/
private def isVariant (s : String) : Bool :=
  allAlnum s &&
    ((s.length ≥ 5 && s.length ≤ 8) ||
     (s.length == 4 && isAsciiDigit (s.toList.headD ' ')))

private def variantsThenRest (rest : List String) : Bool :=
  let vs := rest.takeWhile isVariant
  extensionsAndPrivate (rest.length + 1) (rest.drop vs.length)

private def afterScript (rest : List String) : Bool :=
  match rest with
  | [] => true
  | r :: tl =>
      if (r.length == 2 && allAlpha r) || (r.length == 3 && allDigit r)
      then variantsThenRest tl
      else variantsThenRest rest

private def afterExtlang (rest : List String) : Bool :=
  match rest with
  | [] => true
  | s :: tl =>
      if s.length == 4 && allAlpha s then afterScript tl else afterScript rest

/-- `language = 2*3ALPHA ["-" extlang] / 4ALPHA / 5*8ALPHA`, with
    `extlang = 3ALPHA *2("-" 3ALPHA)`. -/
private def langtagWalk (subtags : List String) : Bool :=
  match subtags with
  | [] => false
  | lang :: rest =>
      if !allAlpha lang then false
      else if lang.length == 2 || lang.length == 3 then
        let ext := (rest.takeWhile (fun t => t.length == 3 && allAlpha t)).take 3
        afterExtlang (rest.drop ext.length)
      else if lang.length ≥ 4 && lang.length ≤ 8 then afterExtlang rest
      else false

/-- Is the string a well-formed BCP 47 language tag (RFC 5646 section
    2.2.9, "well-formed")? The empty string is not. -/
def isWellFormedLangTag (tag : String) : Bool :=
  if tag.isEmpty then false
  else if grandfatheredTags.contains tag.toLower then true
  else
    let subtags := tag.splitOn "-"
    if !subtags.all isSubtag then false
    else
      match subtags with
      | [] => false
      | first :: rest =>
          if first.toLower == "x" then privateUseTail rest
          else langtagWalk subtags

/-! ## Build-time checks

Positive cases come from RFC 5646 appendix A; the negative ones are the
shapes each production rejects, so a recogniser that answers `true` for
everything fails here. -/

-- RFC 5646 appendix A: simple language subtag, with script, with region.
#guard isWellFormedLangTag "de"
#guard isWellFormedLangTag "fr"
#guard isWellFormedLangTag "ja"
#guard isWellFormedLangTag "zh-Hant"
#guard isWellFormedLangTag "zh-Hans-CN"
#guard isWellFormedLangTag "sr-Latn-RS"
#guard isWellFormedLangTag "de-CH"
#guard isWellFormedLangTag "es-419"
-- extlang, variant, extension, private use, grandfathered.
#guard isWellFormedLangTag "zh-cmn-Hans-CN"
#guard isWellFormedLangTag "sl-rozaj-biske"
#guard isWellFormedLangTag "de-CH-1901"
#guard isWellFormedLangTag "en-a-bbb-x-a-ccc"
#guard isWellFormedLangTag "x-whatever"
#guard isWellFormedLangTag "qaa-Qaaa-QM-x-southern"
#guard isWellFormedLangTag "i-klingon"
#guard isWellFormedLangTag "en-GB-oed"
-- Case does not matter for well-formedness.
#guard isWellFormedLangTag "EN-gb"
-- The corpus's own tags.
#guard isWellFormedLangTag "en"
#guard isWellFormedLangTag "es"
#guard isWellFormedLangTag "en-GB"

-- The invalid tag of RMLTC0015b: a one-letter language subtag.
#guard !isWellFormedLangTag "a-english"
#guard !isWellFormedLangTag "a-spanish"
-- Empty tag, empty subtag, over-long subtag, bad characters.
#guard !isWellFormedLangTag ""
#guard !isWellFormedLangTag "en-"
#guard !isWellFormedLangTag "-en"
#guard !isWellFormedLangTag "en--GB"
#guard !isWellFormedLangTag "abcdefghi"
#guard !isWellFormedLangTag "en_GB"
#guard !isWellFormedLangTag "en GB"
#guard !isWellFormedLangTag "1en"
-- A private-use subtag with nothing after the singleton.
#guard !isWellFormedLangTag "x"
#guard !isWellFormedLangTag "en-x"
-- An extension singleton with no subtag after it.
#guard !isWellFormedLangTag "en-a"
-- Four extlang-shaped subtags is one too many.
#guard !isWellFormedLangTag "abc-def-ghi-jkl-mno"
-- A region that is neither two letters nor three digits, and a lone
-- singleton with nothing after it.
#guard !isWellFormedLangTag "en-12"
#guard !isWellFormedLangTag "en-1"

end L4Factoidal.RDF
