/-
L4Factoidal.WHATWG.Encoding.Sniff — the encoding of an HTML document from its bytes,
and the document's text decoded with it (HTML Standard §13.2.3 "The input byte stream",
§13.2.3.2 "Determining the character encoding").

What a host calls where page or frame bytes become text: `decodeDocument bytes charset`
gives the document's encoding and its text, decoded by the Encoding Standard's decoders
(`Core.decode`: BOM sniff, then the encoding's decoder in replacement mode).

  * `prescan` — "prescan a byte stream to determine its encoding" (§13.2.3.2), over the
    first 1024 bytes: comments, `<meta>` attributes (`charset`, and `http-equiv`
    content-type with a charset in `content`, by "extract a character encoding from a
    meta element"), other tags' attributes skipped. UTF-16 is UTF-8 and x-user-defined is
    windows-1252.
  * `sniff` — the "encoding sniffing algorithm" (§13.2.3.2): the BOM, the transport
    layer's charset (HTTP `Content-Type`), the prescan; then the user's setting for pages
    that declare nothing (`Fallback`): "detect" (the default) is UTF-8 for bytes that are
    UTF-8 and otherwise the default of the user's locale; "locale" is always the locale's
    default; or one encoding. The locale's default is §13.2.3.2's table of suggested
    defaults by locale (`localeEncoding`).

No `partial`, no `sorry`. Every loop is a `for` over a bounded range.
-/
import L4Factoidal.WHATWG.Encoding.Core

namespace L4Factoidal.WHATWG.Encoding.Sniff

open L4Factoidal.WHATWG.Encoding

def isWs (b : UInt8) : Bool := b == 0x09 || b == 0x0A || b == 0x0C || b == 0x0D || b == 0x20
def isAlpha (b : UInt8) : Bool := (0x41 ≤ b && b ≤ 0x5A) || (0x61 ≤ b && b ≤ 0x7A)
def lowerB (b : UInt8) : UInt8 := if 0x41 ≤ b && b ≤ 0x5A then b + 0x20 else b

/-- The bytes as characters U+0000 to U+00FF (isomorphic decode). -/
def iso (bs : Array UInt8) : String := bs.foldl (fun s b => s.push (Char.ofNat b.toNat)) ""

/-- Whether the bytes at `pos` are `pat`, ASCII case-insensitively. -/
def at? (b : ByteArray) (pos : Nat) (pat : String) : Bool :=
  let ps := pat.toUTF8
  pos + ps.size ≤ b.size && (List.range ps.size).all fun i => lowerB b[pos + i]! == ps[i]!

/-- §13.2.3.2 "get an attribute": the attribute (name, value) at `pos` and the position
after it, or `none` at `>` or the end. -/
def getAttribute (b : ByteArray) (pos0 : Nat) : Option (String × String) × Nat := Id.run do
  let n := b.size
  let mut pos := pos0
  -- 1. Skip whitespace and `/`.
  for _ in [0:n] do
    if pos < n && (isWs b[pos]! || b[pos]! == 0x2F) then pos := pos + 1 else break
  if pos ≥ n then return (none, pos)
  -- 2. `>` ends the attributes.
  if b[pos]! == 0x3E then return (none, pos)
  -- 3 to 5. The name.
  let mut name : Array UInt8 := #[]
  let mut sawEq := false
  for _ in [0:n] do
    if pos ≥ n then break
    let c := b[pos]!
    if c == 0x3D && !name.isEmpty then
      pos := pos + 1; sawEq := true; break
    if isWs c then break
    if c == 0x2F || c == 0x3E then return (some (iso name, ""), pos)
    name := name.push (lowerB c); pos := pos + 1
  if pos ≥ n then return (some (iso name, ""), pos)
  if !sawEq then
    -- 6. Spaces, then `=` or an attribute with no value.
    for _ in [0:n] do
      if pos < n && isWs b[pos]! then pos := pos + 1 else break
    if pos ≥ n || b[pos]! != 0x3D then return (some (iso name, ""), pos)
    pos := pos + 1
  -- 8. Spaces before the value.
  for _ in [0:n] do
    if pos < n && isWs b[pos]! then pos := pos + 1 else break
  if pos ≥ n then return (some (iso name, ""), pos)
  -- 9 and 10. The value.
  let mut value : Array UInt8 := #[]
  let q := b[pos]!
  if q == 0x22 || q == 0x27 then
    pos := pos + 1
    for _ in [0:n] do
      if pos ≥ n then break
      if b[pos]! == q then return (some (iso name, iso value), pos + 1)
      value := value.push (lowerB b[pos]!); pos := pos + 1
    return (some (iso name, iso value), pos)
  if q == 0x3E then return (some (iso name, ""), pos)
  for _ in [0:n] do
    if pos ≥ n then break
    let c := b[pos]!
    if isWs c || c == 0x3E then break
    value := value.push (lowerB c); pos := pos + 1
  return (some (iso name, iso value), pos)

/-- HTML §2.5 "algorithm for extracting a character encoding from a meta element". -/
def extractFromMeta (content : String) : Option String :=
  let cs := content.toList
  let ws := fun (c : Char) => c == '\t' || c == '\n' || c == '\x0C' || c == '\r' || c == ' '
  let lower := fun (c : Char) => if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c
  let rec go (fuel : Nat) (xs : List Char) : Option String :=
    match fuel, xs with
    | 0, _ | _, [] => none
    | fuel + 1, _ :: rest =>
      if (xs.take 7).map lower != "charset".toList then go fuel rest else
      match (xs.drop 7).dropWhile ws with
      | '=' :: more =>
        match more.dropWhile ws with
        | q :: tail =>
          if q == '"' || q == '\'' then
            if tail.contains q then some (String.ofList (tail.takeWhile (· != q))) else none
          else
            let v := (q :: tail).takeWhile (fun c => !ws c && c != ';')
            if v.isEmpty then none else some (String.ofList v)
        | [] => none
      | _ => go fuel (xs.drop 7)
  go (cs.length + 1) cs

/-- The encoding a `meta` element's attributes declare (§13.2.3.2, the steps after the
attributes), or `none`. -/
def metaEncoding (attrs : Array (String × String)) : Option Encoding := Id.run do
  let mut gotPragma := false
  let mut needPragma : Option Bool := none
  let mut charset : Option Encoding := none
  let mut seen : Array String := #[]
  for (name, value) in attrs do
    if seen.contains name then continue
    seen := seen.push name
    if name == "http-equiv" then
      if value == "content-type" then gotPragma := true
    else if name == "content" then
      if charset.isNone then
        if let some l := extractFromMeta value then
          if let some e := getEncoding l then
            charset := some e; needPragma := some true
    else if name == "charset" then
      charset := getEncoding value; needPragma := some false
  match needPragma, charset with
  | none, _ | _, none => return none
  | some true, _ => if !gotPragma then return none
  | _, _ => pure ()
  return charset.map fun e => match e with
    | .utf_16be | .utf_16le => .utf_8
    | .x_user_defined => .windows_1252
    | e => e

/-- §13.2.3.2 "prescan a byte stream to determine its encoding", over the first 1024
bytes. -/
def prescan (input : ByteArray) : Option Encoding := Id.run do
  let b := input.extract 0 (min 1024 input.size)
  let n := b.size
  let mut pos := 0
  for _ in [0:n + 1] do
    if pos ≥ n then break
    if at? b pos "<!--" then
      -- Advance to the end of the comment: the `-->`, which may share the `--` of `<!--`.
      let mut p := pos + 2
      for _ in [0:n] do
        if p + 3 > n then p := n; break
        if at? b p "-->" then p := p + 3; break
        p := p + 1
      pos := p
    else if at? b pos "<meta" && pos + 5 < n && (isWs b[pos + 5]! || b[pos + 5]! == 0x2F) then
      pos := pos + 6
      let mut attrs : Array (String × String) := #[]
      for _ in [0:n] do
        let (a, p) := getAttribute b pos
        match a with
        | some kv => attrs := attrs.push kv; pos := max p (pos + 1)
        | none => pos := p; break
      if let some e := metaEncoding attrs then return some e
      pos := pos + 1
    else if pos + 1 < n && b[pos]! == 0x3C &&
        (isAlpha b[pos + 1]! || (b[pos + 1]! == 0x2F && pos + 2 < n && isAlpha b[pos + 2]!)) then
      -- A tag: skip its name, then its attributes.
      let mut p := pos + 1
      for _ in [0:n] do
        if p < n && !(isWs b[p]! || b[p]! == 0x3E) then p := p + 1 else break
      for _ in [0:n] do
        let (a, q) := getAttribute b p
        match a with
        | some _ => p := max q (p + 1)
        | none => p := q; break
      pos := p + 1
    else if at? b pos "<!" || at? b pos "</" || at? b pos "<?" then
      let mut p := pos + 2
      for _ in [0:n] do
        if p < n && b[p]! != 0x3E then p := p + 1 else break
      pos := p + 1
    else pos := pos + 1
  return none

/-! ## The default for pages that declare nothing -/

/-- The suggested default encoding of a locale: HTML §13.2.3.2, the table "derived from
the intersection of Windows, Chrome, and Firefox defaults". `locale` is a BCP 47 tag
(`ja-JP`, `zh-Hant-TW`) or a POSIX one (`ja_JP.UTF-8`); the language subtag decides,
and for Chinese the script or region (`zh-Hans`, `zh-CN`, `zh-SG`: GBK; `zh-Hant`,
`zh-HK`, `zh-MO`, `zh-TW`: Big5). All other locales: windows-1252. -/
def localeEncoding (locale : String) : Encoding :=
  let tag := (locale.toList.takeWhile fun c => c != '.' && c != '@').map fun c =>
    if c == '_' then '-' else if 'A' ≤ c && c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c
  match (String.ofList tag).splitOn "-" with
  | [] => .windows_1252
  | lang :: rest =>
    if lang == "zh" then
      if rest.any (["hant", "hk", "mo", "tw"].contains ·) then .big5
      else if rest.any (["hans", "cn", "sg"].contains ·) then .gbk
      else .windows_1252
    else match lang with
      | "ar" | "fa" => .windows_1256
      | "az" | "ku" | "tr" => .windows_1254
      | "ba" | "be" | "bg" | "kk" | "ky" | "mk" | "ru" | "sah" | "sr" | "tg" | "tt" | "uk" => .windows_1251
      | "cs" | "hr" | "sk" => .windows_1250
      | "el" => .iso_8859_7
      | "et" | "lt" | "lv" => .windows_1257
      | "he" => .windows_1255
      | "hu" | "pl" | "sl" => .iso_8859_2
      | "ja" => .shift_jis
      | "ko" => .euc_kr
      | "th" => .windows_874
      | "vi" => .windows_1258
      | _ => .windows_1252

/-- What a page that declares no encoding is read as (the user's setting). -/
inductive Fallback where
  /-- UTF-8 when the bytes are UTF-8, else the locale's default. -/
  | detect
  /-- The locale's default (`localeEncoding`). -/
  | locale
  /-- One encoding. -/
  | fixed (e : Encoding)
  deriving DecidableEq, Repr, Inhabited

/-- The setting's text: "" or "detect", "locale", or an encoding's label. A label that
names no encoding, and "replacement", are "detect". -/
def Fallback.ofSetting (s : String) : Fallback :=
  if s.isEmpty || s == "detect" then .detect
  else if s == "locale" then .locale
  else match getEncoding s with
    | some .replacement | none => .detect
    | some e => .fixed e

/-- The setting as it is stored: "detect", "locale" or the encoding's name. -/
def Fallback.setting : Fallback → String
  | .detect => "detect"
  | .locale => "locale"
  | .fixed e => e.name

/-- The encoding sniffing algorithm (§13.2.3.2) as this engine runs it: the BOM, the
transport layer's charset label, the prescan, then the user's fallback. -/
def sniff (bytes : ByteArray) (transportCharset : Option String := none) (fallback : Fallback := .detect)
    (locale : String := "") : Encoding :=
  match bomSniff bytes with
  | some e => e
  | none =>
    match transportCharset.bind getEncoding with
    | some e => e
    | none =>
      match prescan bytes with
      | some e => e
      | none =>
        match fallback with
        | .detect => if ByteArray.validateUTF8 bytes then .utf_8 else localeEncoding locale
        | .locale => localeEncoding locale
        | .fixed e => e

/-- The document's encoding and its text (HTML §13.2.3.2 and the Encoding Standard's
"decode", which removes a BOM). -/
def decodeDocument (bytes : ByteArray) (transportCharset : Option String := none)
    (fallback : Fallback := .detect) (locale : String := "") : Encoding × String :=
  let e := sniff bytes transportCharset fallback locale
  (e, decode bytes e)

/-- `decodeDocument` with one fast path, for the common page: no BOM, no transport
charset, a UTF-8 `meta` declaration (or none, with the "detect" setting), and bytes that
are UTF-8. Then the text is the bytes as they are (one validation and one copy, no
decoder loop). `decodeDocumentFast_detect` and the `#guard`s below compare it with
`decodeDocument`. -/
def decodeDocumentFast (bytes : ByteArray) (transportCharset : Option String := none)
    (fallback : Fallback := .detect) (locale : String := "") : Encoding × String :=
  if transportCharset.isNone && bomSniff bytes == none then
    match prescan bytes, fallback with
    | some .utf_8, _ | none, .detect =>
      match String.fromUTF8? bytes with
      | some s => (.utf_8, s)
      | none => decodeDocument bytes transportCharset fallback locale
    | _, _ => decodeDocument bytes transportCharset fallback locale
  else decodeDocument bytes transportCharset fallback locale

/-- Under "detect", a page that declares nothing and whose bytes are UTF-8 is read as
UTF-8, whatever the locale. -/
theorem sniff_detect_utf8 (b : ByteArray) (loc : String) (hbom : bomSniff b = none)
    (hpre : prescan b = none) (hv : ByteArray.validateUTF8 b = true) :
    sniff b none .detect loc = .utf_8 := by
  simp [sniff, hbom, hpre, hv]

/-- ... and its text is the bytes' string (the fast path). -/
theorem decodeDocumentFast_detect (b : ByteArray) (s loc : String) (hbom : bomSniff b = none)
    (hpre : prescan b = none) (hs : String.fromUTF8? b = some s) :
    decodeDocumentFast b none .detect loc = (.utf_8, s) := by
  simp [decodeDocumentFast, hbom, hpre, hs]

/-! ## Checks -/

private def agrees (b : ByteArray) (t : Option String := none) : Bool :=
  [Fallback.detect, .locale, .fixed .shift_jis].all fun f =>
    ["", "en-GB", "ja_JP.UTF-8"].all fun loc => decodeDocumentFast b t f loc == decodeDocument b t f loc

-- §13.2.3.2's table.
#guard localeEncoding "ja-JP" == .shift_jis
#guard localeEncoding "ja_JP.UTF-8" == .shift_jis
#guard localeEncoding "zh-CN" == .gbk
#guard localeEncoding "zh-Hans-SG" == .gbk
#guard localeEncoding "zh-Hant-CN" == .big5
#guard localeEncoding "zh_TW" == .big5
#guard localeEncoding "zh" == .windows_1252
#guard localeEncoding "ko-KR" == .euc_kr
#guard localeEncoding "uk-UA" == .windows_1251
#guard localeEncoding "el" == .iso_8859_7
#guard localeEncoding "he-IL" == .windows_1255
#guard localeEncoding "th" == .windows_874
#guard localeEncoding "lt" == .windows_1257
#guard localeEncoding "en-US" == .windows_1252
#guard localeEncoding "" == .windows_1252
#guard Fallback.ofSetting "" == .detect
#guard Fallback.ofSetting "sjis" == .fixed .shift_jis
#guard Fallback.ofSetting "replacement" == .detect
#guard Fallback.ofSetting (Fallback.fixed .big5).setting == .fixed .big5
-- WPT encoding/sniffing.html: UTF-8 bytes and no declaration. "detect" reads UTF-8; the
-- English locale's default reads windows-1252, as that test expects.
#guard sniff (ByteArray.mk #[0x3C, 0x70, 0x3E, 0xC2, 0x80]) none .detect "en" == .utf_8
#guard sniff (ByteArray.mk #[0x3C, 0x70, 0x3E, 0xC2, 0x80]) none .locale "en" == .windows_1252
#guard sniff (ByteArray.mk #[0x3C, 0x70, 0x3E, 0x82, 0xA0]) none .detect "ja" == .shift_jis

#guard agrees "<p>caf\u00e9".toUTF8
#guard agrees "<meta charset=utf-8><p>\u3042".toUTF8
#guard agrees "<meta charset=windows-1252><p>\u00e9".toUTF8
#guard agrees (ByteArray.mk #[0xEF, 0xBB, 0xBF, 0x41])
#guard agrees (ByteArray.mk #[0x63, 0x61, 0x66, 0xE9])
#guard agrees "<p>x".toUTF8 (some "shift_jis")
#guard agrees ByteArray.empty

#guard prescan "<!doctype html><meta charset=\"euc-jp\">".toUTF8 == some .euc_jp
#guard prescan "<meta charset='Shift_JIS'>".toUTF8 == some .shift_jis
#guard prescan "<META HTTP-EQUIV=Content-Type CONTENT='text/html; charset=big5'>".toUTF8 == some .big5
#guard prescan "<meta content='text/html; charset=big5'>".toUTF8 == none
#guard prescan "<!-- <meta charset=euc-kr> --><meta charset=gbk>".toUTF8 == some .gbk
#guard prescan "<p title='<meta charset=koi8-r>'><meta charset=iso-8859-2>".toUTF8 == some .iso_8859_2
#guard prescan "<meta charset=utf-16le>".toUTF8 == some .utf_8
#guard prescan "<meta charset=x-user-defined>".toUTF8 == some .windows_1252
#guard prescan "<meta charset=nonsense><meta charset=euc-jp>".toUTF8 == some .euc_jp
#guard sniff (ByteArray.mk #[0xEF, 0xBB, 0xBF] ++ "<meta charset=windows-1252>".toUTF8) == .utf_8
#guard sniff "<p>x".toUTF8 (some "euc-jp") == .euc_jp
#guard sniff (ByteArray.mk #[0x3C, 0x70, 0x3E, 0xE9]) == .windows_1252
#guard (decodeDocument (ByteArray.mk #[0x3C, 0x6D, 0x65, 0x74, 0x61, 0x20, 0x63, 0x68, 0x61, 0x72, 0x73, 0x65, 0x74,
  0x3D, 0x73, 0x6A, 0x69, 0x73, 0x3E, 0x82, 0xA0])).2 == "<meta charset=sjis>あ"

end L4Factoidal.WHATWG.Encoding.Sniff
