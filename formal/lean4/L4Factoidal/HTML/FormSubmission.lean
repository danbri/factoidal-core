/-
L4Factoidal.HTML.FormSubmission — form submission up to navigation (HTML §4.10.21.3
"Form submission algorithm", §4.10.21.4 "Constructing the entry list", §4.10.21.5
"Selecting a form submission encoding", §4.10.21.6 "Converting an entry list to a list of
name-value pairs"), and the application/x-www-form-urlencoded serializer of the URL
Standard (§5.2) in the form's encoding.

Specifications: HTML Living Standard (whatwg/html `93967771`), URL Standard and Encoding
Standard (the commits of `WHATWG.URL.Parser` and `WHATWG.Encoding.Core`).

What is here, as values:

  * `entryList`: the entry list of a form (§4.10.21.4) over the Lean DOM arena. The values
    are the arena's: an `input`'s value is its `value` attribute, as prelude.js's `value`
    accessor keeps it; a `select`'s selected options are those with `selected` (else the
    first option of a single-select that is not disabled); a `textarea`'s is its text.
  * `pickEncoding`: the form's encoding (§4.10.21.5): the first label of `accept-charset`
    that is an encoding, UTF-8 when it has none that is, else the document's encoding;
    then "get an output encoding".
  * `serialize`: the application/x-www-form-urlencoded serializer with an encoding: each
    name and value through "percent-encode after encoding" with the
    application/x-www-form-urlencoded percent-encode set and spaceAsPlus. A code point the
    encoding cannot encode becomes the numeric character reference `&#N;`, percent-encoded
    (`%26%23N%3B`), as the URL Standard says.
  * `plan`: the form submission algorithm's decisions: the action URL (submitter's
    `formaction`, else the form's `action`, else the document's URL), the method, the
    enctype, the target name, and what is sent. GET replaces the URL's query ("mutate
    action URL"); POST to an http(s) URL is "submit as entity body" (§4.10.21.3): the body
    is the entry list in the enctype (`application/x-www-form-urlencoded`,
    `multipart/form-data` (§4.10.21.8, `multipartBody`) or `text/plain` (§4.10.21.9,
    `textPlainBody`)), each in the form's encoding. `dialog` and the `javascript:` and
    `mailto:` schemes navigate nowhere here: `plan` answers `none`.
  * `navigationAllowed`: where a submission may go (the outbound rule of a navigation the
    page starts): http(s) only where a page's own request may connect
    (`Net.PageFetch.mayConnect`: no local address from a page that is not local, no `http`
    from an `https` page); `data:` only for GET; `file:` only from a `file:` page.
  * `entriesOfWire`: an entry list the page's script host passes back after the `formdata`
    event (§4.10.21.4 step 6): the script may add or change entries; the decisions above are
    still taken here.

Theorems on where a submission goes: `navigationAllowed_post` (a POST goes only where a page
request may connect) and `navigationAllowed_local` (a page that is not local never sends a
form to a local address).

Theorems (cheap, at the byte layer that every encoding shares): `decode_encodeBytes`
(percent-decoding a serialized component gives back exactly the encoder's bytes, so the
serialization loses nothing), `encodeBytes_no_separator` (no raw `&`, `=` or `+` is left
in a component, so splitting the query is unambiguous), `encodeBytes_ncr` (the numeric
character reference of an unencodable code point is `%26%23`, its decimal digits, `%3B`,
which is what the fast path appends), and `utf8_roundTrip` (for UTF-8, decoding the
percent-decoded component gives back the string). `Tests` checks the fast path
(`WHATWG.URL.percentEncodeAfterEncoding`) against the spec-level composition
(`componentSpec`: html-mode encoder bytes, then `encodeByte` per byte) for every encoding
with an encoder, on encodable and unencodable inputs.

No `partial`, no `sorry`.
-/
import L4Factoidal.DOM.Forms
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.WHATWG.Encoding.Core
import L4Factoidal.WHATWG.Encoding.Theorems
import L4Factoidal.Net.PageFetch

namespace L4Factoidal.HTML.FormSubmission
open L4Factoidal.DOM L4Factoidal.DOM.Forms
open L4Factoidal.WHATWG
open L4Factoidal.WHATWG.Encoding (Encoding)

/-! ## Constructing the entry list (§4.10.21.4) -/

/-- An element with a `datalist` ancestor is barred from constraint validation and not
submitted (§4.10.21.4 step 5.1). -/
def inDatalist (d : Dom) (k : NodeId) : Bool := Id.run do
  let mut cur := (d.get k).parent
  for _ in [0:d.size + 1] do
    match cur with
    | none => return false
    | some p => if isHtml d p ["datalist"] then return true else cur := (d.get p).parent
  return false

/-- Strip and collapse ASCII whitespace (Infra), for an `option`'s text. -/
def stripCollapse (s : String) : String :=
  " ".intercalate ((s.splitToList Encoding.isAsciiWhitespace).filter (!·.isEmpty))

/-- An `option`'s value: its `value` attribute, else its text, stripped and collapsed
(§4.10.10). -/
def optionValue (d : Dom) (o : NodeId) : String :=
  match attr? d o "value" with
  | some v => v
  | none => stripCollapse ((d.textContent o).getD "")

/-- An option is disabled when it or its `optgroup` parent has `disabled` (§4.10.10). -/
def optionDisabled (d : Dom) (o : NodeId) : Bool :=
  (attr? d o "disabled").isSome ||
    match (d.get o).parent with
    | some p => isHtml d p ["optgroup"] && (attr? d p "disabled").isSome
    | none => false

/-- The selected options of a `select` in tree order: those with `selected`; for a select
that is not `multiple` and has none, the first option that is not disabled (the
selectedness setting algorithm for a display size of 1). -/
def selectedOptions (d : Dom) (sel : NodeId) : Array NodeId :=
  let opts := (d.treeOrder sel false).filter (isHtml d · ["option"])
  let chosen := opts.filter fun o => (attr? d o "selected").isSome
  if !chosen.isEmpty || (attr? d sel "multiple").isSome then chosen
  else match opts.find? (!optionDisabled d ·) with
    | some o => #[o]
    | none => #[]

/-- An entry's value (XHR "entry"): a string, or a file (its name, its type and its bytes). -/
inductive Value where
  | text (v : String)
  | file (name type : String) (bytes : ByteArray)
  deriving BEq, Inhabited

/-- A value as a string, where a file stands for its name (§4.10.21.7 step 3.2 and
§4.10.21.9 step 3.1). -/
def Value.asText : Value → String
  | .text v => v
  | .file n _ _ => n

/-- The entry list of `form` (§4.10.21.4) with `submitter` (none for `form.submit()`),
and the name of the encoding for a hidden `_charset_` control. Only the controls in the
form's subtree have it as their form owner here (`DOM.Forms.formOwner`: the `form`
attribute is not read). A file control gives an empty file named "" of type
`application/octet-stream` (no file is ever selected here, step 5.11.1). -/
def entries (d : Dom) (form : NodeId) (submitter : Option NodeId) (charsetName : String) :
    Array (String × Value) := Id.run do
  let mut out : Array (String × Value) := #[]
  for k in d.treeOrder form false do
    if !isHtml d k ["button", "input", "select", "textarea"] then continue
    if formOwner d k != some form then continue
    if inDatalist d k || disabledControl d k then continue
    let isInput := isHtml d k ["input"]
    let t := if isInput then inputType d k else ""
    -- buttons count only as the submitter
    let isButton := isHtml d k ["button"] || (isInput && ["submit", "image", "reset", "button"].contains t)
    if isButton && submitter != some k then continue
    if isInput && (t == "checkbox" || t == "radio") && !checkedness d k then continue
    -- an image button: its coordinate entries (0, 0: there is no pointer position here)
    if isInput && t == "image" then
      let n := (attr? d k "name").getD ""
      let pfx := if n.isEmpty then "" else n ++ "."
      out := out.push (pfx ++ "x", .text "0") |>.push (pfx ++ "y", .text "0")
      continue
    let name := (attr? d k "name").getD ""
    if name.isEmpty then continue
    if isHtml d k ["select"] then
      for o in selectedOptions d k do
        if !optionDisabled d o then out := out.push (name, .text (optionValue d o))
    else if isInput && (t == "checkbox" || t == "radio") then
      out := out.push (name, .text ((attr? d k "value").getD "on"))
    else if isInput && t == "file" then
      out := out.push (name, .file "" "application/octet-stream" ByteArray.empty)
    else if isInput && t == "hidden" && Dom.asciiLower name == "_charset_" then
      out := out.push (name, .text charsetName)
    else if isHtml d k ["textarea"] then
      out := out.push (name, .text ((d.textContent k).getD ""))
    else
      out := out.push (name, .text ((attr? d k "value").getD ""))
  return out

/-- The entry list as names and strings (a file stands for its name). -/
def entryList (d : Dom) (form : NodeId) (submitter : Option NodeId) (charsetName : String) :
    Array (String × String) :=
  (entries d form submitter charsetName).map fun (n, v) => (n, v.asText)

/-- §4.10.21.6: every CR not followed by LF, and every LF not preceded by CR, becomes
CR LF. -/
def normalizeLineBreaks (s : String) : String := Id.run do
  let cs := s.toList.toArray
  let mut out : String := ""
  for i in [0:cs.size] do
    let c := cs[i]!
    if c == '\r' then out := out.push '\r' |>.push '\n'
    else if c == '\n' then
      if i > 0 && cs[i - 1]! == '\r' then pure () else out := out.push '\r' |>.push '\n'
    else out := out.push c
  return out

/-- Converting an entry list to a list of name-value pairs (§4.10.21.6). -/
def pairs (entries : Array (String × String)) : List (String × String) :=
  entries.toList.map fun (n, v) => (normalizeLineBreaks n, normalizeLineBreaks v)

/-! ## The form's encoding (§4.10.21.5) -/

/-- Selecting a form submission encoding: the first `accept-charset` label that is an
encoding (UTF-8 when none is), else the document's encoding; then get an output encoding. -/
def pickEncoding (acceptCharset : Option String) (docEncoding : Encoding) : Encoding :=
  let enc := match acceptCharset with
    | none => docEncoding
    | some input =>
      let labels := (input.splitToList Encoding.isAsciiWhitespace).filter (!·.isEmpty)
      (labels.findSome? Encoding.getEncoding).getD .utf_8
  Encoding.getOutputEncoding enc

/-! ## The serializer (URL §5.2) in an encoding -/

/-- One name or value: percent-encode after encoding, with the
application/x-www-form-urlencoded set and spaceAsPlus. -/
def component (enc : Encoding) (s : String) : String :=
  URL.percentEncodeAfterEncoding enc (s.toList.toArray.map (·.val)) .formUrlencoded true

/-- The application/x-www-form-urlencoded serializer with `enc` (URL §5.2). -/
def serialize (enc : Encoding) (tuples : List (String × String)) : String :=
  "&".intercalate (tuples.map fun (n, v) => component enc n ++ "=" ++ component enc v)

/-! ## Request bodies (§4.10.21.7 to §4.10.21.9) -/

/-- A string in the form's encoding, an unencodable code point as its numeric character
reference (Encoding "encode", mode html). -/
def encodeText (enc : Encoding) (s : String) : ByteArray :=
  (Encoding.encode (s.toList.toArray.map (·.val)) (Encoding.getOutputEncoding enc)).getD s.toUTF8

/-- A field name or filename in a `Content-Disposition` header (§4.10.21.8): LF, CR and `"`
become `%0A`, `%0D` and `%22`. -/
def escapeField (s : String) : String :=
  String.join (s.toList.map fun c =>
    if c == '\n' then "%0A" else if c == '\r' then "%0D" else if c == '"' then "%22" else c.toString)

/-- The ISO-8859-1 reading of bytes (each byte one code point), to search them as text. -/
def isoText (b : ByteArray) : String := String.ofList (b.toList.map fun x => Char.ofNat x.toNat)

/-- The first boundary of the form `----FoafnautFormBoundary<k>` that occurs in no part
(RFC 2046 §5.1.1: a boundary must not occur in the parts). -/
def boundaryFor (parts : List ByteArray) : String := Id.run do
  let texts := parts.map isoText
  for k in [0:parts.length + 2] do
    let b := s!"----FoafnautFormBoundary{k}"
    if texts.all fun t => (t.splitOn b).length == 1 then return b
  return s!"----FoafnautFormBoundary{parts.length + 2}"

/-- The multipart/form-data encoding algorithm (§4.10.21.8, RFC 7578) in encoding `enc`:
names and string values with their line breaks normalized, names, string values and
filenames in `enc`, a file's type or `application/octet-stream`. The boundary and the
body. -/
def multipartBody (enc : Encoding) (es : List (String × Value)) : String × ByteArray := Id.run do
  let parts := es.map fun (n, v) =>
    let head := "Content-Disposition: form-data; name=\"" ++ escapeField (normalizeLineBreaks n) ++ "\"" ++
      match v with
      | .text _ => ""
      | .file fname type _ =>
        "; filename=\"" ++ escapeField fname ++ "\"\r\nContent-Type: " ++
          (if type.isEmpty then "application/octet-stream" else type)
    let content := match v with
      | .text t => encodeText enc (normalizeLineBreaks t)
      | .file _ _ b => b
    (encodeText enc head, content)
  let b := boundaryFor (parts.flatMap fun (h, c) => [h, c])
  let mut out := ByteArray.empty
  for (h, c) in parts do
    out := out ++ ("--" ++ b ++ "\r\n").toUTF8 ++ h ++ "\r\n\r\n".toUTF8 ++ c ++ "\r\n".toUTF8
  return (b, out ++ ("--" ++ b ++ "--\r\n").toUTF8)

/-- The text/plain encoding algorithm (§4.10.21.9): each pair as `name=value` and CR LF, a
file as its name, in encoding `enc`. -/
def textPlainBody (enc : Encoding) (es : List (String × Value)) : ByteArray :=
  encodeText enc (String.join (es.map fun (n, v) =>
    normalizeLineBreaks n ++ "=" ++ normalizeLineBreaks v.asText ++ "\r\n"))

/-! ## Where a submission may go -/

/-- The outbound rule of a form submission, a navigation the page starts. `page`: what the
engine knows of the page (`Net.PageFetch.Page.ofUrl`, never what the page says of itself);
`pageScheme`: the scheme of the form's document. An http(s) URL only where a request of
the page may connect (`Net.PageFetch.mayConnect`); a `data:` URL only with GET (it is
answered from the URL, nothing is sent); a `file:` URL only from a `file:` document. -/
def navigationAllowed (page : Net.PageFetch.Page) (pageScheme : String) (u : URL.Url) (post : Bool) : Bool :=
  if u.scheme == "http" || u.scheme == "https" then Net.PageFetch.mayConnect page u
  else if u.scheme == "data" then !post
  else u.scheme == "file" && pageScheme == "file" && !post

/-- Theorem (security, safety property). Says: a POST submission is allowed only to a URL
that a request of the page may connect to (`Net.PageFetch.mayConnect`), so the rules for a
page's requests (local addresses, mixed content) hold for every request body a form sends.
Does not say: anything about what the embedder does with the request, nor about GET to
`data:` or `file:` URLs. -/
theorem navigationAllowed_post (page : Net.PageFetch.Page) (s : String) (u : URL.Url)
    (h : navigationAllowed page s u true = true) : Net.PageFetch.mayConnect page u = true := by
  unfold navigationAllowed at h
  by_cases hs : (u.scheme == "http" || u.scheme == "https") = true
  · simpa [hs] using h
  · simp only [hs, if_false, Bool.false_eq_true] at h
    split at h <;> simp_all

/-- Theorem (security, safety property). Says: a page that is not local never sends a form
(GET or POST) to a local http(s) address (`localhost`, a `.localhost` name or a
special-purpose IP literal, `Net.PageFetch.privateHost`). Does not say: anything about a
name that resolves to a local address (the request's DNS pin is the embedder's, as for a
page request), nor about `data:` or `file:` URLs, which go to no host. -/
theorem navigationAllowed_local (page : Net.PageFetch.Page) (s : String) (u : URL.Url) (post : Bool)
    (hl : page.isLocal = false) (hs : (u.scheme == "http" || u.scheme == "https") = true)
    (h : navigationAllowed page s u post = true) : Net.PageFetch.privateHost u = false := by
  unfold navigationAllowed at h
  simp only [hs, if_true] at h
  cases hp : Net.PageFetch.privateHost u
  · rfl
  · have := Net.PageFetch.mayConnect_local_needs_local_page page u h hp
    simp_all

/-! ## The submission (§4.10.21.3) -/

/-- The enctype of a submission (§4.10.19.6): the submitter's `formenctype`, else the
form's `enctype`; `application/x-www-form-urlencoded` when missing or invalid. -/
inductive Enctype where
  | urlencoded | multipart | textPlain
  deriving BEq, Repr, Inhabited, DecidableEq

/-- What a submission does: navigate the navigable that `target` names (resolved by the
host: "" and `_self` the form's own, `_blank`, `_parent`, `_top`, or a frame name) to
`url`, with GET, or with POST and a body of type `contentType`. -/
structure Plan where
  target : String
  url : String
  method : String := "GET"
  contentType : String := ""
  body : ByteArray := ByteArray.empty
  deriving BEq, Inhabited

/-- A submit button's override of a form attribute (`formaction`, `formmethod`,
`formtarget`): only a submitter that is a submit button has them. -/
def submitterAttr (d : Dom) (submitter : Option NodeId) (name : String) : Option String :=
  match submitter with
  | some s =>
    if isHtml d s ["button"] && buttonType d s == "submit" ||
       isHtml d s ["input"] && (inputType d s == "submit" || inputType d s == "image") then attr? d s name
    else none
  | none => none

/-- The method keyword (§4.10.19.6): `get`, `post` or `dialog`; GET when missing or
invalid. -/
def method (d : Dom) (form : NodeId) (submitter : Option NodeId) : String :=
  let m := Dom.asciiLower ((submitterAttr d submitter "formmethod" <|> attr? d form "method").getD "get")
  if m == "post" || m == "dialog" then m else "get"

def enctype (d : Dom) (form : NodeId) (submitter : Option NodeId) : Enctype :=
  let e := Dom.asciiLower ((submitterAttr d submitter "formenctype" <|> attr? d form "enctype").getD "")
  if e == "multipart/form-data" then .multipart
  else if e == "text/plain" then .textPlain
  else .urlencoded

/-- The target of the submission (§4.10.21.3 step 18, "get an element's target"): the
submitter's `formtarget`, else the form's `target`, else `baseTarget` (the first `base`
element's `target` in the document). -/
def target (d : Dom) (form : NodeId) (submitter : Option NodeId) (baseTarget : String) : String :=
  (submitterAttr d submitter "formtarget" <|> attr? d form "target").getD baseTarget

/-- The form's encoding for a submission: `accept-charset`, else the document's
(`pickEncoding`). -/
def formEncoding (d : Dom) (form : NodeId) (docEncoding : Encoding) : Encoding :=
  pickEncoding (attr? d form "accept-charset") docEncoding

/-- The form submission algorithm for `form` with `submitter`, in a document with URL
`docURL` (its base URL) and encoding `docEncoding`, with the entry list `given` when the
page's script host passed one back after the `formdata` event (else the form's own,
`entries`): the navigation it makes. GET to an http(s), data or file URL: "mutate action
URL" (the query becomes the serialized entry list in the form's encoding). POST to an
http(s) URL: "submit as entity body" in the enctype; POST to a data URL: "get action URL"
(nothing is sent). `none` when it navigates nowhere here: the action does not parse,
`dialog`, `javascript:` and `mailto:` URLs. Where it may go is `navigationAllowed`, asked by
the caller, which knows the page. -/
def plan (d : Dom) (form : NodeId) (submitter : Option NodeId) (docURL : String) (docEncoding : Encoding)
    (baseTarget : String := "") (given : Option (Array (String × Value)) := none) : Option Plan := do
  let action := (submitterAttr d submitter "formaction" <|> attr? d form "action").getD ""
  let action := if action.isEmpty then docURL else action
  let parsed ← URL.parseUrl action (if docURL.isEmpty then none else some docURL)
  let m := method d form submitter
  if m == "dialog" then none
  if !["http", "https", "data", "file"].contains parsed.scheme then none
  let enc := formEncoding d form docEncoding
  let es := (given.getD (entries d form submitter enc.name)).toList
  let tgt := target d form submitter baseTarget
  if m == "get" then
    let query := serialize enc (pairs (es.toArray.map fun (n, v) => (n, v.asText)))
    return { target := tgt, url := { parsed with query := some query }.href }
  if parsed.scheme == "data" then return { target := tgt, url := parsed.href }
  if parsed.scheme != "http" && parsed.scheme != "https" then none
  match enctype d form submitter with
  | .urlencoded =>
    let body := serialize enc (pairs (es.toArray.map fun (n, v) => (n, v.asText)))
    return { target := tgt, url := parsed.href, method := "POST",
             contentType := "application/x-www-form-urlencoded", body := body.toUTF8 }
  | .multipart =>
    let (b, body) := multipartBody enc es
    return { target := tgt, url := parsed.href, method := "POST",
             contentType := "multipart/form-data; boundary=" ++ b, body }
  | .textPlain =>
    return { target := tgt, url := parsed.href, method := "POST",
             contentType := "text/plain", body := textPlainBody enc es }

/-! ## An entry list from the page's script host

After the `formdata` event the script's `FormData` holds the entry list. The host passes it
back as text: fields separated by U+0000, each with `\` written `\\` and U+0000 written `\0`.
An entry is `s`, name, value; or `f`, name, filename, type, bytes (one code point below 256
a byte). -/

/-- Escape one field for the wire. -/
def escapeWire (s : String) : String :=
  String.join (s.toList.map fun c => if c == '\\' then "\\\\" else if c.toNat == 0 then "\\0" else c.toString)

/-- An entry list as wire text, for the page's script host (the `formdata` event's
`FormData`, and `new FormData(form)`). -/
def entriesToWire (es : Array (String × Value)) : String :=
  "\x00".intercalate (es.toList.flatMap fun (n, v) => match v with
    | .text t => ["s", escapeWire n, escapeWire t]
    | .file fname type b => ["f", escapeWire n, escapeWire fname, escapeWire type, escapeWire (isoText b)])

/-- Undo the escapes of one field. -/
def unescapeField (s : String) : String := Id.run do
  let mut out := ""
  let mut esc := false
  for c in s.toList do
    if esc then
      out := out.push (if c == '0' then Char.ofNat 0 else c)
      esc := false
    else if c == '\\' then esc := true
    else out := out.push c
  return out

/-- Bytes from a field of code points below 256; `none` when one is not. -/
def bytesOfField (s : String) : Option ByteArray :=
  s.toList.foldlM (fun (b : ByteArray) c => if c.toNat < 256 then some (b.push c.toNat.toUInt8) else none) ByteArray.empty

/-- The entry list of the wire text; `none` when it is malformed. -/
def entriesOfWire (wire : String) : Option (Array (String × Value)) := do
  if wire.isEmpty then return #[]
  let rec go (fuel : Nat) (fs : List String) (acc : Array (String × Value)) : Option (Array (String × Value)) :=
    match fuel, fs with
    | _, [] => some acc
    | 0, _ => none
    | fuel + 1, "s" :: n :: v :: rest => go fuel rest (acc.push (unescapeField n, .text (unescapeField v)))
    | fuel + 1, "f" :: n :: fname :: type :: bytes :: rest => do
      let b ← bytesOfField (unescapeField bytes)
      go fuel rest (acc.push (unescapeField n, .file (unescapeField fname) (unescapeField type) b))
    | _, _ => none
  let fs := wire.splitOn "\x00"
  go fs.length fs #[]

/-! ## The byte layer, at the level of the specification

`encodeByte` is URL §1.3 "percent-encode after encoding" step 5.3 for one byte with the
application/x-www-form-urlencoded set and spaceAsPlus; `decodeChars` is "percent-decode"
after the application/x-www-form-urlencoded parser's `+` to space. -/

def hexDigit (n : Nat) : Char := URL.hexUpper n

/-- The value of an upper- or lower-case hex digit. -/
def hexVal? (c : Char) : Option Nat :=
  if '0' ≤ c && c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 'A'.toNat + 10)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def encodeByte (b : UInt8) : List Char :=
  if b == 0x20 then ['+']
  else if URL.inFormUrlencoded b.toNat then ['%', hexDigit (b.toNat / 16), hexDigit (b.toNat % 16)]
  else [Char.ofNat b.toNat]

def encodeBytes (bs : List UInt8) : List Char := bs.flatMap encodeByte

/-- `+` is a space, `%` and two hex digits the byte they name, any other ASCII character
its byte. Specification only (the theorems below): not compiled. -/
noncomputable def decodeChars : List Char → List UInt8
  | [] => []
  | '+' :: r => 0x20 :: decodeChars r
  | '%' :: h :: l :: r =>
    match hexVal? h, hexVal? l with
    | some x, some y => (x * 16 + y).toUInt8 :: decodeChars r
    | _, _ => 0x25 :: decodeChars (h :: l :: r)
  | c :: r => c.toNat.toUInt8 :: decodeChars r

/-- A component at the level of the specification: the encoder's bytes in mode html (an
unencodable code point becomes `&#N;`), then `encodeByte` per byte. -/
def componentSpec (enc : Encoding) (s : String) : String :=
  match Encoding.encode (s.toList.toArray.map (·.val)) (Encoding.getOutputEncoding enc) with
  | some bs => String.ofList (encodeBytes bs.toList)
  | none => String.ofList (encodeBytes (String.toUTF8 s).toList)

private theorem hexVal_hexDigit : ∀ x : Fin 16, hexVal? (hexDigit x.val) = some x.val := by decide

/-- What `encodeByte` makes of a byte it does not percent-encode. -/
private theorem plain_bytes : ∀ n : Fin 256, (UInt8.ofNat n.val) ≠ 0x20 → URL.inFormUrlencoded (UInt8.ofNat n.val).toNat = false →
    (Char.ofNat (UInt8.ofNat n.val).toNat).toNat.toUInt8 = UInt8.ofNat n.val ∧
      Char.ofNat (UInt8.ofNat n.val).toNat ≠ '%' ∧ Char.ofNat (UInt8.ofNat n.val).toNat ≠ '+' := by
  decide +kernel

private theorem plain_byte (b : UInt8) (h1 : b ≠ 0x20) (h2 : URL.inFormUrlencoded b.toNat = false) :
    (Char.ofNat b.toNat).toNat.toUInt8 = b ∧ Char.ofNat b.toNat ≠ '%' ∧ Char.ofNat b.toNat ≠ '+' := by
  have := plain_bytes ⟨b.toNat, b.toNat_lt⟩
  simp only [UInt8.ofNat_toNat] at this
  exact this h1 h2

theorem decodeChars_other (c : Char) (r : List Char) (h1 : c ≠ '+') (h2 : c ≠ '%') :
    decodeChars (c :: r) = c.toNat.toUInt8 :: decodeChars r := by
  rcases r with _ | ⟨h, _ | ⟨l, r⟩⟩ <;> simp [decodeChars, h2] <;> simp [decodeChars, h1, h2]

theorem decode_encodeByte (b : UInt8) (r : List Char) :
    decodeChars (encodeByte b ++ r) = b :: decodeChars r := by
  unfold encodeByte
  by_cases h1 : b = 0x20
  · subst h1; simp [decodeChars]
  · by_cases h2 : URL.inFormUrlencoded b.toNat = true
    · have hb : b.toNat < 256 := b.toNat_lt
      have hx := hexVal_hexDigit ⟨b.toNat / 16, by omega⟩
      have hy := hexVal_hexDigit ⟨b.toNat % 16, by omega⟩
      simp only [h1, h2, if_false, if_true, beq_iff_eq, List.cons_append, List.nil_append]
      simp only [decodeChars, hx, hy]
      congr 1
      apply UInt8.toNat.inj
      simp [UInt8.toNat_ofNat]
      omega
    · have h2' : URL.inFormUrlencoded b.toNat = false := by simpa using h2
      obtain ⟨hv, hp, hplus⟩ := plain_byte b h1 h2'
      simp only [h1, h2', beq_iff_eq, if_false, Bool.false_eq_true, List.cons_append, List.nil_append]
      rw [decodeChars_other _ _ hplus hp, hv]

/-- Percent-decoding a serialized component gives back exactly the bytes: the
serialization loses nothing, in every encoding. -/
theorem decode_encodeBytes (bs : List UInt8) : decodeChars (encodeBytes bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b r ih => simp only [encodeBytes, List.flatMap_cons] at *; rw [decode_encodeByte, ih]

private theorem no_sep_bytes : ∀ n : Fin 256, '&' ∉ encodeByte (UInt8.ofNat n.val) ∧ '=' ∉ encodeByte (UInt8.ofNat n.val) := by
  decide +kernel

private theorem no_sep_byte (b : UInt8) : '&' ∉ encodeByte b ∧ '=' ∉ encodeByte b := by
  have := no_sep_bytes ⟨b.toNat, b.toNat_lt⟩
  simpa only [UInt8.ofNat_toNat] using this

/-- No raw `&` or `=` is left in a component, and a `+` only stands for a space: splitting
the query at `&` and `=` finds the names and values again. -/
theorem encodeBytes_no_separator (bs : List UInt8) :
    '&' ∉ encodeBytes bs ∧ '=' ∉ encodeBytes bs := by
  simp only [encodeBytes, List.mem_flatMap, not_exists, not_and]
  exact ⟨fun b _ => (no_sep_byte b).1, fun b _ => (no_sep_byte b).2⟩

private theorem digit_bytes : ∀ k : Fin 10, encodeByte (48 + k.val).toUInt8 = [Char.ofNat (48 + k.val)] := by
  decide

private theorem encodeByte_digit (c : Char) (h : c.isDigit = true) : encodeByte c.toNat.toUInt8 = [c] := by
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : 48 ≤ c.toNat := h1
  have h2' : c.toNat ≤ 57 := h2
  have := digit_bytes ⟨c.toNat - 48, by omega⟩
  simp only [show 48 + (c.toNat - 48) = c.toNat by omega, Char.ofNat_toNat] at this
  exact this

private theorem encodeBytes_digits (cs : List Char) (h : ∀ c ∈ cs, c.isDigit = true) :
    encodeBytes (cs.map (·.toNat.toUInt8)) = cs := by
  induction cs with
  | nil => rfl
  | cons c r ih =>
    simp only [encodeBytes, List.map_cons, List.flatMap_cons] at *
    rw [encodeByte_digit c (h c (by simp)), ih (fun x hx => h x (by simp [hx]))]
    rfl

/-- The numeric character reference of an unencodable code point (`&#N;`, Encoding
Standard "encode" in mode html) serializes as `%26%23`, the decimal digits of `N`, `%3B`:
the text the fast path (`WHATWG.URL.percentEncodeAfterEncoding`) appends for an error. -/
theorem encodeBytes_ncr (n : Nat) :
    encodeBytes ([0x26, 0x23] ++ Encoding.decimalBytes n ++ [0x3B]) =
      "%26%23".toList ++ (toString n).toList ++ "%3B".toList := by
  have hd : ∀ c ∈ (toString n).toList, c.isDigit = true := by
    intro c hc
    have : (toString n).toList = Nat.toDigits 10 n := by
      show (Nat.repr n).toList = _
      simp [Nat.repr, String.toList_ofList]
    rw [this] at hc
    exact Nat.isDigit_of_mem_toDigits (by decide) (by decide) hc
  simp only [encodeBytes, List.flatMap_append] at *
  rw [show (Encoding.decimalBytes n).flatMap encodeByte = encodeBytes ((toString n).toList.map (·.toNat.toUInt8)) from rfl,
    encodeBytes_digits _ hd]
  rfl

/-- For UTF-8, the percent-decoded component is the string's UTF-8 bytes, which decode
to the string. -/
theorem utf8_roundTrip (s : String) :
    ∃ bs : ByteArray, bs.toList = decodeChars (encodeBytes s.toUTF8.toList) ∧
      Encoding.utf8DecodeWithoutBOMOrFail bs = some s :=
  ⟨s.toUTF8, (decode_encodeBytes _).symm, Encoding.utf8DecodeWithoutBOMOrFail_toUTF8 s⟩

end L4Factoidal.HTML.FormSubmission
