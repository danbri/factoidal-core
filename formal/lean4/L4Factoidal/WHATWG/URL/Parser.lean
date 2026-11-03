/-
L4Factoidal.WHATWG.URL.Parser — URLs of the WHATWG URL Standard: the URL
record (section 4.1), the basic URL parser with state override (section 4.4),
the URL serializer (section 4.5), origins (section 4.7), the
application/x-www-form-urlencoded parser and serializer (section 5), and the
attribute getters and setters of the URL class (section 6.1).

Specification: URL Standard, WHATWG Living Standard, Last Updated 19 October
2026 (commit snapshot whatwg/url `845bafca22fb0c5a42c4bf384a9bdea525a2f10d`). Tests: web-platform-tests `url/`
(third_party/testing/wpt-url), run by tests/whatwg-url/run.sh.

The parser is the standard's state machine, transcribed: one mutable record
for url, buffer, the three flags and pointer, and a loop that runs one state
per round. "Decrease pointer by 1" and "start over" are pointer arithmetic, as
in the standard. The loop has fuel `8 × (input length + 2)`: the scheme state
starts over at most once, the authority state rewinds at most once, and every
other rewind is one code point. If the fuel ends the result is failure; the
self-test `l4whatwg-url selftest` parses inputs of 1,000,000 code points of
each shape that rewinds.

Validation errors are not reported; they do not change the result.

https://github.com/danbri/factoidal/issues/1167, milestone 3. No `partial`, no
`sorry`.
-/
import L4Factoidal.WHATWG.URL.Host

namespace L4Factoidal.WHATWG.URL

open L4Factoidal.WHATWG.Encoding

/-! ## URL records (section 4.1) -/

/-- A URL's path: an opaque path (a string) or a list of segments. -/
inductive UrlPath where
  | opaque (s : String)
  | segments (xs : Array String)
  deriving DecidableEq, Repr, Inhabited

/-- A URL record. The blob URL entry is not represented. -/
structure Url where
  scheme : String := ""
  username : String := ""
  password : String := ""
  host : Option Host := none
  port : Option Nat := none
  path : UrlPath := .segments #[]
  query : Option String := none
  fragment : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- The default port of a special scheme (section 4.1). -/
def defaultPort : String → Option Nat
  | "ftp" => some 21
  | "http" => some 80
  | "https" => some 443
  | "ws" => some 80
  | "wss" => some 443
  | _ => none

def isSpecialScheme (s : String) : Bool :=
  s == "ftp" || s == "file" || s == "http" || s == "https" || s == "ws" || s == "wss"

def Url.isSpecial (u : Url) : Bool := isSpecialScheme u.scheme

def Url.includesCredentials (u : Url) : Bool := !u.username.isEmpty || !u.password.isEmpty

def Url.hasOpaquePath (u : Url) : Bool :=
  match u.path with | .opaque _ => true | .segments _ => false

/-- A URL cannot have a username/password/port when its host is null or the
empty host, or its scheme is "file". -/
def Url.cannotHaveUsernamePasswordPort (u : Url) : Bool :=
  u.host.isNone || u.host == some .empty || u.scheme == "file"

/-- A Windows drive letter: an ASCII alpha followed by `:` or `|`. -/
def isWindowsDriveLetter (s : List Char) : Bool :=
  match s with
  | [a, b] => isAsciiAlpha a && (b == ':' || b == '|')
  | _ => false

def isNormalizedWindowsDriveLetter (s : String) : Bool :=
  match s.toList with
  | [a, b] => isAsciiAlpha a && b == ':'
  | _ => false

/-- A string starts with a Windows drive letter. -/
def startsWithWindowsDriveLetter (s : List Char) : Bool :=
  match s with
  | a :: b :: rest =>
    isWindowsDriveLetter [a, b] &&
      (match rest with
       | [] => true
       | c :: _ => c == '/' || c == '\\' || c == '?' || c == '#')
  | _ => false

/-- Shorten a URL's path. -/
def Url.shortenPath (u : Url) : Url :=
  match u.path with
  | .opaque _ => u
  | .segments xs =>
    if u.scheme == "file" && xs.size == 1 && isNormalizedWindowsDriveLetter xs[0]! then u
    else { u with path := .segments xs.pop }

def Url.appendSegment (u : Url) (s : String) : Url :=
  match u.path with
  | .opaque p => { u with path := .opaque (p ++ s) }
  | .segments xs => { u with path := .segments (xs.push s) }

def isSingleDot (s : String) : Bool := s == "." || asciiLowerStr s == "%2e"

def isDoubleDot (s : String) : Bool :=
  let l := asciiLowerStr s
  l == ".." || l == ".%2e" || l == "%2e." || l == "%2e%2e"

/-- Path state step 1 for one segment (buffer), given whether c is `/` (or
`\\` in a special URL): a double-dot segment shortens the path, a single-dot
segment adds nothing, any other segment is appended; a dot segment that ends
the path appends the empty segment. A Windows drive letter that starts a
file URL's path gets `:`. -/
def Url.pathSegment (u : Url) (buffer : String) (slashLike : Bool) : Url :=
  if isDoubleDot buffer then
    let u := u.shortenPath
    if !slashLike then u.appendSegment "" else u
  else if isSingleDot buffer then
    if !slashLike then u.appendSegment "" else u
  else
    let isEmptyPath := match u.path with | .segments xs => xs.isEmpty | .opaque _ => false
    if u.scheme == "file" && isEmptyPath && isWindowsDriveLetter buffer.toList then
      u.appendSegment (String.ofList [buffer.toList[0]!, ':'])
    else u.appendSegment buffer

/-! ## The basic URL parser (section 4.4) -/

/-- The states of the basic URL parser. -/
inductive State where
  | schemeStart | scheme | noScheme | specialRelativeOrAuthority | pathOrAuthority
  | relative | relativeSlash | specialAuthoritySlashes | specialAuthorityIgnoreSlashes
  | authority | host | hostname | port | file | fileSlash | fileHost | pathStart | path
  | opaquePath | query | fragment
  deriving DecidableEq, Repr, Inhabited

/-- The result of the basic URL parser. With a state override, the standard
changes url in place and may return failure after some changes; `failure`
carries url as it is then. -/
inductive ParseResult where
  | ok (u : Url)
  | failure (u : Url)
  deriving Repr, Inhabited

def ParseResult.toOption : ParseResult → Option Url
  | .ok u => some u
  | .failure _ => none

def ParseResult.url : ParseResult → Url
  | .ok u => u
  | .failure u => u

def isC0OrSpace (c : Char) : Bool := c.toNat ≤ 0x20

/-- Remove leading and trailing C0 control or space. -/
def trimC0Space (s : String) : String :=
  String.ofList ((s.toList.dropWhile isC0OrSpace).reverse.dropWhile isC0OrSpace).reverse

def removeTabNewline (s : String) : String :=
  String.ofList (s.toList.filter (fun c => c != '\t' && c != '\n' && c != '\r'))

/-- Percent-encode the query buffer with an encoding (query state step 2). -/
def encodeQuery (enc : Encoding) (buffer : String) (set : PercentEncodeSet) : String :=
  if enc == .utf_8 then utf8PercentEncodeString set buffer
  else percentEncodeAfterEncoding enc ((buffer.toList.map (fun c => c.val)).toArray) set

/-- The basic URL parser: input, an optional base, an optional url and state
override, and an encoding (UTF-8 by default). -/
def basicParse (input0 : String) (base : Option Url := none) (urlIn : Option Url := none)
    (override : Option State := none) (encoding : Encoding := .utf_8) : ParseResult := Id.run do
  let mut url := urlIn.getD {}
  let input := removeTabNewline (if urlIn.isNone then trimC0Space input0 else input0)
  let cs := input.toList.toArray
  let n := cs.size
  let mut state := override.getD .schemeStart
  let mut enc := encoding
  let mut buffer : String := ""
  let mut atSignSeen := false
  let mut insideBrackets := false
  let mut passwordTokenSeen := false
  -- pointer; -1 only between "start over" and the increment that follows it.
  let mut p : Int := 0
  let overridden := override.isSome
  for _ in [0:8 * (n + 2)] do
    let i := p.toNat
    let c : Option Char := if p ≥ 0 then cs[i]? else none
    let rem0 : Option Char := cs[i + 1]?
    let isEof := c.isNone
    let special := url.isSpecial
    match state with
    | .schemeStart =>
      match c with
      | some ch =>
        if isAsciiAlpha ch then
          buffer := buffer.push (asciiLower ch)
          state := .scheme
        else if !overridden then
          state := .noScheme
          p := p - 1
        else return .failure url
      | none =>
        if !overridden then
          state := .noScheme
          p := p - 1
        else return .failure url
    | .scheme =>
      match c with
      | some ch =>
        if isAsciiAlpha ch || isAsciiDigit ch || ch == '+' || ch == '-' || ch == '.' then
          buffer := buffer.push (asciiLower ch)
        else if ch == ':' then
          if overridden then
            if url.isSpecial && !isSpecialScheme buffer then return .ok url
            if !url.isSpecial && isSpecialScheme buffer then return .ok url
            if (url.includesCredentials || url.port.isSome) && buffer == "file" then return .ok url
            if url.scheme == "file" && url.host == some .empty then return .ok url
          url := { url with scheme := buffer }
          if overridden then
            if url.port.isSome && url.port == defaultPort url.scheme then
              url := { url with port := none }
            return .ok url
          buffer := ""
          if url.scheme == "file" then
            state := .file
          else if url.isSpecial && base.isSome && (base.map (·.scheme)) == some url.scheme then
            state := .specialRelativeOrAuthority
          else if url.isSpecial then
            state := .specialAuthoritySlashes
          else if rem0 == some '/' then
            state := .pathOrAuthority
            p := p + 1
          else
            url := { url with path := .opaque "" }
            state := .opaquePath
        else if !overridden then
          buffer := ""
          state := .noScheme
          p := -1
        else return .failure url
      | none =>
        if !overridden then
          buffer := ""
          state := .noScheme
          p := -1
        else return .failure url
    | .noScheme =>
      match base with
      | none => return .failure url
      | some b =>
        if b.hasOpaquePath && c != some '#' then return .failure url
        else if b.hasOpaquePath && c == some '#' then
          url := { url with scheme := b.scheme, path := b.path, query := b.query, fragment := some "" }
          state := .fragment
        else if b.scheme != "file" then
          state := .relative
          p := p - 1
        else
          state := .file
          p := p - 1
    | .specialRelativeOrAuthority =>
      if c == some '/' && rem0 == some '/' then
        state := .specialAuthorityIgnoreSlashes
        p := p + 1
      else
        state := .relative
        p := p - 1
    | .pathOrAuthority =>
      if c == some '/' then state := .authority
      else
        state := .path
        p := p - 1
    | .relative =>
      let b := base.getD {}
      url := { url with scheme := b.scheme }
      if c == some '/' then state := .relativeSlash
      else if url.isSpecial && c == some '\\' then state := .relativeSlash
      else
        url := { url with username := b.username, password := b.password, host := b.host,
                          port := b.port, path := b.path, query := b.query }
        if c == some '?' then
          url := { url with query := some "" }
          state := .query
        else if c == some '#' then
          url := { url with fragment := some "" }
          state := .fragment
        else if !isEof then
          url := { url with query := none }
          url := url.shortenPath
          state := .path
          p := p - 1
    | .relativeSlash =>
      if url.isSpecial && (c == some '/' || c == some '\\') then
        state := .specialAuthorityIgnoreSlashes
      else if c == some '/' then state := .authority
      else
        let b := base.getD {}
        url := { url with username := b.username, password := b.password, host := b.host,
                          port := b.port }
        state := .path
        p := p - 1
    | .specialAuthoritySlashes =>
      if c == some '/' && rem0 == some '/' then
        state := .specialAuthorityIgnoreSlashes
        p := p + 1
      else
        state := .specialAuthorityIgnoreSlashes
        p := p - 1
    | .specialAuthorityIgnoreSlashes =>
      if c != some '/' && c != some '\\' then
        state := .authority
        p := p - 1
    | .authority =>
      if c == some '@' then
        if atSignSeen then buffer := "%40" ++ buffer
        atSignSeen := true
        for cp in buffer.toList do
          if cp == ':' && !passwordTokenSeen then
            passwordTokenSeen := true
          else
            let pe := utf8PercentEncodeChar .userinfo cp
            if passwordTokenSeen then url := { url with password := url.password ++ pe }
            else url := { url with username := url.username ++ pe }
        buffer := ""
      else if isEof || c == some '/' || c == some '?' || c == some '#'
          || (special && c == some '\\') then
        if atSignSeen && buffer.isEmpty then return .failure url
        p := p - (buffer.length + 1 : Nat)
        buffer := ""
        state := .host
      else
        buffer := buffer.push c.get!
    | .host | .hostname =>
      if overridden && url.scheme == "file" then
        p := p - 1
        state := .fileHost
      else if c == some ':' && !insideBrackets then
        if buffer.isEmpty then return .failure url
        if override == some .hostname then return .failure url
        match parseHost buffer (!special) with
        | none => return .failure url
        | some h =>
          url := { url with host := some h }
          buffer := ""
          state := .port
      else if isEof || c == some '/' || c == some '?' || c == some '#'
          || (special && c == some '\\') then
        p := p - 1
        if special && buffer.isEmpty then return .failure url
        else if overridden && buffer.isEmpty && (url.includesCredentials || url.port.isSome) then
          return .failure url
        match parseHost buffer (!special) with
        | none => return .failure url
        | some h =>
          url := { url with host := some h }
          buffer := ""
          state := .pathStart
          if overridden then return .ok url
      else
        if c == some '[' then insideBrackets := true
        if c == some ']' then insideBrackets := false
        buffer := buffer.push c.get!
    | .port =>
      if c.any isAsciiDigit then
        buffer := buffer.push c.get!
      else if isEof || c == some '/' || c == some '?' || c == some '#'
          || (special && c == some '\\') || overridden then
        if !buffer.isEmpty then
          let port := buffer.foldl (fun n d => n * 10 + (d.toNat - 48)) 0
          if port > 65535 then return .failure url
          url := { url with port := if defaultPort url.scheme == some port then none else some port }
          buffer := ""
          if overridden then return .ok url
        if overridden then return .failure url
        state := .pathStart
        p := p - 1
      else return .failure url
    | .file =>
      url := { url with scheme := "file", host := some .empty }
      if c == some '/' || c == some '\\' then
        state := .fileSlash
      else
        match base with
        | some b =>
          if b.scheme == "file" then
            url := { url with host := b.host, path := b.path, query := b.query }
            if c == some '?' then
              url := { url with query := some "" }
              state := .query
            else if c == some '#' then
              url := { url with fragment := some "" }
              state := .fragment
            else if !isEof then
              url := { url with query := none }
              if !startsWithWindowsDriveLetter (cs.toList.drop i) then url := url.shortenPath
              else url := { url with path := .segments #[] }
              state := .path
              p := p - 1
          else
            state := .path
            p := p - 1
        | none =>
          state := .path
          p := p - 1
    | .fileSlash =>
      if c == some '/' || c == some '\\' then
        state := .fileHost
      else
        match base with
        | some b =>
          if b.scheme == "file" then
            url := { url with host := b.host }
            if !startsWithWindowsDriveLetter (cs.toList.drop i) then
              match b.path with
              | .segments xs =>
                match xs[0]? with
                | some s0 => if isNormalizedWindowsDriveLetter s0 then url := url.appendSegment s0
                | none => pure ()
              | .opaque _ => pure ()
        | none => pure ()
        state := .path
        p := p - 1
    | .fileHost =>
      if isEof || c == some '/' || c == some '\\' || c == some '?' || c == some '#' then
        p := p - 1
        if !overridden && isWindowsDriveLetter buffer.toList then
          state := .path
        else if buffer.isEmpty then
          url := { url with host := some .empty }
          if overridden then return .ok url
          state := .pathStart
        else
          match parseHost buffer (!special) with
          | none => return .failure url
          | some h =>
            let h := if h == .domain "localhost" then Host.empty else h
            url := { url with host := some h }
            if overridden then return .ok url
            buffer := ""
            state := .pathStart
      else
        buffer := buffer.push c.get!
    | .pathStart =>
      if special then
        state := .path
        if c != some '/' && c != some '\\' then p := p - 1
      else if !overridden && c == some '?' then
        url := { url with query := some "" }
        state := .query
      else if !overridden && c == some '#' then
        url := { url with fragment := some "" }
        state := .fragment
      else if !isEof then
        state := .path
        if c != some '/' then p := p - 1
      else if overridden && url.host.isNone then
        url := url.appendSegment ""
    | .path =>
      if isEof || c == some '/' || (special && c == some '\\')
          || (!overridden && (c == some '?' || c == some '#')) then
        let slashLike := c == some '/' || (special && c == some '\\')
        url := url.pathSegment buffer slashLike
        buffer := ""
        if c == some '?' then
          url := { url with query := some "" }
          state := .query
        if c == some '#' then
          url := { url with fragment := some "" }
          state := .fragment
      else
        buffer := buffer ++ utf8PercentEncodeChar .path c.get!
    | .opaquePath =>
      if c == some '?' then
        url := { url with query := some "" }
        state := .query
      else if c == some '#' then
        url := { url with fragment := some "" }
        state := .fragment
      else if c == some ' ' then
        if rem0 == some '?' || rem0 == some '#' then url := url.appendSegment "%20"
        else url := url.appendSegment " "
      else if !isEof then
        url := url.appendSegment (utf8PercentEncodeChar .c0control c.get!)
    | .query =>
      if enc != .utf_8 && (!special || url.scheme == "ws" || url.scheme == "wss") then
        enc := .utf_8
      if (!overridden && c == some '#') || isEof then
        let set := if special then PercentEncodeSet.specialQuery else .query
        url := { url with query := some (url.query.getD "" ++ encodeQuery enc buffer set) }
        buffer := ""
        if c == some '#' then
          url := { url with fragment := some "" }
          state := .fragment
      else if !isEof then
        buffer := buffer.push c.get!
    | .fragment =>
      if !isEof then
        url := { url with fragment := some (url.fragment.getD "" ++ utf8PercentEncodeChar .fragment c.get!) }
    if p ≥ n then return .ok url
    p := p + 1
  return .failure url

/-! ## The URL serializer (section 4.5) -/

def Url.serializePath (u : Url) : String :=
  match u.path with
  | .opaque s => s
  | .segments xs => xs.foldl (fun acc s => acc ++ "/" ++ s) ""

def Url.serialize (u : Url) (excludeFragment := false) : String := Id.run do
  let mut out := u.scheme ++ ":"
  match u.host with
  | some h =>
    out := out ++ "//"
    if u.includesCredentials then
      out := out ++ u.username
      if !u.password.isEmpty then out := out ++ ":" ++ u.password
      out := out ++ "@"
    out := out ++ h.serialize
    match u.port with
    | some p => out := out ++ ":" ++ toString p
    | none => pure ()
  | none => pure ()
  match u.host, u.path with
  | none, .segments xs => if xs.size > 1 && xs[0]! == "" then out := out ++ "/."
  | _, _ => pure ()
  out := out ++ u.serializePath
  match u.query with
  | some q => out := out ++ "?" ++ q
  | none => pure ()
  if !excludeFragment then
    match u.fragment with
    | some f => out := out ++ "#" ++ f
    | none => pure ()
  return out

/-! ## The URL parser and the API (sections 4.4 and 6.1) -/

/-- The API URL parser of `new URL(input, base)`: `none` is a TypeError. -/
def parseUrl (input : String) (base : Option String := none) : Option Url :=
  match base with
  | none => (basicParse input).toOption
  | some b =>
    match (basicParse b).toOption with
    | none => none
    | some bu => (basicParse input (some bu)).toOption

/-! ## application/x-www-form-urlencoded (section 5) -/

def replacePlus (bs : ByteArray) : ByteArray :=
  bs.foldl (fun acc b => acc.push (if b == 0x2B then 0x20 else b)) ByteArray.empty

/-- The application/x-www-form-urlencoded parser. -/
def urlencodedParse (input : String) : List (String × String) :=
  -- Splitting the scalar values at `&` and `=` splits their UTF-8 bytes at
  -- 0x26 and 0x3D, as the standard does.
  (input.splitOn "&").filterMap fun s =>
    if s.isEmpty then none
    else
      let (name, value) :=
        match s.splitOn "=" with
        | [] => (s, "")
        | [a] => (a, "")
        | a :: rest => (a, "=".intercalate rest)
      let dec := fun (x : String) => utf8DecodeWithoutBOM (percentDecode (replacePlus x.toUTF8))
      some (dec name, dec value)

/-- The application/x-www-form-urlencoded serializer (UTF-8). -/
def urlencodedSerialize (tuples : List (String × String)) : String :=
  let enc := fun (s : String) =>
    s.foldl (fun acc c =>
      if c == ' ' then acc.push '+' else acc ++ utf8PercentEncodeChar .formUrlencoded c) ""
  "&".intercalate (tuples.map (fun (n, v) => enc n ++ "=" ++ enc v))

/-! ## Getters (section 6.1) -/

def Url.href (u : Url) : String := u.serialize
def Url.protocol (u : Url) : String := u.scheme ++ ":"
def Url.hostGetter (u : Url) : String :=
  match u.host with
  | none => ""
  | some h => match u.port with
    | none => h.serialize
    | some p => h.serialize ++ ":" ++ toString p
def Url.hostname (u : Url) : String := (u.host.map Host.serialize).getD ""
def Url.portGetter (u : Url) : String := (u.port.map toString).getD ""
def Url.pathname (u : Url) : String := u.serializePath
def Url.search (u : Url) : String :=
  match u.query with | none | some "" => "" | some q => "?" ++ q
def Url.hash (u : Url) : String :=
  match u.fragment with | none | some "" => "" | some f => "#" ++ f
def Url.searchParams (u : Url) : String :=
  urlencodedSerialize (urlencodedParse (u.query.getD ""))

/-! ## Origins (section 4.7) -/

/-- The ASCII serialization of a URL's origin; `"null"` for an opaque origin.
A blob URL entry is never present here. -/
def Url.origin (u : Url) : String :=
  let tuple := fun (v : Url) =>
    v.scheme ++ "://" ++ ((v.host.map Host.serialize).getD "") ++
      ((v.port.map (fun p => ":" ++ toString p)).getD "")
  match u.scheme with
  | "blob" =>
    match (basicParse u.serializePath).toOption with
    | some pu => if pu.scheme == "http" || pu.scheme == "https" then tuple pu else "null"
    | none => "null"
  | "ftp" | "http" | "https" | "ws" | "wss" => tuple u
  | _ => "null"

/-! ## Setters (section 6.1) -/

/-- Potentially strip trailing spaces from an opaque path. -/
def Url.stripTrailingSpacesFromOpaquePath (u : Url) : Url :=
  match u.path with
  | .opaque s =>
    if u.fragment.isSome || u.query.isSome then u
    else { u with path := .opaque (String.ofList (s.toList.reverse.dropWhile (· == ' ')).reverse) }
  | .segments _ => u

/-- Set an attribute of the URL class to a value; `none` is a TypeError
(the href setter given a URL that does not parse). -/
def Url.set (u : Url) (attr value : String) : Option Url :=
  match attr with
  | "href" => (basicParse value).toOption
  | "protocol" => some (basicParse (value ++ ":") none (some u) (some .schemeStart)).url
  | "username" =>
    if u.cannotHaveUsernamePasswordPort then some u
    else some { u with username := utf8PercentEncodeString .userinfo value }
  | "password" =>
    if u.cannotHaveUsernamePasswordPort then some u
    else some { u with password := utf8PercentEncodeString .userinfo value }
  | "host" =>
    if u.hasOpaquePath then some u
    else some (basicParse value none (some u) (some .host)).url
  | "hostname" =>
    if u.hasOpaquePath then some u
    else some (basicParse value none (some u) (some .hostname)).url
  | "port" =>
    if u.cannotHaveUsernamePasswordPort then some u
    else if value.isEmpty then some { u with port := none }
    else some (basicParse value none (some u) (some .port)).url
  | "pathname" =>
    if u.hasOpaquePath then some u
    else some (basicParse value none (some { u with path := .segments #[] }) (some .pathStart)).url
  | "search" =>
    if value.isEmpty then some { u with query := none }.stripTrailingSpacesFromOpaquePath
    else
      let input := if value.startsWith "?" then String.ofList (value.toList.drop 1) else value
      some (basicParse input none (some { u with query := some "" }) (some .query)).url
  | "hash" =>
    if value.isEmpty then some { u with fragment := none }.stripTrailingSpacesFromOpaquePath
    else
      let input := if value.startsWith "#" then String.ofList (value.toList.drop 1) else value
      some (basicParse input none (some { u with fragment := some "" }) (some .fragment)).url
  | _ => some u

#guard (parseUrl "http://example.com/a/../b").map Url.href == some "http://example.com/b"
#guard (parseUrl "../c?d#e" (some "http://x/a/b")).map Url.href == some "http://x/c?d#e"
#guard (parseUrl "file:///C|/x").map Url.href == some "file:///C:/x"
#guard (parseUrl "mailto:a@b").map Url.pathname == some "a@b"
#guard (parseUrl "http://[::1]:80/").map Url.href == some "http://[::1]/"
#guard (parseUrl "http://a:b@c:8080/?x=y z#f").map Url.href == some "http://a:b@c:8080/?x=y%20z#f"
#guard parseUrl "http://[::1" == none

end L4Factoidal.WHATWG.URL
