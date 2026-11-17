/-
L4Factoidal.WHATWG.URL.Parser — URLs of the WHATWG URL Standard: the URL
record (section 4.1), the basic URL parser with state override (section 4.4),
the URL serializer (section 4.5), origins (section 4.7), the
application/x-www-form-urlencoded parser and serializer (section 5), and the
attribute getters and setters of the URL class (section 6.1).

Specification: URL Standard, WHATWG Living Standard, Last Updated 19 October
2026 (commit snapshot whatwg/url `845bafca22fb0c5a42c4bf384a9bdea525a2f10d`). Tests: web-platform-tests `url/`
(third_party/testing/wpt-url), run by tests/whatwg-url/run.sh.

The parser is the standard's state machine, transcribed: the record `Machine`
holds url, state, buffer, the three flags and pointer; each state is one
function whose doc comment gives the standard's steps for it; `step` switches
on state and `run` is the loop. "Decrease pointer by 1" and "start over" are
pointer arithmetic, as in the standard. The loop has fuel `8 × (input length +
2)`; `Cost.basicParse_rounds_le` (URL/Cost.lean) proves that at most
`3 × (input length) + 16` rounds run, so the fuel never ends. The self-test
`l4whatwg-url selftest` parses inputs of 1,000,000 code points of each shape
that rewinds.

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

/-! ### The state machine

The standard's algorithm keeps *url*, *state*, *buffer*, the flags *atSignSeen*,
*insideBrackets* and *passwordTokenSeen*, and *pointer*, and runs one state per
round of "keep running the following state machine by switching on state".
Here those variables are the record `Machine`, each state of the standard is
one function (`stSchemeStart` … `stFragment`) whose doc comment gives the
steps of the standard it transcribes, `step` switches on state, and `run` is
the loop: after a state's steps, "if after a run pointer points to the EOF
code point, go to the next step; otherwise, increase pointer by 1 and
continue". "Decrease pointer by 1" and "start over (from the first code point
in input)" are pointer arithmetic, as in the standard: the increment that
follows makes the next round read the same code point again, or the first.

Validation errors are not reported; they do not change the result. -/

/-- What a run of the basic URL parser is given and does not change: the code
points of *input* (after the removal of leading and trailing C0 control or
space and of ASCII tab or newline), *base*, and *state override*. -/
structure ParseCfg where
  cs : Array Char
  base : Option Url
  override : Option State

/-- The variables of the basic URL parser. `enc` is *encoding*; `p` is
*pointer*, an index into the code points of *input*; it is −1 only between
"start over" and the increment that follows it. -/
structure Machine where
  url : Url
  state : State
  enc : Encoding
  buffer : String := ""
  atSignSeen : Bool := false
  insideBrackets : Bool := false
  passwordTokenSeen : Bool := false
  p : Int := 0

/-- What one state's steps give: the variables for the next round, or the
return value of the parser. -/
inductive Step where
  | next (m : Machine)
  | done (r : ParseResult)

/-- *c*: the code point *pointer* points to, `none` for the EOF code point. -/
@[inline] def ParseCfg.charAt (cfg : ParseCfg) (p : Int) : Option Char :=
  if p ≥ 0 then cfg.cs[p.toNat]? else none

/-- The first code point of *remaining* (the code point after *c*). -/
@[inline] def ParseCfg.next (cfg : ParseCfg) (p : Int) : Option Char := cfg.cs[p.toNat + 1]?

@[inline] def ParseCfg.overridden (cfg : ParseCfg) : Bool := cfg.override.isSome

/-- "Decrease pointer by 1." -/
@[inline] def Machine.back (m : Machine) : Machine := { m with p := m.p - 1 }

/-- The standard's test "c is the EOF code point, U+002F (/), U+003F (?), or
U+0023 (#), or url is special and c is U+005C (\)", used by the authority,
host and port states. -/
@[inline] def endsAuthority (special : Bool) (c : Option Char) : Bool :=
  c.isNone || c == some '/' || c == some '?' || c == some '#' || (special && c == some '\\')

/-- **Scheme start state.**
1. If c is an ASCII alpha, append c, lowercased, to buffer, and set state to
   scheme state.
2. Otherwise, if state override is not given, set state to no scheme state
   and decrease pointer by 1.
3. Otherwise, return failure. -/
def stSchemeStart (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  match c with
  | some ch =>
    if isAsciiAlpha ch then .next { m with buffer := m.buffer.push (asciiLower ch), state := .scheme }
    else if !cfg.overridden then .next { m with state := .noScheme, p := m.p - 1 }
    else .done (.failure m.url)
  | none =>
    if !cfg.overridden then .next { m with state := .noScheme, p := m.p - 1 }
    else .done (.failure m.url)

/-- Scheme state, step 2 (c is U+003A (:)), after the checks of step 2.1.
2.2. Set url's scheme to buffer.
2.3. If state override is given: if url's port is url's scheme's default
     port, set url's port to null; return.
2.4. Set buffer to the empty string.
2.5. If url's scheme is "file", set state to file state.
2.6. Otherwise, if url is special, base is non-null, and base's scheme is
     url's scheme, set state to special relative or authority state.
2.7. Otherwise, if url is special, set state to special authority slashes
     state.
2.8. Otherwise, if remaining starts with U+002F (/), set state to path or
     authority state and increase pointer by 1.
2.9. Otherwise, set url's path to the empty string and set state to opaque
     path state. -/
def stSchemeColon (cfg : ParseCfg) (m : Machine) : Step :=
  let url := { m.url with scheme := m.buffer }
  if cfg.overridden then
    .done (.ok (if url.port.isSome && url.port == defaultPort url.scheme then { url with port := none } else url))
  else if url.scheme == "file" then .next { m with url := url, buffer := "", state := .file }
  else if url.isSpecial && cfg.base.isSome && (cfg.base.map (·.scheme)) == some url.scheme then
    .next { m with url := url, buffer := "", state := .specialRelativeOrAuthority }
  else if url.isSpecial then .next { m with url := url, buffer := "", state := .specialAuthoritySlashes }
  else if cfg.next m.p == some '/' then
    .next { m with url := url, buffer := "", state := .pathOrAuthority, p := m.p + 1 }
  else .next { m with url := { url with path := .opaque "" }, buffer := "", state := .opaquePath }

/-- **Scheme state.**
1. If c is an ASCII alphanumeric, U+002B (+), U+002D (-), or U+002E (.),
   append c, lowercased, to buffer.
2. Otherwise, if c is U+003A (:):
   2.1. If state override is given, return (url unchanged) when: url's scheme
        is a special scheme and buffer is not; or url's scheme is not a
        special scheme and buffer is; or url includes credentials or has a
        non-null port, and buffer is "file"; or url's scheme is "file" and
        its host is an empty host.
   then steps 2.2 to 2.9 (`stSchemeColon`).
3. Otherwise, if state override is not given, set buffer to the empty
   string, state to no scheme state, and start over (from the first code
   point in input).
4. Otherwise, return failure. -/
def stScheme (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  match c with
  | some ch =>
    if isAsciiAlpha ch || isAsciiDigit ch || ch == '+' || ch == '-' || ch == '.' then
      .next { m with buffer := m.buffer.push (asciiLower ch) }
    else if ch == ':' then
      if cfg.overridden &&
          ((m.url.isSpecial && !isSpecialScheme m.buffer)
            || (!m.url.isSpecial && isSpecialScheme m.buffer)
            || ((m.url.includesCredentials || m.url.port.isSome) && m.buffer == "file")
            || (m.url.scheme == "file" && m.url.host == some .empty)) then
        .done (.ok m.url)
      else stSchemeColon cfg m
    else if !cfg.overridden then .next { m with buffer := "", state := .noScheme, p := -1 }
    else .done (.failure m.url)
  | none =>
    if !cfg.overridden then .next { m with buffer := "", state := .noScheme, p := -1 }
    else .done (.failure m.url)

/-- **No scheme state.**
1. If base is null, or base has an opaque path and c is not U+0023 (#),
   return failure.
2. Otherwise, if base has an opaque path and c is U+0023 (#), set url's
   scheme to base's scheme, url's path to base's path, url's query to base's
   query, url's fragment to the empty string, and set state to fragment
   state.
3. Otherwise, if base's scheme is not "file", set state to relative state
   and decrease pointer by 1.
4. Otherwise, set state to file state and decrease pointer by 1. -/
def stNoScheme (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  match cfg.base with
  | none => .done (.failure m.url)
  | some b =>
    if b.hasOpaquePath && c != some '#' then .done (.failure m.url)
    else if b.hasOpaquePath && c == some '#' then
      .next { m with url := { m.url with scheme := b.scheme, path := b.path, query := b.query,
                                         fragment := some "" },
                     state := .fragment }
    else if b.scheme != "file" then .next { m with state := .relative, p := m.p - 1 }
    else .next { m with state := .file, p := m.p - 1 }

/-- **Special relative or authority state.**
1. If c is U+002F (/) and remaining starts with U+002F (/), set state to
   special authority ignore slashes state and increase pointer by 1.
2. Otherwise, set state to relative state and decrease pointer by 1. -/
def stSpecialRelativeOrAuthority (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  if c == some '/' && cfg.next m.p == some '/' then
    .next { m with state := .specialAuthorityIgnoreSlashes, p := m.p + 1 }
  else .next { m with state := .relative, p := m.p - 1 }

/-- **Path or authority state.**
1. If c is U+002F (/), set state to authority state.
2. Otherwise, set state to path state and decrease pointer by 1. -/
def stPathOrAuthority (m : Machine) (c : Option Char) : Step :=
  if c == some '/' then .next { m with state := .authority }
  else .next { m with state := .path, p := m.p - 1 }

/-- **Relative state.** (base is non-null and its scheme is not "file".)
1. Set url's scheme to base's scheme.
2. If c is U+002F (/), set state to relative slash state.
3. Otherwise, if url is special and c is U+005C (\), set state to relative
   slash state.
4. Otherwise: set url's username, password, host, port, path and query to
   base's; then
   - if c is U+003F (?), set url's query to the empty string and state to
     query state;
   - otherwise, if c is U+0023 (#), set url's fragment to the empty string
     and state to fragment state;
   - otherwise, if c is not the EOF code point: set url's query to null,
     shorten url's path, set state to path state and decrease pointer by 1. -/
def stRelative (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  let b := cfg.base.getD {}
  let url := { m.url with scheme := b.scheme }
  if c == some '/' then .next { m with url := url, state := .relativeSlash }
  else if url.isSpecial && c == some '\\' then .next { m with url := url, state := .relativeSlash }
  else
    let url := { url with username := b.username, password := b.password, host := b.host,
                          port := b.port, path := b.path, query := b.query }
    if c == some '?' then .next { m with url := { url with query := some "" }, state := .query }
    else if c == some '#' then .next { m with url := { url with fragment := some "" }, state := .fragment }
    else if c.isSome then
      .next { m with url := ({ url with query := none } : Url).shortenPath, state := .path, p := m.p - 1 }
    else .next { m with url := url }

/-- **Relative slash state.**
1. If url is special and c is U+002F (/) or U+005C (\), set state to special
   authority ignore slashes state.
2. Otherwise, if c is U+002F (/), set state to authority state.
3. Otherwise, set url's username, password, host and port to base's, set
   state to path state, and decrease pointer by 1. -/
def stRelativeSlash (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  if m.url.isSpecial && (c == some '/' || c == some '\\') then
    .next { m with state := .specialAuthorityIgnoreSlashes }
  else if c == some '/' then .next { m with state := .authority }
  else
    let b := cfg.base.getD {}
    .next { m with url := { m.url with username := b.username, password := b.password, host := b.host,
                                       port := b.port },
                   state := .path, p := m.p - 1 }

/-- **Special authority slashes state.**
1. If c is U+002F (/) and remaining starts with U+002F (/), set state to
   special authority ignore slashes state and increase pointer by 1.
2. Otherwise, set state to special authority ignore slashes state and
   decrease pointer by 1. -/
def stSpecialAuthoritySlashes (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  if c == some '/' && cfg.next m.p == some '/' then
    .next { m with state := .specialAuthorityIgnoreSlashes, p := m.p + 1 }
  else .next { m with state := .specialAuthorityIgnoreSlashes, p := m.p - 1 }

/-- **Special authority ignore slashes state.**
1. If c is neither U+002F (/) nor U+005C (\), set state to authority state
   and decrease pointer by 1.
2. Otherwise (a validation error only), go on. -/
def stSpecialAuthorityIgnoreSlashes (m : Machine) (c : Option Char) : Step :=
  if c != some '/' && c != some '\\' then .next { m with state := .authority, p := m.p - 1 }
  else .next m

/-- Authority state, step 1.4, for one code point of buffer: the first
U+003A (:) sets passwordTokenSeen; every other code point is UTF-8
percent-encoded with the userinfo percent-encode set and appended to url's
password if passwordTokenSeen is true, to url's username otherwise. The pair
is (url, passwordTokenSeen). -/
def addCredential (acc : Url × Bool) (cp : Char) : Url × Bool :=
  if cp == ':' && !acc.2 then (acc.1, true)
  else
    let pe := utf8PercentEncodeChar .userinfo cp
    if acc.2 then ({ acc.1 with password := acc.1.password ++ pe }, acc.2)
    else ({ acc.1 with username := acc.1.username ++ pe }, acc.2)

/-- **Authority state.**
1. If c is U+0040 (@):
   1.2. If atSignSeen is true, prepend "%40" to buffer.
   1.3. Set atSignSeen to true.
   1.4. For each code point in buffer: `addCredential`.
   1.5. Set buffer to the empty string.
2. Otherwise, if c is the EOF code point, U+002F (/), U+003F (?), or
   U+0023 (#), or url is special and c is U+005C (\):
   2.1. If atSignSeen is true and buffer is the empty string, return failure.
   2.2. Decrease pointer by buffer's code point length + 1, set buffer to
        the empty string, and set state to host state.
3. Otherwise, append c to buffer. -/
def stAuthority (m : Machine) (c : Option Char) : Step :=
  match c with
  | some '@' =>
    let buffer := if m.atSignSeen then "%40" ++ m.buffer else m.buffer
    let (url, seen) := buffer.toList.foldl addCredential (m.url, m.passwordTokenSeen)
    .next { m with url := url, passwordTokenSeen := seen, atSignSeen := true, buffer := "" }
  | _ =>
    if endsAuthority m.url.isSpecial c then
      if m.atSignSeen && m.buffer.isEmpty then .done (.failure m.url)
      else .next { m with p := m.p - (m.buffer.length + 1 : Nat), buffer := "", state := .host }
    else .next { m with buffer := m.buffer.push c.get! }

/-- **Host state** and **hostname state.**
1. If state override is given and url's scheme is "file", decrease pointer
   by 1 and set state to file host state.
2. Otherwise, if c is U+003A (:) and insideBrackets is false:
   2.1. If buffer is the empty string, return failure.
   2.2. If state override is given and state override is hostname state,
        return failure.
   2.3. Let host be the result of host parsing buffer with url is not
        special. 2.4. If host is failure, return failure.
   2.5. Set url's host to host, buffer to the empty string, and state to
        port state.
3. Otherwise, if c is the EOF code point, U+002F (/), U+003F (?), or
   U+0023 (#), or url is special and c is U+005C (\), decrease pointer by 1,
   and then:
   3.1. If url is special and buffer is the empty string, return failure.
   3.2. Otherwise, if state override is given, buffer is the empty string,
        and either url includes credentials or url's port is non-null,
        return failure.
   3.3. Let host be the result of host parsing buffer with url is not
        special. 3.4. If host is failure, return failure.
   3.5. Set url's host to host, buffer to the empty string, and state to
        path start state.
   3.6. If state override is given, return.
4. Otherwise: if c is U+005B ([), set insideBrackets to true; if c is
   U+005D (]), set insideBrackets to false; append c to buffer. -/
def stHost (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  let special := m.url.isSpecial
  if cfg.overridden && m.url.scheme == "file" then .next { m with p := m.p - 1, state := .fileHost }
  else if c == some ':' && !m.insideBrackets then
    if m.buffer.isEmpty then .done (.failure m.url)
    else if cfg.override == some .hostname then .done (.failure m.url)
    else
      match parseHost m.buffer (!special) with
      | none => .done (.failure m.url)
      | some h => .next { m with url := { m.url with host := some h }, buffer := "", state := .port }
  else if endsAuthority special c then
    if special && m.buffer.isEmpty then .done (.failure m.url)
    else if cfg.overridden && m.buffer.isEmpty && (m.url.includesCredentials || m.url.port.isSome) then
      .done (.failure m.url)
    else
      match parseHost m.buffer (!special) with
      | none => .done (.failure m.url)
      | some h =>
        let url := { m.url with host := some h }
        if cfg.overridden then .done (.ok url)
        else .next { m with url := url, buffer := "", state := .pathStart, p := m.p - 1 }
  else
    let ib := if c == some ']' then false else if c == some '[' then true else m.insideBrackets
    .next { m with insideBrackets := ib, buffer := m.buffer.push c.get! }

/-- **Port state.**
1. If c is an ASCII digit, append c to buffer.
2. Otherwise, if c is the EOF code point, U+002F (/), U+003F (?), or
   U+0023 (#); or url is special and c is U+005C (\); or state override is
   given:
   2.1. If buffer is not the empty string: let port be the mathematical
        integer value that buffer represents in radix 10; if port is not a
        16-bit unsigned integer, return failure; set url's port to null if
        port is url's scheme's default port, otherwise to port; set buffer
        to the empty string; if state override is given, return.
   2.2. If state override is given, return failure.
   2.3. Set state to path start state and decrease pointer by 1.
3. Otherwise, return failure. -/
def stPort (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  if c.any isAsciiDigit then .next { m with buffer := m.buffer.push c.get! }
  else if endsAuthority m.url.isSpecial c || cfg.overridden then
    if !m.buffer.isEmpty then
      let port := m.buffer.foldl (fun n d => n * 10 + (d.toNat - 48)) 0
      if port > 65535 then .done (.failure m.url)
      else
        let url := { m.url with port := if defaultPort m.url.scheme == some port then none else some port }
        if cfg.overridden then .done (.ok url)
        else .next { m with url := url, buffer := "", state := .pathStart, p := m.p - 1 }
    else if cfg.overridden then .done (.failure m.url)
    else .next { m with state := .pathStart, p := m.p - 1 }
  else .done (.failure m.url)

/-- **File state.**
1. Set url's scheme to "file". 2. Set url's host to the empty string.
3. If c is U+002F (/) or U+005C (\), set state to file slash state.
4. Otherwise, if base is non-null and base's scheme is "file":
   4.1. Set url's host, path and query to base's.
   4.2. If c is U+003F (?), set url's query to the empty string and state to
        query state.
   4.3. Otherwise, if c is U+0023 (#), set url's fragment to the empty
        string and state to fragment state.
   4.4. Otherwise, if c is not the EOF code point: set url's query to null;
        if the code point substring from pointer to the end of input does
        not start with a Windows drive letter, shorten url's path;
        otherwise set url's path to « »; set state to path state and
        decrease pointer by 1.
5. Otherwise, set state to path state, and decrease pointer by 1. -/
def stFile (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  let url := { m.url with scheme := "file", host := some .empty }
  if c == some '/' || c == some '\\' then .next { m with url := url, state := .fileSlash }
  else
    match cfg.base with
    | some b =>
      if b.scheme == "file" then
        let url := { url with host := b.host, path := b.path, query := b.query }
        if c == some '?' then .next { m with url := { url with query := some "" }, state := .query }
        else if c == some '#' then .next { m with url := { url with fragment := some "" }, state := .fragment }
        else if c.isSome then
          let url := { url with query := none }
          let url :=
            if !startsWithWindowsDriveLetter (cfg.cs.toList.drop m.p.toNat) then url.shortenPath
            else { url with path := .segments #[] }
          .next { m with url := url, state := .path, p := m.p - 1 }
        else .next { m with url := url }
      else .next { m with url := url, state := .path, p := m.p - 1 }
    | none => .next { m with url := url, state := .path, p := m.p - 1 }

/-- **File slash state.**
1. If c is U+002F (/) or U+005C (\), set state to file host state.
2. Otherwise:
   2.1. If base is non-null and base's scheme is "file": set url's host to
        base's host; if the code point substring from pointer to the end of
        input does not start with a Windows drive letter and base's path[0]
        is a normalized Windows drive letter, append base's path[0] to
        url's path.
   2.2. Set state to path state, and decrease pointer by 1. -/
def stFileSlash (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  if c == some '/' || c == some '\\' then .next { m with state := .fileHost }
  else
    let url :=
      match cfg.base with
      | some b =>
        if b.scheme == "file" then
          let url := { m.url with host := b.host }
          if !startsWithWindowsDriveLetter (cfg.cs.toList.drop m.p.toNat) then
            match b.path with
            | .segments xs =>
              match xs[0]? with
              | some s0 => if isNormalizedWindowsDriveLetter s0 then url.appendSegment s0 else url
              | none => url
            | .opaque _ => url
          else url
        else m.url
      | none => m.url
    .next { m with url := url, state := .path, p := m.p - 1 }

/-- **File host state.**
1. If c is the EOF code point, U+002F (/), U+005C (\), U+003F (?), or
   U+0023 (#), decrease pointer by 1 and then:
   1.1. If state override is not given and buffer is a Windows drive letter,
        set state to path state (buffer is kept for the path state).
   1.2. Otherwise, if buffer is the empty string: set url's host to the
        empty string; if state override is given, return; set state to path
        start state.
   1.3. Otherwise: let host be the result of host parsing buffer with url is
        not special; if host is failure, return failure; if host is
        "localhost", set host to the empty string; set url's host to host;
        if state override is given, return; set buffer to the empty string
        and state to path start state.
2. Otherwise, append c to buffer. -/
def stFileHost (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  if c.isNone || c == some '/' || c == some '\\' || c == some '?' || c == some '#' then
    if !cfg.overridden && isWindowsDriveLetter m.buffer.toList then
      .next { m with state := .path, p := m.p - 1 }
    else if m.buffer.isEmpty then
      let url := { m.url with host := some .empty }
      if cfg.overridden then .done (.ok url)
      else .next { m with url := url, state := .pathStart, p := m.p - 1 }
    else
      match parseHost m.buffer (!m.url.isSpecial) with
      | none => .done (.failure m.url)
      | some h =>
        let url := { m.url with host := some (if h == .domain "localhost" then Host.empty else h) }
        if cfg.overridden then .done (.ok url)
        else .next { m with url := url, buffer := "", state := .pathStart, p := m.p - 1 }
  else .next { m with buffer := m.buffer.push c.get! }

/-- **Path start state.**
1. If url is special, set state to path state; if c is neither U+002F (/)
   nor U+005C (\), decrease pointer by 1.
2. Otherwise, if state override is not given and c is U+003F (?), set url's
   query to the empty string and state to query state.
3. Otherwise, if state override is not given and c is U+0023 (#), set url's
   fragment to the empty string and state to fragment state.
4. Otherwise, if c is not the EOF code point, set state to path state; if c
   is not U+002F (/), decrease pointer by 1.
5. Otherwise, if state override is given and url's host is null, append the
   empty string to url's path. -/
def stPathStart (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  if m.url.isSpecial then
    if c != some '/' && c != some '\\' then .next { m with state := .path, p := m.p - 1 }
    else .next { m with state := .path }
  else if !cfg.overridden && c == some '?' then
    .next { m with url := { m.url with query := some "" }, state := .query }
  else if !cfg.overridden && c == some '#' then
    .next { m with url := { m.url with fragment := some "" }, state := .fragment }
  else if c.isSome then
    if c != some '/' then .next { m with state := .path, p := m.p - 1 }
    else .next { m with state := .path }
  else if cfg.overridden && m.url.host.isNone then .next { m with url := m.url.appendSegment "" }
  else .next m

/-- **Path state.**
1. If c is the EOF code point or U+002F (/); or url is special and c is
   U+005C (\); or state override is not given and c is U+003F (?) or
   U+0023 (#): the rule for the segment in buffer (`Url.pathSegment`); set
   buffer to the empty string; if c is U+003F (?), set url's query to the
   empty string and state to query state; if c is U+0023 (#), set url's
   fragment to the empty string and state to fragment state.
2. Otherwise, UTF-8 percent-encode c using the path percent-encode set and
   append the result to buffer. -/
def stPath (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  let special := m.url.isSpecial
  if c.isNone || c == some '/' || (special && c == some '\\')
      || (!cfg.overridden && (c == some '?' || c == some '#')) then
    let url := m.url.pathSegment m.buffer (c == some '/' || (special && c == some '\\'))
    if c == some '?' then .next { m with url := { url with query := some "" }, buffer := "", state := .query }
    else if c == some '#' then
      .next { m with url := { url with fragment := some "" }, buffer := "", state := .fragment }
    else .next { m with url := url, buffer := "" }
  else .next { m with buffer := m.buffer ++ utf8PercentEncodeChar .path c.get! }

/-- **Opaque path state.**
1. If c is U+003F (?), set url's query to the empty string and state to
   query state.
2. Otherwise, if c is U+0023 (#), set url's fragment to the empty string and
   state to fragment state.
3. Otherwise, if c is U+0020 SPACE: if remaining starts with U+003F (?) or
   U+0023 (#), append "%20" to url's path; otherwise append U+0020 SPACE.
4. Otherwise, if c is not the EOF code point, UTF-8 percent-encode c using
   the C0 control percent-encode set and append the result to url's path. -/
def stOpaquePath (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  if c == some '?' then .next { m with url := { m.url with query := some "" }, state := .query }
  else if c == some '#' then .next { m with url := { m.url with fragment := some "" }, state := .fragment }
  else if c == some ' ' then
    let r := cfg.next m.p
    if r == some '?' || r == some '#' then .next { m with url := m.url.appendSegment "%20" }
    else .next { m with url := m.url.appendSegment " " }
  else if c.isSome then
    .next { m with url := m.url.appendSegment (utf8PercentEncodeChar .c0control c.get!) }
  else .next m

/-- **Query state.**
1. If encoding is not UTF-8 and url is not special, or url's scheme is "ws"
   or "wss", set encoding to UTF-8.
2. If state override is not given and c is U+0023 (#), or c is the EOF code
   point: percent-encode after encoding, with encoding, buffer, and the
   special-query percent-encode set if url is special, the query
   percent-encode set otherwise; append the result to url's query; set
   buffer to the empty string; if c is U+0023 (#), set url's fragment to
   the empty string and state to fragment state.
3. Otherwise, if c is not the EOF code point, append c to buffer. -/
def stQuery (cfg : ParseCfg) (m : Machine) (c : Option Char) : Step :=
  let special := m.url.isSpecial
  let enc :=
    if m.enc != .utf_8 && (!special || m.url.scheme == "ws" || m.url.scheme == "wss") then Encoding.utf_8
    else m.enc
  if (!cfg.overridden && c == some '#') || c.isNone then
    let set := if special then PercentEncodeSet.specialQuery else .query
    let url := { m.url with query := some (m.url.query.getD "" ++ encodeQuery enc m.buffer set) }
    if c == some '#' then
      .next { m with enc := enc, url := { url with fragment := some "" }, buffer := "", state := .fragment }
    else .next { m with enc := enc, url := url, buffer := "" }
  else .next { m with enc := enc, buffer := m.buffer.push c.get! }

/-- **Fragment state.** If c is not the EOF code point, UTF-8 percent-encode
c using the fragment percent-encode set and append the result to url's
fragment. -/
def stFragment (m : Machine) (c : Option Char) : Step :=
  match c with
  | some ch =>
    let f := m.url.fragment.getD "" ++ utf8PercentEncodeChar .fragment ch
    .next { m with url := { m.url with fragment := some f } }
  | none => .next m

/-- One round of the state machine: the steps of the current state, with c
the code point at pointer. -/
def step (cfg : ParseCfg) (m : Machine) : Step :=
  let c := cfg.charAt m.p
  match m.state with
  | .schemeStart => stSchemeStart cfg m c
  | .scheme => stScheme cfg m c
  | .noScheme => stNoScheme cfg m c
  | .specialRelativeOrAuthority => stSpecialRelativeOrAuthority cfg m c
  | .pathOrAuthority => stPathOrAuthority m c
  | .relative => stRelative cfg m c
  | .relativeSlash => stRelativeSlash cfg m c
  | .specialAuthoritySlashes => stSpecialAuthoritySlashes cfg m c
  | .specialAuthorityIgnoreSlashes => stSpecialAuthorityIgnoreSlashes m c
  | .authority => stAuthority m c
  | .host | .hostname => stHost cfg m c
  | .port => stPort cfg m c
  | .file => stFile cfg m c
  | .fileSlash => stFileSlash cfg m c
  | .fileHost => stFileHost cfg m c
  | .pathStart => stPathStart cfg m c
  | .path => stPath cfg m c
  | .opaquePath => stOpaquePath cfg m c
  | .query => stQuery cfg m c
  | .fragment => stFragment m c

/-- The loop of the state machine, at most `fuel` rounds: run the current
state; "if after a run pointer points to the EOF code point, go to the next
step" (return url); "otherwise, increase pointer by 1 and continue". When
the fuel ends the result is failure; `Cost.run_fuel_irrelevant` (URL/Cost.lean) shows
that the fuel `basicParse` gives is never used up.

Irreducible: the fuel `8 × (n + 2)` reduces to a successor even for an unknown input, so
without it `whnf` of `parseUrl x` (a `match` on it, in a proof about a caller) would
unfold round after round of the machine until it ran out of heartbeats. Proofs about
`run` use its equations (`rw [run]`, `unfold run`). -/
@[irreducible] def run (cfg : ParseCfg) : Nat → Machine → ParseResult
  | 0, m => .failure m.url
  | fuel + 1, m =>
    match step cfg m with
    | .done r => r
    | .next m' => if m'.p ≥ cfg.cs.size then .ok m'.url else run cfg fuel { m' with p := m'.p + 1 }

/-- The fixed part of a run: *input* with leading and trailing C0 control or
space removed (when no url is given) and ASCII tab or newline removed. -/
def parseCfg (input0 : String) (base urlIn : Option Url) (override : Option State) : ParseCfg :=
  let input := removeTabNewline (if urlIn.isNone then trimC0Space input0 else input0)
  { cs := input.toList.toArray, base := base, override := override }

/-- The variables at the start: url (a new URL if none is given), state
override or scheme start state, an empty buffer, the flags false, pointer at
the first code point. -/
def initMachine (urlIn : Option Url) (override : Option State) (encoding : Encoding) : Machine :=
  { url := urlIn.getD {}, state := override.getD .schemeStart, enc := encoding }

/-- The basic URL parser: input, an optional base, an optional url and state
override, and an encoding (UTF-8 by default). -/
def basicParse (input0 : String) (base : Option Url := none) (urlIn : Option Url := none)
    (override : Option State := none) (encoding : Encoding := .utf_8) : ParseResult :=
  let cfg := parseCfg input0 base urlIn override
  run cfg (8 * (cfg.cs.size + 2)) (initMachine urlIn override encoding)


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
