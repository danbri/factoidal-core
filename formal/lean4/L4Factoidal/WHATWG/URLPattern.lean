/-
L4Factoidal.WHATWG.URLPattern — the URL Pattern Standard (https://urlpattern.spec.whatwg.org/):
pattern strings (tokenizer, part list, regular expression and pattern string generation), the
constructor string parser, canonicalization through the URL parser, and matching.

Everything here is a pure function of strings. `create` is the constructor of `URLPattern`
(a compiled pattern or the message of its TypeError) and `exec` is its `exec()`; the page
object is glue over them (`JS/Interp.lean`, `NativeX.urlPattern`, and the class in
`tools/wasmvm/quickjs/prelude.js`). Section names in the comments are the Standard's.

Regular expressions are compiled and run by the engine's own `JS.Re` (the Standard creates a
RegExp with the `v` flag; `JS.Re` reads the same pattern text without the `v`-only set
operations). No `partial`, no `sorry`.
-/
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.JS.Regex
import L4Factoidal.Regex.XPath40

namespace L4Factoidal.WHATWG.URLPattern

open L4Factoidal.WHATWG.URL

/-! ## Tokens (section 2.1, "Parsing pattern strings") -/

inductive TokType where
  | open_ | close | regexp | name | char | escapedChar | otherModifier | asterisk | end_ | invalidChar
  deriving DecidableEq, Repr, Inhabited

/-- A token: its type, the index of its first code point in the pattern, and its value. -/
structure Tok where
  type : TokType
  index : Nat
  value : String
  deriving Repr, Inhabited

def inRanges (rs : List (Nat × Nat)) (c : Nat) : Bool := rs.any fun (a, b) => a ≤ c && c ≤ b

/-- The code points above ASCII that may start a name: General_Category L and Nl (ID_Start
without the few Other_ID_Start characters), from the Unicode tables of `Regex.UnicodeProps`. -/
def idStartRanges : Thunk (List (Nat × Nat)) :=
  Thunk.mk fun _ => ((L4Factoidal.Regex.XPath40.categoryRanges "L").getD []) ++
    ((L4Factoidal.Regex.XPath40.categoryRanges "Nl").getD [])

/-- The further code points above ASCII that may continue a name: Mn, Mc, Nd, Pc. -/
def idContinueRanges : Thunk (List (Nat × Nat)) :=
  Thunk.mk fun _ => ["Mn", "Mc", "Nd", "Pc"].flatMap fun k => (L4Factoidal.Regex.XPath40.categoryRanges k).getD []

/-- A valid name code point: IdentifierStart for the first, IdentifierPart after (ECMA-262
§12.7, with General_Category standing for ID_Start and ID_Continue above ASCII). -/
def validNameChar (c : Char) (first : Bool) : Bool :=
  let n := c.toNat
  if n < 128 then c.isAlpha || c == '$' || c == '_' || (!first && c.isDigit)
  else inRanges idStartRanges.get n ||
    -- Other_ID_Start (PropList.txt)
    n == 0x1885 || n == 0x1886 || n == 0x2118 || n == 0x212E || n == 0x309B || n == 0x309C ||
    (!first && (inRanges idContinueRanges.get n || n == 0x200C || n == 0x200D ||
      -- Other_ID_Continue
      n == 0xB7 || n == 0x387 || (0x1369 ≤ n && n ≤ 0x1371) || n == 0x19DA || n == 0x30FB || n == 0xFF65))

def strOf (cs : Array Char) (a b : Nat) : String := String.ofList (cs.extract a b).toList

/-- The token that starts at `i` and the index after it; `none` for a tokenizing error whose
next token starts at the index given (section 2.1.1, one turn of the loop). -/
def tokenAt (cs : Array Char) (i : Nat) : Tok × Nat ⊕ Nat :=
  let c := cs[i]!
  if c == '*' then .inl (⟨.asterisk, i, "*"⟩, i + 1)
  else if c == '+' || c == '?' then .inl (⟨.otherModifier, i, c.toString⟩, i + 1)
  else if c == '\\' then
    if i + 1 ≥ cs.size then .inr (i + 1)
    else .inl (⟨.escapedChar, i, cs[i + 1]!.toString⟩, i + 2)
  else if c == '{' then .inl (⟨.open_, i, "{"⟩, i + 1)
  else if c == '}' then .inl (⟨.close, i, "}"⟩, i + 1)
  else if c == ':' then
    let start := i + 1
    let stop := Id.run do
      let mut p := start
      for _ in [0:cs.size] do
        if p < cs.size && validNameChar cs[p]! (p == start) then p := p + 1 else break
      return p
    if stop ≤ start then .inr start else .inl (⟨.name, i, strOf cs start stop⟩, stop)
  else if c == '(' then
    -- the body of a regexp group: ASCII only, no `?` first, groups inside are `(?...)`
    let start := i + 1
    let (stop, depth, bad) := Id.run do
      let mut p := start
      let mut depth := 1
      let mut bad := false
      for _ in [0:cs.size + 1] do
        if p ≥ cs.size || bad || depth == 0 then break
        let d := cs[p]!
        if d.toNat ≥ 128 then bad := true
        else if p == start && d == '?' then bad := true
        else if d == '\\' then
          if p + 1 ≥ cs.size then bad := true
          else if cs[p + 1]!.toNat ≥ 128 then bad := true
          else p := p + 2
        else if d == ')' then
          depth := depth - 1
          p := p + 1
        else if d == '(' then
          depth := depth + 1
          if p + 1 ≥ cs.size then bad := true
          else if cs[p + 1]! != '?' then bad := true
          else p := p + 1
        else p := p + 1
      return (p, depth, bad)
    if bad || depth != 0 || stop - start - 1 == 0 then .inr start
    else .inl (⟨.regexp, i, strOf cs start (stop - 1)⟩, stop)
  else .inl (⟨.char, i, c.toString⟩, i + 1)

/-- Tokenize a pattern (section 2.1.1). `strict`: an error is a TypeError (`none`); else it
becomes an `invalidChar` token. The index grows at each turn, so `fuel` (the length plus
one) is enough; the loop is a tail call. -/
def tokenizeGo (cs : Array Char) (strict : Bool) : Nat → Nat → Array Tok → Option (Array Tok)
  | 0, i, acc => some (acc.push ⟨.end_, i, ""⟩)
  | fuel + 1, i, acc =>
    if i ≥ cs.size then some (acc.push ⟨.end_, i, ""⟩) else
    match tokenAt cs i with
    | .inl (tok, next) => tokenizeGo cs strict fuel next (acc.push tok)
    | .inr next =>
      if strict then none
      else tokenizeGo cs strict fuel (max next (i + 1)) (acc.push ⟨.invalidChar, i, strOf cs i (max next (i + 1))⟩)

def tokenize (cs : Array Char) (strict : Bool) : Option (Array Tok) :=
  tokenizeGo cs strict (cs.size + 1) 0 #[]

/-! ## Parts (section 2.1.2) -/

inductive PartType where
  | fixedText | regexp | segmentWildcard | fullWildcard
  deriving DecidableEq, Repr, Inhabited

inductive Modifier where
  | none | optional | zeroOrMore | oneOrMore
  deriving DecidableEq, Repr, Inhabited

structure Part where
  type : PartType
  value : String
  modifier : Modifier
  name : String := ""
  prefix_ : String := ""
  suffix : String := ""
  deriving DecidableEq, Repr, Inhabited

/-- The options of a component: the delimiter and prefix code points ("" for none). -/
structure Options where
  delimiter : String := ""
  prefix_ : String := ""
  ignoreCase : Bool := false
  deriving Repr, Inhabited

def hostnameOptions : Options := { delimiter := "." }
def pathnameOptions : Options := { delimiter := "/", prefix_ := "/" }

/-- Escape a regexp string (section 2.1.5). -/
def escapeRegexp (s : String) : String :=
  String.join (s.toList.map fun c =>
    if ".+*?^${}()[]|/\\".toList.contains c then "\\" ++ c.toString else c.toString)

/-- Escape a pattern string (section 2.1.4). -/
def escapePattern (s : String) : String :=
  String.join (s.toList.map fun c =>
    if "+*?:{}()\\".toList.contains c then "\\" ++ c.toString else c.toString)

def fullWildcard : String := ".*"

/-- Generate a segment wildcard regexp (section 2.1.2). -/
def segmentWildcard (o : Options) : String := "[^" ++ escapeRegexp o.delimiter ++ "]+?"

def Modifier.str : Modifier → String
  | .none => "" | .optional => "?" | .zeroOrMore => "*" | .oneOrMore => "+"

/-- The state of the pattern parser. -/
structure PP where
  toks : Array Tok
  index : Nat := 0
  parts : Array Part := #[]
  pending : String := ""
  nextName : Nat := 0

/-- An encoding callback: the canonical form of a fixed text, or a TypeError. -/
abbrev Encode := String → Except String String

abbrev PM := StateT PP (Except String)

def tryConsume (t : TokType) : PM (Option Tok) := do
  let s ← get
  let tok := s.toks.getD s.index default
  if tok.type == t then
    set { s with index := s.index + 1 }
    pure (some tok)
  else pure none

def tryConsumeModifier : PM (Option Tok) := do
  match ← tryConsume .otherModifier with
  | some t => pure (some t)
  | none => tryConsume .asterisk

def tryConsumeRegexpOrWildcard (nameTok : Option Tok) : PM (Option Tok) := do
  match ← tryConsume .regexp with
  | some t => pure (some t)
  | none => if nameTok.isNone then tryConsume .asterisk else pure none

def consumeRequired (t : TokType) : PM Tok := do
  match ← tryConsume t with
  | some tok => pure tok
  | none => throw "URLPattern: the pattern is not valid"

/-- Consume text: the values of the char and escaped-char tokens from the index on (a loop,
one token a turn). -/
def consumeTextGo (toks : Array Tok) : Nat → Nat → String → Nat × String
  | 0, i, acc => (i, acc)
  | fuel + 1, i, acc =>
    let t := toks.getD i default
    if i < toks.size && (t.type == .char || t.type == .escapedChar) then consumeTextGo toks fuel (i + 1) (acc ++ t.value)
    else (i, acc)

def consumeText : PM String := do
  let s ← get
  let (i, out) := consumeTextGo s.toks s.toks.size s.index ""
  set { s with index := i }
  pure out

def maybeAddPending (enc : Encode) : PM Unit := do
  let s ← get
  if s.pending.isEmpty then return
  let v ← liftM (m := Except String) (enc s.pending)
  set { s with pending := "", parts := s.parts.push { type := .fixedText, value := v, modifier := .none } }

/-- Add a part (section 2.1.2). -/
def addPart (enc : Encode) (o : Options) (prefix_ : String) (nameTok regexTok : Option Tok)
    (suffix : String) (modTok : Option Tok) : PM Unit := do
  let modifier : Modifier := match modTok with
    | some t => if t.value == "?" then .optional else if t.value == "*" then .zeroOrMore
        else if t.value == "+" then .oneOrMore else .none
    | none => .none
  if nameTok.isNone && regexTok.isNone && modifier == .none then
    modify fun s => { s with pending := s.pending ++ prefix_ }
    return
  maybeAddPending enc
  if nameTok.isNone && regexTok.isNone then
    if prefix_.isEmpty then return
    let v ← liftM (m := Except String) (enc prefix_)
    modify fun s => { s with parts := s.parts.push { type := .fixedText, value := v, modifier } }
    return
  let seg := segmentWildcard o
  let regexValue := match regexTok with
    | none => seg
    | some t => if t.type == .asterisk then fullWildcard else t.value
  let (type, regexValue) : PartType × String :=
    if regexValue == seg then (.segmentWildcard, "")
    else if regexValue == fullWildcard then (.fullWildcard, "")
    else (.regexp, regexValue)
  let s ← get
  let (name, s) := match nameTok with
    | some t => (t.value, s)
    | none => if regexTok.isSome then (toString s.nextName, { s with nextName := s.nextName + 1 }) else ("", s)
  if s.parts.any (·.name == name) then throw s!"URLPattern: the name '{name}' is used twice"
  let p ← liftM (m := Except String) (enc prefix_)
  let sf ← liftM (m := Except String) (enc suffix)
  set { s with parts := s.parts.push { type, value := regexValue, modifier, name, prefix_ := p, suffix := sf } }

/-- One turn of the loop of "parse a pattern string" (section 2.1.2); `true` when the end
token was consumed. -/
def parseStep (enc : Encode) (o : Options) : PM Bool := do
  let charTok ← tryConsume .char
  let nameTok ← tryConsume .name
  let regexTok ← tryConsumeRegexpOrWildcard nameTok
  if nameTok.isSome || regexTok.isSome then
    let mut prefix_ := match charTok with | some t => t.value | none => ""
    if !prefix_.isEmpty && prefix_ != o.prefix_ then
      modify fun s => { s with pending := s.pending ++ prefix_ }
      prefix_ := ""
    maybeAddPending enc
    let modTok ← tryConsumeModifier
    addPart enc o prefix_ nameTok regexTok "" modTok
    return false
  let fixedTok ← match charTok with
    | some t => pure (some t)
    | none => tryConsume .escapedChar
  if let some t := fixedTok then
    modify fun s => { s with pending := s.pending ++ t.value }
    return false
  if (← tryConsume .open_).isSome then
    let prefix_ ← consumeText
    let nameTok ← tryConsume .name
    let regexTok ← tryConsumeRegexpOrWildcard nameTok
    let suffix ← consumeText
    let _ ← consumeRequired .close
    let modTok ← tryConsumeModifier
    addPart enc o prefix_ nameTok regexTok suffix modTok
    return false
  maybeAddPending enc
  let _ ← consumeRequired .end_
  return true

/-- Parse a pattern string: turns until the tokens are used (each turn consumes a token, so
`fuel`, the token count plus two, is enough). The loop is a tail call. -/
def parseLoop (enc : Encode) (o : Options) : Nat → PP → Except String PP
  | 0, _ => .error "URLPattern: the pattern is too long"
  | fuel + 1, s =>
    if s.index ≥ s.toks.size then .ok s else
    match (parseStep enc o).run s with
    | .error e => .error e
    | .ok (done, s') => if done then .ok s' else parseLoop enc o fuel s'

def parsePattern (input : String) (o : Options) (enc : Encode) : Except String (Array Part) := do
  let cs := input.toList.toArray
  let some toks := tokenize cs true | throw "URLPattern: the pattern is not valid"
  let st ← parseLoop enc o (toks.size + 2) { toks }
  pure st.parts

/-! ## Regular expression and pattern string of a part list (sections 2.1.3, 2.1.4) -/

/-- Generate a regular expression and name list. -/
def regexOf (parts : Array Part) (o : Options) : String × Array String := Id.run do
  let mut r := "^"
  let mut names : Array String := #[]
  for p in parts do
    if p.type == .fixedText then
      if p.modifier == .none then r := r ++ escapeRegexp p.value
      else r := r ++ "(?:" ++ escapeRegexp p.value ++ ")" ++ p.modifier.str
      continue
    names := names.push p.name
    let v := match p.type with
      | .segmentWildcard => segmentWildcard o
      | .fullWildcard => fullWildcard
      | _ => p.value
    if p.prefix_.isEmpty && p.suffix.isEmpty then
      if p.modifier == .none || p.modifier == .optional then r := r ++ "(" ++ v ++ ")" ++ p.modifier.str
      else r := r ++ "((?:" ++ v ++ ")" ++ p.modifier.str ++ ")"
      continue
    if p.modifier == .none || p.modifier == .optional then
      r := r ++ "(?:" ++ escapeRegexp p.prefix_ ++ "(" ++ v ++ ")" ++ escapeRegexp p.suffix ++ ")" ++ p.modifier.str
      continue
    r := r ++ "(?:" ++ escapeRegexp p.prefix_ ++ "((?:" ++ v ++ ")(?:" ++ escapeRegexp p.suffix ++
      escapeRegexp p.prefix_ ++ "(?:" ++ v ++ "))*)" ++ escapeRegexp p.suffix ++ ")"
    if p.modifier == .zeroOrMore then r := r ++ "?"
  return (r ++ "$", names)

def firstChar? (s : String) : Option Char := s.toList.head?
def lastChar? (s : String) : Option Char := s.toList.getLast?

/-- Generate a pattern string: the canonical text of a part list. -/
def patternOf (parts : Array Part) (o : Options) : String := Id.run do
  let mut r := ""
  for i in [0:parts.size] do
    let p := parts[i]!
    let prev : Option Part := if i > 0 then parts[i - 1]? else none
    let next : Option Part := parts[i + 1]?
    if p.type == .fixedText then
      if p.modifier == .none then r := r ++ escapePattern p.value
      else r := r ++ "{" ++ escapePattern p.value ++ "}" ++ p.modifier.str
      continue
    let customName := match firstChar? p.name with | some c => !c.isDigit | none => true
    let mut grouping := !p.suffix.isEmpty || (!p.prefix_.isEmpty && p.prefix_ != o.prefix_)
    if !grouping && customName && p.type == .segmentWildcard && p.modifier == .none then
      if let some nx := next then
        if nx.prefix_.isEmpty && nx.suffix.isEmpty then
          if nx.type == .fixedText then
            grouping := match firstChar? nx.value with | some c => validNameChar c false | none => false
          else
            grouping := match firstChar? nx.name with | some c => c.isDigit | none => false
    if !grouping && p.prefix_.isEmpty then
      if let some pv := prev then
        if pv.type == .fixedText && !o.prefix_.isEmpty && (lastChar? pv.value).map Char.toString == some o.prefix_ then
          grouping := true
    if grouping then r := r ++ "{"
    r := r ++ escapePattern p.prefix_
    if customName then r := r ++ ":" ++ p.name
    if p.type == .regexp then r := r ++ "(" ++ p.value ++ ")"
    else if p.type == .segmentWildcard && !customName then r := r ++ "(" ++ segmentWildcard o ++ ")"
    else if p.type == .fullWildcard then
      let star := !customName && (match prev with
        | none => true
        | some pv => pv.type == .fixedText || pv.modifier != .none) || (!customName && (grouping || !p.prefix_.isEmpty))
      if star then r := r ++ "*" else r := r ++ "(" ++ fullWildcard ++ ")"
    if p.type == .segmentWildcard && customName && !p.suffix.isEmpty then
      if let some c := firstChar? p.suffix then
        if validNameChar c false then r := r ++ "\\"
    r := r ++ escapePattern p.suffix
    if grouping then r := r ++ "}"
    r := r ++ p.modifier.str
  return r

/-! ## Components (section 1.3) -/

/-- A compiled component: its pattern string, regular expression, group names. -/
structure Component where
  pattern : String
  regex : L4Factoidal.JS.Re.Compiled
  names : Array String
  hasRegexpGroups : Bool := false
  deriving Inhabited

/-- The escapes of a regular expression text are ones the `u` and `v` flags allow: after a
`\`, a letter must be one of the class, control, hexadecimal, Unicode, property or
back-reference escapes (§22.2.1: an identity escape is a syntax character or `/` only). -/
def regexEscapesOk (s : String) : Bool := Id.run do
  let mut escaped := false
  for c in s.toList do
    if escaped then
      if c.isAlpha && !"dDwWsSbBfnrtvcxupPk".toList.contains c then return false
      escaped := false
    else if c == '\\' then escaped := true
  return true

/-- Compile a component. -/
def compileComponent (input : String) (enc : Encode) (o : Options) : Except String Component := do
  let parts ← parsePattern input o enc
  if parts.any (fun p => p.type == .regexp && !regexEscapesOk p.value) then
    throw "URLPattern: the pattern's regular expression has an escape that is not valid"
  let (src, names) := regexOf parts o
  match L4Factoidal.JS.Re.compile src (if o.ignoreCase then "ui" else "u") with
  | .error e => throw s!"URLPattern: the pattern's regular expression is not valid ({e})"
  | .ok regex =>
    pure { pattern := patternOf parts o, regex, names, hasRegexpGroups := parts.any (·.type == .regexp) }

/-- Run a component's regular expression on an input: the groups by name (`none`: the group
did not take part), or `none` when the input does not match. -/
def Component.exec (c : Component) (input : String) : Option (Array (String × Option String)) :=
  let cs := input.toList.toArray
  match L4Factoidal.JS.Re.exec c.regex cs 0 with
  | none => none
  | some caps =>
    some (c.names.zipIdx.map fun (name, i) =>
      (name, (caps.getD (i + 1) none).map fun (a, b) => strOf cs a b))

def specialSchemes : List String := ["ftp", "file", "http", "https", "ws", "wss"]

def Component.matchesSpecialScheme (c : Component) : Bool :=
  specialSchemes.any fun s => (c.exec s).isSome

/-! ## Canonicalization (section 3, "Canonicalization") -/

/-- The dummy URL of the encoding callbacks. -/
def dummyUrl : Url := (basicParse "https://dummy.invalid/").url

def canonProtocol : Encode := fun v =>
  if v.isEmpty then pure v else
  match basicParse (v ++ "://dummy.invalid/") with
  | .ok u => pure u.scheme
  | .failure _ => throw s!"URLPattern: '{v}' is not a valid protocol"

def canonUsername : Encode := fun v =>
  if v.isEmpty then pure v else pure (utf8PercentEncodeString .userinfo v)

def canonPassword : Encode := canonUsername

def canonHostname : Encode := fun v =>
  if v.isEmpty then pure v else
  match basicParse v none (some dummyUrl) (some .hostname) with
  | .ok u => pure ((u.host.map Host.serialize).getD "")
  | .failure _ => throw s!"URLPattern: '{v}' is not a valid hostname"

def canonIPv6Hostname : Encode := fun v =>
  let ok (c : Char) : Bool :=
    c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F') || c == '[' || c == ']' || c == ':'
  if v.toList.all ok then pure (String.ofList (v.toList.map Char.toLower))
  else throw s!"URLPattern: '{v}' is not a valid IPv6 hostname"

/-- Canonicalize a port; `protocol`, when given, decides the default port. -/
def canonPort (protocol : Option String) : Encode := fun v =>
  if v.isEmpty then pure v else
  -- a URL record with no scheme, so that a port is kept unless `protocol` makes it the default
  let d : Url := match protocol with | some p => { scheme := p } | none => {}
  match basicParse v none (some d) (some .port) with
  | .ok u => pure ((u.port.map toString).getD "")
  | .failure _ => throw s!"URLPattern: '{v}' is not a valid port"

def canonPathname : Encode := fun v =>
  if v.isEmpty then pure v else
  let leading := v.startsWith "/"
  let modified := if leading then v else "/-" ++ v
  let u := (basicParse modified none (some { dummyUrl with path := .segments #[] }) (some .pathStart)).url
  let r := u.serializePath
  pure (if leading then r else String.ofList (r.toList.drop 2))

def canonOpaquePathname : Encode := fun v =>
  if v.isEmpty then pure v else
  pure (basicParse v none (some { dummyUrl with path := .opaque "" }) (some .opaquePath)).url.serializePath

def canonSearch : Encode := fun v =>
  if v.isEmpty then pure v else
  pure (((basicParse v none (some { dummyUrl with query := some "" }) (some .query)).url.query).getD "")

def canonHash : Encode := fun v =>
  if v.isEmpty then pure v else
  pure (((basicParse v none (some { dummyUrl with fragment := some "" }) (some .fragment)).url.fragment).getD "")

/-! ## URLPatternInit (section 1.4, "process a URLPatternInit") -/

/-- A URLPatternInit: each member present or not. -/
structure Init where
  protocol : Option String := none
  username : Option String := none
  password : Option String := none
  hostname : Option String := none
  port : Option String := none
  pathname : Option String := none
  search : Option String := none
  hash : Option String := none
  baseURL : Option String := none
  deriving DecidableEq, Repr, Inhabited

/-- Is an absolute pathname. `pattern`: the type is "pattern". -/
def isAbsolutePathname (s : String) (pattern : Bool) : Bool :=
  match s.toList with
  | [] => false
  | '/' :: _ => true
  | c :: d :: _ => pattern && ((c == '\\' && d == '/') || (c == '{' && d == '/'))
  | _ => false

def dropTrailing (s : String) (c : Char) : String :=
  if s.toList.getLast? == some c then String.ofList s.toList.dropLast else s

def dropLeading (s : String) (c : Char) : String :=
  if s.toList.head? == some c then String.ofList (s.toList.drop 1) else s

/-- Process a URLPatternInit. `pattern`: the type is "pattern" (the constructor); else "url"
(an input of `test` and `exec`), where each value is canonicalized and `start` gives the
empty strings the result begins with. -/
def processInit (init : Init) (pattern : Bool) (start : Init := {}) : Except String Init := do
  let mut r := start
  let baseStr (s : String) : String := if pattern then escapePattern s else s
  let mut base : Option Url := none
  if let some b := init.baseURL then
    match basicParse b with
    | .failure _ => throw s!"URLPattern: the base URL '{b}' is not valid"
    | .ok u =>
      base := some u
      if init.protocol.isNone then r := { r with protocol := some (baseStr u.scheme) }
      if !pattern && init.protocol.isNone && init.hostname.isNone && init.port.isNone && init.username.isNone then
        r := { r with username := some (baseStr u.username) }
      if !pattern && init.protocol.isNone && init.hostname.isNone && init.port.isNone && init.username.isNone &&
          init.password.isNone then
        r := { r with password := some (baseStr u.password) }
      if init.protocol.isNone && init.hostname.isNone then
        r := { r with hostname := some (baseStr ((u.host.map Host.serialize).getD "")) }
      if init.protocol.isNone && init.hostname.isNone && init.port.isNone then
        r := { r with port := some ((u.port.map toString).getD "") }
      if init.protocol.isNone && init.hostname.isNone && init.port.isNone && init.pathname.isNone then
        r := { r with pathname := some (baseStr u.serializePath) }
      if init.protocol.isNone && init.hostname.isNone && init.port.isNone && init.pathname.isNone &&
          init.search.isNone then
        r := { r with search := some (baseStr (u.query.getD "")) }
      if init.protocol.isNone && init.hostname.isNone && init.port.isNone && init.pathname.isNone &&
          init.search.isNone && init.hash.isNone then
        r := { r with hash := some (baseStr (u.fragment.getD "")) }
  if let some v := init.protocol then
    let s := dropTrailing v ':'
    r := { r with protocol := some (← if pattern then pure s else canonProtocol s) }
  if let some v := init.username then
    r := { r with username := some (← if pattern then pure v else canonUsername v) }
  if let some v := init.password then
    r := { r with password := some (← if pattern then pure v else canonPassword v) }
  if let some v := init.hostname then
    r := { r with hostname := some (← if pattern then pure v else canonHostname v) }
  let proto := r.protocol.getD ""
  if let some v := init.port then
    r := { r with port := some (← if pattern then pure v else canonPort (some proto) v) }
  if let some v := init.pathname then
    let mut p := v
    if let some u := base then
      if !u.hasOpaquePath && !isAbsolutePathname p pattern then
        let bp := baseStr u.serializePath
        match (bp.toList.zipIdx.filter (·.1 == '/')).getLast? with
        | some (_, i) => p := String.ofList (bp.toList.take (i + 1)) ++ p
        | none => pure ()
    let p' ← if pattern then pure p
      else if specialSchemes.contains proto || proto.isEmpty then canonPathname p
      else canonOpaquePathname p
    r := { r with pathname := some p' }
  if let some v := init.search then
    let s := dropLeading v '?'
    r := { r with search := some (← if pattern then pure s else canonSearch s) }
  if let some v := init.hash then
    let s := dropLeading v '#'
    r := { r with hash := some (← if pattern then pure s else canonHash s) }
  pure r

/-! ## The constructor string parser (section 2.2) -/

inductive CState where
  | init | protocol | authority | username | password | hostname | port | pathname | search | hash | done
  deriving DecidableEq, Repr, Inhabited

structure CP where
  cs : Array Char
  toks : Array Tok
  result : Init := {}
  componentStart : Nat := 0
  tokenIndex : Nat := 0
  tokenIncrement : Nat := 1
  groupDepth : Nat := 0
  ipv6Depth : Nat := 0
  special : Bool := false
  state : CState := .init

namespace CP

def safeTok (p : CP) (i : Nat) : Tok :=
  if i < p.toks.size then p.toks[i]! else p.toks.getD (p.toks.size - 1) default

def nonSpecial (p : CP) (i : Nat) (v : String) : Bool :=
  let t := p.safeTok i
  t.value == v && (t.type == .char || t.type == .escapedChar || t.type == .invalidChar)

def componentString (p : CP) : String :=
  strOf p.cs (p.safeTok p.componentStart).index (p.safeTok p.tokenIndex).index

def isSearchPrefix (p : CP) : Bool :=
  if p.nonSpecial p.tokenIndex "?" then true
  else if (p.safeTok p.tokenIndex).value != "?" then false
  else if p.tokenIndex == 0 then true
  else
    let prev := p.safeTok (p.tokenIndex - 1)
    !(prev.type == .name || prev.type == .regexp || prev.type == .close || prev.type == .asterisk)

def setComponent (r : Init) (st : CState) (v : String) : Init :=
  match st with
  | .protocol => { r with protocol := some v }
  | .username => { r with username := some v }
  | .password => { r with password := some v }
  | .hostname => { r with hostname := some v }
  | .port => { r with port := some v }
  | .pathname => { r with pathname := some v }
  | .search => { r with search := some v }
  | .hash => { r with hash := some v }
  | _ => r

/-- Change state: the component just read is stored, and the components the new state
skips over get their implied values. -/
def changeState (p : CP) (new : CState) (skip : Nat) : CP :=
  let r := if p.state != .init && p.state != .authority && p.state != .done
    then setComponent p.result p.state p.componentString else p.result
  let r := if p.state != .init && new != .done then
      let before := [CState.protocol, .authority, .username, .password]
      let r := if before.contains p.state && [CState.port, .pathname, .search, .hash].contains new && r.hostname.isNone
        then { r with hostname := some "" } else r
      let r := if (before ++ [CState.hostname, CState.port]).contains p.state && [CState.search, .hash].contains new && r.pathname.isNone
        then { r with pathname := some (if p.special then "/" else "") } else r
      if (before ++ [CState.hostname, CState.port, CState.pathname]).contains p.state && new == .hash && r.search.isNone
        then { r with search := some "" } else r
    else r
  { p with result := r, state := new, tokenIndex := p.tokenIndex + skip,
           componentStart := p.tokenIndex + skip, tokenIncrement := 0 }

def rewind (p : CP) : CP := { p with tokenIndex := p.componentStart, tokenIncrement := 0 }

def rewindAndSet (p : CP) (st : CState) : CP := { p.rewind with state := st }

end CP

/-- One turn of the loop of "parse a constructor string" (section 2.2); `true` when the
state is `done`. -/
def constructorStep (p0 : CP) : Except String (CP × Bool) := do
  let p := { p0 with tokenIncrement := 1 }
  let step (q : CP) : CP := { q with tokenIndex := q.tokenIndex + q.tokenIncrement }
  if (p.safeTok p.tokenIndex).type == .end_ then
    if p.state == .init then
      let q := p.rewind
      let q := if q.nonSpecial q.tokenIndex "#" then q.changeState .hash 1
        else if q.isSearchPrefix then q.changeState .search 1
        else q.changeState .pathname 0
      return (step q, false)
    if p.state == .authority then return (step (p.rewindAndSet .hostname), false)
    return (p.changeState .done 0, true)
  if (p.safeTok p.tokenIndex).type == .open_ then
    return (step { p with groupDepth := p.groupDepth + 1 }, false)
  if p.groupDepth > 0 then
    if (p.safeTok p.tokenIndex).type == .close then
      return (step { p with groupDepth := p.groupDepth - 1 }, false)
    else return (step p, false)
  let isP (v : String) : Bool := p.nonSpecial p.tokenIndex v
  let q ← match p.state with
    | .init => pure (if isP ":" then p.rewindAndSet .protocol else p)
    | .protocol =>
      if isP ":" then do
        -- compute the "protocol matches a special scheme" flag
        let special ← match compileComponent p.componentString canonProtocol {} with
          | .ok c => pure c.matchesSpecialScheme
          | .error e => throw e
        let p := { p with special }
        if p.nonSpecial (p.tokenIndex + 1) "/" && p.nonSpecial (p.tokenIndex + 2) "/" then
          pure (p.changeState .authority 3)
        else if special then pure (p.changeState .authority 1)
        else pure (p.changeState .pathname 1)
      else pure p
    | .authority =>
      pure (if isP "@" then p.rewindAndSet .username
        else if isP "/" || p.isSearchPrefix || isP "#" then p.rewindAndSet .hostname else p)
    | .username =>
      pure (if isP ":" then p.changeState .password 1 else if isP "@" then p.changeState .hostname 1 else p)
    | .password => pure (if isP "@" then p.changeState .hostname 1 else p)
    | .hostname =>
      pure (if isP "[" then { p with ipv6Depth := p.ipv6Depth + 1 }
        else if isP "]" then { p with ipv6Depth := p.ipv6Depth - 1 }
        else if isP ":" && p.ipv6Depth == 0 then p.changeState .port 1
        else if isP "/" then p.changeState .pathname 0
        else if p.isSearchPrefix then p.changeState .search 1
        else if isP "#" then p.changeState .hash 1 else p)
    | .port =>
      pure (if isP "/" then p.changeState .pathname 0
        else if p.isSearchPrefix then p.changeState .search 1
        else if isP "#" then p.changeState .hash 1 else p)
    | .pathname =>
      pure (if p.isSearchPrefix then p.changeState .search 1 else if isP "#" then p.changeState .hash 1 else p)
    | .search => pure (if isP "#" then p.changeState .hash 1 else p)
    | _ => pure p
  return (step q, false)

/-- Parse a constructor string: turns until the tokens are used or the state is `done`. Each
turn moves the token index forward or goes back at most once a component, so `fuel` (four
turns a token and a few more) is enough; running out is an invalid pattern. A tail call. -/
def constructorLoop : Nat → CP → Except String CP
  | 0, _ => .error "URLPattern: the pattern is not valid"
  | fuel + 1, p =>
    if p.tokenIndex ≥ p.toks.size then .ok p else
    match constructorStep p with
    | .error e => .error e
    | .ok (q, done) => if done then .ok q else constructorLoop fuel q

def parseConstructorString (input : String) : Except String Init := do
  let cs := input.toList.toArray
  let some toks := tokenize cs false | throw "URLPattern: the pattern is not valid"
  let p ← constructorLoop (4 * toks.size + 16) { cs, toks }
  let r := p.result
  pure (if r.hostname.isSome && r.port.isNone then { r with port := some "" } else r)

/-! ## URLPattern (section 1.2): create and match -/

/-- The input of the constructor, `test` and `exec`: a string or a URLPatternInit. -/
inductive Input where
  | str (s : String)
  | init (i : Init)
  deriving Repr, Inhabited

/-- A URL pattern: its eight components. -/
structure Pattern where
  protocol : Component
  username : Component
  password : Component
  hostname : Component
  port : Component
  pathname : Component
  search : Component
  hash : Component
  deriving Inhabited

def Pattern.hasRegexpGroups (p : Pattern) : Bool :=
  p.protocol.hasRegexpGroups || p.username.hasRegexpGroups || p.password.hasRegexpGroups ||
  p.hostname.hasRegexpGroups || p.port.hasRegexpGroups || p.pathname.hasRegexpGroups ||
  p.search.hasRegexpGroups || p.hash.hasRegexpGroups

/-- The hostname pattern is an IPv6 address. -/
def hostnameIsIPv6 (s : String) : Bool :=
  match s.toList with
  | '[' :: _ :: _ => true
  | '{' :: '[' :: _ => true
  | '\\' :: '[' :: _ => true
  | _ => false

def defaultPortOf (scheme : String) : Option String :=
  match scheme with
  | "ftp" => some "21" | "http" => some "80" | "https" => some "443" | "ws" => some "80" | "wss" => some "443"
  | _ => none

/-- Create a URL pattern (the constructor): `error` is the message of the TypeError. -/
def create (input : Input) (baseURL : Option String) (ignoreCase : Bool) : Except String Pattern := do
  let init ← match input with
    | .str s => do
      let i ← parseConstructorString s
      if baseURL.isNone && i.protocol.isNone then
        throw "URLPattern: a relative pattern needs a base URL"
      pure { i with baseURL := baseURL.orElse fun _ => i.baseURL }
    | .init i => do
      if baseURL.isSome then throw "URLPattern: a base URL can not be given with an object"
      pure i
  let p ← processInit init true
  let get (o : Option String) : String := o.getD "*"
  let protocolS := get p.protocol
  let portS := get p.port
  let portS := if specialSchemes.contains protocolS && defaultPortOf protocolS == some portS then "" else portS
  let protocol ← compileComponent protocolS canonProtocol {}
  let username ← compileComponent (get p.username) canonUsername {}
  let password ← compileComponent (get p.password) canonPassword {}
  let hostS := get p.hostname
  let hostname ← compileComponent hostS (if hostnameIsIPv6 hostS then canonIPv6Hostname else canonHostname) hostnameOptions
  let port ← compileComponent portS (canonPort none) {}
  let special := protocol.matchesSpecialScheme
  let pathname ← if special then compileComponent (get p.pathname) canonPathname { pathnameOptions with ignoreCase }
    else compileComponent (get p.pathname) canonOpaquePathname { ignoreCase }
  let search ← compileComponent (get p.search) canonSearch { ignoreCase }
  let hash ← compileComponent (get p.hash) canonHash { ignoreCase }
  pure { protocol, username, password, hostname, port, pathname, search, hash }

/-- The groups of one component of a match. -/
abbrev Groups := Array (String × Option String)

/-- The result of `exec`: each component's input and groups, in the order protocol, username,
password, hostname, port, pathname, search, hash. -/
structure Result where
  components : Array (String × Groups)
  deriving Inhabited

/-- Match (the steps of `test` and `exec`). `error`: a TypeError (an object input with a base
URL). `none`: no match. -/
def exec (pat : Pattern) (input : Input) (baseURL : Option String) : Except String (Option Result) := do
  let values : Option (Array String) ← match input with
    | .init i => do
      if baseURL.isSome then throw "URLPattern: a base URL can not be given with an object"
      let start : Init := { protocol := some "", username := some "", password := some "", hostname := some "",
                            port := some "", pathname := some "", search := some "", hash := some "" }
      match processInit i false start with
      | .error _ => pure none
      | .ok r => pure (some #[r.protocol.getD "", r.username.getD "", r.password.getD "", r.hostname.getD "",
          r.port.getD "", r.pathname.getD "", r.search.getD "", r.hash.getD ""])
    | .str s =>
      let base : Option (Option Url) := match baseURL with
        | none => some none
        | some b => match basicParse b with | .ok u => some (some u) | .failure _ => none
      match base with
      | none => pure none
      | some b =>
        match basicParse s b with
        | .failure _ => pure none
        | .ok u => pure (some #[u.scheme, u.username, u.password, (u.host.map Host.serialize).getD "",
            (u.port.map toString).getD "", u.serializePath, u.query.getD "", u.fragment.getD ""])
  let some vs := values | return none
  let comps := [pat.protocol, pat.username, pat.password, pat.hostname, pat.port, pat.pathname, pat.search, pat.hash]
  -- every component must match its value
  let results := comps.zipIdx.map fun (c, i) => let v := vs.getD i ""; (v, c.exec v)
  if results.any (·.2.isNone) then return none
  return some { components := (results.map fun (v, g) => (v, g.getD #[])).toArray }

end L4Factoidal.WHATWG.URLPattern
