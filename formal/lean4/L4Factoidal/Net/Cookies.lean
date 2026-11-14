/-
L4Factoidal.Net.Cookies — cookies as page scripts see them (`document.cookie`; HTTP State
Management Mechanism, RFC 6265bis: §5.1.1 dates, §5.1.3 domain matching, §5.1.4 paths,
§5.6 the Set-Cookie algorithm, §5.7 the storage model for a "non-HTTP" API, §5.8.3
retrieval). `web_api` ops 96 and 97 (`WasmVM.Hosts.WebApi`).

## Decisions

* For scripts only, tonight. The engine sends no `Cookie` field and reads no `Set-Cookie`
  field (`Net.PageFetch`: no credentials; `responseOf_no_set_cookie`). What a script sets
  with `document.cookie` it reads back with `document.cookie`; no server sees it. This keeps
  a page's own scripts working (consent, preferences) and changes nothing on the wire.
* In memory, for the session. Nothing is written to disk.
* A cookie is its host's. The host and the secure flag are the engine's (the session's page
  origin), never an argument. A `Domain` attribute must domain-match the host; one that names
  a parent domain is accepted and the cookie is still kept for the host alone: no public
  suffix list is held, so no cookie is shared between hosts (`set_keeps_host`,
  `visible_host`). This is narrower than the standard and is the safe side.
* A script cannot set or read an `HttpOnly` cookie (`set_no_httpOnly`, `visible_not_httpOnly`),
  and a `Secure` cookie is neither set by nor shown to a page that is not secure
  (`visible_secure`).
* The `__Secure-` and `__Host-` prefixes are enforced (§4.1.3).

Every loop is a core list combinator or a tail call on a shorter list.
-/

namespace L4Factoidal.Net.Cookies

/-- ASCII lower case. -/
def lower (s : String) : String :=
  s.map fun c => if 'A' ≤ c ∧ c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- Space or tab. -/
def isWsp (c : Char) : Bool := c == ' ' || c == '\t'

/-- Without leading and trailing spaces and tabs. -/
def trimWsp (cs : List Char) : List Char := ((cs.dropWhile isWsp).reverse.dropWhile isWsp).reverse

/-- A control character that makes a cookie string invalid (§5.6 step 1): U+0000 to U+0008,
U+000A to U+001F, U+007F. -/
def isCtl (c : Char) : Bool := (c.toNat ≤ 0x08) || (0x0A ≤ c.toNat && c.toNat ≤ 0x1F) || c.toNat == 0x7F

/-- One cookie of the jar. -/
structure Cookie where
  name : String
  value : String
  /-- The host it is for (lower case). -/
  host : String
  path : String
  secure : Bool := false
  httpOnly : Bool := false
  /-- Seconds since the epoch when it ends; `none` for a session cookie. -/
  expires : Option Nat := none
  /-- Its place in the order of creation. -/
  created : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- The cookies of the session. -/
structure Jar where
  cookies : List Cookie := []
  next : Nat := 0
  deriving Inhabited

/-- The document that asks: its host (lower case), its path, and whether it is secure. -/
structure Site where
  host : String
  path : String
  secure : Bool
  deriving DecidableEq, Repr, Inhabited

/-- Cookies kept for one host, and the largest name and value together (§5.6 step 6, §5.7). -/
def maxPerHost : Nat := 180
def maxNameValue : Nat := 4096
def maxAttribute : Nat := 1024

/-! ## Dates (§5.1.1) -/

/-- A delimiter of a cookie date. -/
def isDateDelimiter (c : Char) : Bool :=
  c.toNat == 0x09 || (0x20 ≤ c.toNat && c.toNat ≤ 0x2F) || (0x3B ≤ c.toNat && c.toNat ≤ 0x40) ||
    (0x5B ≤ c.toNat && c.toNat ≤ 0x60) || (0x7B ≤ c.toNat && c.toNat ≤ 0x7E)

/-- The tokens of a date: the runs between delimiters. `fuel`: one token a turn. -/
def dateTokensGo : List Char → List (List Char) → Nat → List (List Char)
  | _, acc, 0 => acc.reverse
  | cs, acc, fuel + 1 =>
    match cs.dropWhile isDateDelimiter with
    | [] => acc.reverse
    | rest => dateTokensGo (rest.dropWhile (!isDateDelimiter ·)) (rest.takeWhile (!isDateDelimiter ·) :: acc) fuel

/-- The leading digits of a token as a number, when there are between `lo` and `hi` of them. -/
def leadingDigits (t : List Char) (lo hi : Nat) : Option (Nat × List Char) :=
  let ds := t.takeWhile Char.isDigit
  if lo ≤ ds.length && ds.length ≤ hi then some ((String.ofList ds).toNat?.getD 0, t.dropWhile Char.isDigit) else none

/-- A time token `h:m:s` (one or two digits each). -/
def timeOf (t : List Char) : Option (Nat × Nat × Nat) :=
  match leadingDigits t 1 2 with
  | some (h, ':' :: r1) =>
    match leadingDigits r1 1 2 with
    | some (m, ':' :: r2) =>
      match leadingDigits r2 1 2 with
      | some (s, rest) => if rest.head?.any Char.isDigit then none else some (h, m, s)
      | none => none
    | _ => none
  | _ => none

/-- The month a token names by its first three letters (1 to 12). -/
def monthOf (t : List Char) : Option Nat :=
  let key := lower (String.ofList (t.take 3))
  let months := ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"]
  match months.findIdx? (· == key) with
  | some i => some (i + 1)
  | none => none

/-- Days from 1970-01-01 to a date of the proleptic Gregorian calendar, for a year from 1970. -/
def daysFromCivil (y m d : Nat) : Nat :=
  let y' := if m ≤ 2 then y - 1 else y
  let era := y' / 400
  let yoe := y' - era * 400
  let mp := if m > 2 then m - 3 else m + 9
  let doy := (153 * mp + 2) / 5 + d - 1
  let doe := yoe * 365 + yoe / 4 - yoe / 100 + doy
  era * 146097 + doe - 719468

/-- The date parts found so far. -/
structure DateParts where
  time : Option (Nat × Nat × Nat) := none
  day : Option Nat := none
  month : Option Nat := none
  year : Option Nat := none

/-- §5.1.1 step 2: a token is the time, else the day of the month, else the month, else the
year, each taken once. -/
def datePart (p : DateParts) (t : List Char) : DateParts :=
  match p.time, timeOf t with
  | none, some v => { p with time := some v }
  | _, _ =>
    match p.day, leadingDigits t 1 2 with
    | none, some (d, rest) => if rest.head?.any Char.isDigit then datePartRest p t else { p with day := some d }
    | _, _ => datePartRest p t
where
  datePartRest (p : DateParts) (t : List Char) : DateParts :=
    match p.month, monthOf t with
    | none, some m => { p with month := some m }
    | _, _ =>
      match p.year, leadingDigits t 2 4 with
      | none, some (y, rest) => if rest.head?.any Char.isDigit then p else { p with year := some y }
      | _, _ => p

/-- "Parse a cookie date" (§5.1.1): seconds since the epoch; `none` when it is not a date.
A date before 1970 is 0 (the cookie has ended). -/
def parseDate (s : String) : Option Nat :=
  let cs := s.toList
  let p := (dateTokensGo cs [] (cs.length + 1)).foldl datePart {}
  match p.time, p.day, p.month, p.year with
  | some (h, mi, sec), some d, some m, some y =>
    let y := if 70 ≤ y && y ≤ 99 then y + 1900 else if y ≤ 69 then y + 2000 else y
    if d < 1 || d > 31 || y < 1601 || h > 23 || mi > 59 || sec > 59 then none
    else if y < 1970 then some 0
    else some (daysFromCivil y m d * 86400 + h * 3600 + mi * 60 + sec)
  | _, _, _, _ => none

/-! ## Matching (§5.1.3, §5.1.4) -/

/-- An IPv4 address in dotted form, or an IPv6 address in brackets: never a domain suffix. -/
def isIpLiteral (h : String) : Bool :=
  h.startsWith "[" || (!h.isEmpty && h.toList.all fun c => c.isDigit || c == '.')

/-- §5.1.3 "domain-match": `host` is `domain`, or ends with `.domain` and is not an IP address. -/
def domainMatch (host domain : String) : Bool :=
  host == domain || (!domain.isEmpty && host.endsWith ("." ++ domain) && !isIpLiteral host)

/-- §5.1.4 "path-match". -/
def pathMatch (requestPath cookiePath : String) : Bool :=
  requestPath == cookiePath ||
    (requestPath.startsWith cookiePath &&
      (cookiePath.endsWith "/" || ((requestPath.drop cookiePath.length).toString.startsWith "/")))

/-- §5.1.4 "default-path" of a request path. -/
def defaultPath (path : String) : String :=
  if !path.startsWith "/" then "/" else
  let cs := path.toList
  let upTo := (cs.reverse.dropWhile (· != '/')).reverse
  -- `upTo` ends with the last slash; without it, or "/" when that slash is the first
  if upTo.length ≤ 1 then "/" else String.ofList (upTo.take (upTo.length - 1))

/-! ## Setting a cookie from a script (§5.6, §5.7) -/

/-- The attributes of a cookie string after its name and value. -/
structure Attributes where
  expires : Option Nat := none
  maxAge : Option Int := none
  domain : Option String := none
  path : Option String := none
  secure : Bool := false
  httpOnly : Bool := false

/-- One attribute (§5.6): its name and value, trimmed. -/
def readAttribute (a : Attributes) (text : String) : Attributes :=
  let cs := text.toList
  let name := lower (String.ofList (trimWsp (cs.takeWhile (· != '='))))
  let value := String.ofList (trimWsp ((cs.dropWhile (· != '=')).drop 1))
  if value.length > maxAttribute then a else
  match name with
  | "expires" => match parseDate value with
    | some t => { a with expires := some t }
    | none => a
  | "max-age" =>
    let ds := value.toList
    let digits := if ds.head? == some '-' then ds.drop 1 else ds
    if digits.isEmpty || !digits.all Char.isDigit then a
    else { a with maxAge := some (if ds.head? == some '-' then 0 else Int.ofNat ((String.ofList digits).toNat?.getD 0)) }
  | "domain" =>
    let d := lower (if value.startsWith "." then (value.drop 1).toString else value)
    { a with domain := some d }
  | "path" => { a with path := if value.isEmpty || !value.startsWith "/" then none else some value }
  | "secure" => { a with secure := true }
  | "httponly" => { a with httpOnly := true }
  | _ => a

/-- The name, the value and the attribute texts of a cookie string (§5.6 steps 1 to 6);
`none` when the string is refused: a control character, a name and value over the size, or
neither a name nor a value. -/
def nameValue (text : String) : Option (String × String × List String) :=
  if text.toList.any isCtl then none else
  let pair := ((text.splitOn ";").headD "").toList
  let name := if pair.contains '=' then trimWsp (pair.takeWhile (· != '=')) else []
  let value := if pair.contains '=' then trimWsp ((pair.dropWhile (· != '=')).drop 1) else trimWsp pair
  if name.length + value.length > maxNameValue || (name.isEmpty && value.isEmpty) then none
  else some (String.ofList name, String.ofList value, (text.splitOn ";").drop 1)

/-- The steps of the storage model (§5.7) that refuse a script's cookie, and the cookie
kept: for the page's host, never `HttpOnly`. -/
def admit (site : Site) (now : Nat) (name value : String) (a : Attributes) : Option Cookie :=
  -- a script can not make an HttpOnly cookie; a Secure cookie needs a secure page
  if a.httpOnly || (a.secure && !site.secure) then none
  -- the Domain attribute must name this host or a parent of it
  else if (a.domain.any fun d => !d.isEmpty && !domainMatch site.host d) then none
  -- the prefixes (§4.1.3)
  else if (lower name).startsWith "__secure-" && !a.secure then none
  else if (lower name).startsWith "__host-" && !(a.secure && a.domain.all (·.isEmpty) && a.path == some "/") then none
  else some { name, value, host := site.host, path := a.path.getD (defaultPath site.path), secure := a.secure,
              httpOnly := false,
              expires := match a.maxAge with
                | some d => some (if d ≤ 0 then 0 else now + d.toNat)
                | none => a.expires }

/-- The cookie that a script's string makes for `site` at time `now`; `none` when the string
is refused (`nameValue`, `admit`). -/
def parseForScript (site : Site) (now : Nat) (text : String) : Option Cookie :=
  match nameValue text with
  | none => none
  | some (name, value, attrs) => admit site now name value (attrs.foldl readAttribute {})

/-- A cookie has ended at `now`. -/
def expired (c : Cookie) (now : Nat) : Bool :=
  match c.expires with
  | some t => t ≤ now
  | none => false

/-- The same cookie for replacement: name, host and path (§5.7 step 23). -/
def sameKey (a b : Cookie) : Bool := a.name == b.name && a.host == b.host && a.path == b.path

/-- `document.cookie = text` on a page of `site` at `now`: the jar after it. A refused string
changes nothing; a cookie that has ended removes the one it names. -/
def setFromScript (jar : Jar) (site : Site) (now : Nat) (text : String) : Jar :=
  match parseForScript site now text with
  | none => jar
  | some c =>
    -- a script does not replace an HttpOnly cookie (§5.7 step 23.2)
    if jar.cookies.any (fun o => sameKey o c && o.httpOnly) then jar else
    let old := jar.cookies.find? (sameKey · c)
    let rest := jar.cookies.filter fun o => !sameKey o c && !expired o now
    if expired c now then { jar with cookies := rest } else
    let c := { c with created := (old.map (·.created)).getD jar.next }
    let kept := if (rest.filter (·.host == c.host)).length ≥ maxPerHost then rest.drop 1 else rest
    { cookies := kept ++ [c], next := jar.next + 1 }

/-! ## Reading (§5.8.3) -/

/-- A cookie that a script of `site` reads at `now`. -/
def visible (site : Site) (now : Nat) (c : Cookie) : Bool :=
  c.host == site.host && pathMatch site.path c.path && (!c.secure || site.secure) && !c.httpOnly && !expired c now

/-- The cookies a script of `site` reads, in the order of §5.8.3: longer paths first, then
earlier creation. -/
def visibleCookies (jar : Jar) (site : Site) (now : Nat) : List Cookie :=
  (jar.cookies.filter (visible site now)).mergeSort fun a b =>
    a.path.length > b.path.length || (a.path.length == b.path.length && a.created ≤ b.created)

/-- `document.cookie`: `name=value` of each visible cookie, joined by `; ` (a cookie with no
name is its value alone). -/
def forScript (jar : Jar) (site : Site) (now : Nat) : String :=
  "; ".intercalate ((visibleCookies jar site now).map fun c => if c.name.isEmpty then c.value else c.name ++ "=" ++ c.value)

/-- The document a script's cookie operations are for, from what the engine holds of the page:
its origin (`scheme://host[:port]`; only `http` and `https` documents have cookies, HTML
§3.1.5 "cookie-averse"), whether it is secure, and the path the script's side gives (the
path is no boundary: RFC 6265bis §8.5). -/
def siteOf (origin : String) (secure : Bool) (path : String) : Option Site :=
  match origin.splitOn "://" with
  | [scheme, rest] =>
    if scheme != "http" && scheme != "https" then none else
    let host := if rest.startsWith "[" then String.ofList (rest.toList.takeWhile (· != ']')) ++ "]"
      else String.ofList (rest.toList.takeWhile (· != ':'))
    if host.isEmpty then none else some { host := lower host, path := if path.startsWith "/" then path else "/", secure }
  | _ => none

/-- One field of a `web_api` call as a string. -/
def strAt (fs : Array ByteArray) (i : Nat) : String :=
  (String.fromUTF8? (fs.getD i ByteArray.empty)).getD ""

/-- `web_api` ops 96 and 97 for the page of `origin`: 96 `document.cookie` (fields: the
document's path, the time in seconds), 97 `document.cookie = text` (path, time, text). A
document with no cookies (an opaque origin, another scheme) reads "" and sets nothing. -/
def op (jar : Jar) (origin : String) (secure : Bool) (code : Nat) (fs : Array ByteArray) : Jar × Except Int ByteArray :=
  match siteOf origin secure (strAt fs 0) with
  | none => (jar, .ok ByteArray.empty)
  | some site =>
    let now := (strAt fs 1).toNat?.getD 0
    match code with
    | 96 => (jar, .ok (forScript jar site now).toUTF8)
    | 97 => (setFromScript jar site now (strAt fs 2), .ok ByteArray.empty)
    | _ => (jar, .error (-2))

/-! ## Theorems -/

/-- Kind: privacy invariant (cookies are their host's, read side). Says: every cookie that a
script reads was stored for the host of its own page. Does not say: that the engine passes
the right host (`WebApi.run` takes it from the session's page origin). -/
theorem visible_host (jar : Jar) (site : Site) (now : Nat) (c : Cookie)
    (h : c ∈ visibleCookies jar site now) : c.host = site.host := by
  unfold visibleCookies at h
  have h' := (List.mem_filter.mp ((List.mem_mergeSort).mp h)).2
  unfold visible at h'
  simp only [Bool.and_eq_true, beq_iff_eq] at h'
  exact h'.1.1.1.1

/-- Kind: security invariant. Says: a script never reads an `HttpOnly` cookie. -/
theorem visible_not_httpOnly (jar : Jar) (site : Site) (now : Nat) (c : Cookie)
    (h : c ∈ visibleCookies jar site now) : c.httpOnly = false := by
  unfold visibleCookies at h
  have h' := (List.mem_filter.mp ((List.mem_mergeSort).mp h)).2
  unfold visible at h'
  simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h'
  exact h'.1.2

/-- Kind: security invariant. Says: a page that is not secure never reads a `Secure` cookie. -/
theorem visible_secure (jar : Jar) (site : Site) (now : Nat) (c : Cookie)
    (h : c ∈ visibleCookies jar site now) (hs : site.secure = false) : c.secure = false := by
  unfold visibleCookies at h
  have h' := (List.mem_filter.mp ((List.mem_mergeSort).mp h)).2
  unfold visible at h'
  simp only [Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, hs, Bool.false_eq_true, or_false] at h'
  exact h'.1.1.2

/-- Kind: privacy invariant (cookies are their host's, write side). Says: a cookie that the
storage model admits for a script is for the host of its page, is not `HttpOnly`, and is
`Secure` only on a secure page, whatever `Domain` its attributes name. -/
theorem admit_keeps_host (site : Site) (now : Nat) (name value : String) (a : Attributes) (c : Cookie)
    (h : admit site now name value a = some c) :
    c.host = site.host ∧ c.httpOnly = false ∧ (c.secure = true → site.secure = true) := by
  unfold admit at h
  split at h
  · simp at h
  · rename_i h1
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Option.some.injEq] at h
          rw [← h]
          refine ⟨rfl, rfl, ?_⟩
          intro hs
          cases hsite : site.secure <;> simp_all

/-- Kind: privacy invariant (cookies are their host's, write side). Says: a cookie that a
script's string makes is for the host of its page, is not `HttpOnly`, and is `Secure` only on
a secure page. -/
theorem parse_keeps_host (site : Site) (now : Nat) (text : String) (c : Cookie)
    (h : parseForScript site now text = some c) :
    c.host = site.host ∧ c.httpOnly = false ∧ (c.secure = true → site.secure = true) := by
  unfold parseForScript at h
  split at h
  · simp at h
  · exact admit_keeps_host _ _ _ _ _ _ h

/-- Kind: privacy invariant. Says: after `document.cookie = text`, every cookie in the jar
was there before or is for the host of the page that set it and is not `HttpOnly`: a script
never adds a cookie for another host. -/
theorem set_keeps_host (jar : Jar) (site : Site) (now : Nat) (text : String) (c : Cookie)
    (h : c ∈ (setFromScript jar site now text).cookies) :
    (∃ o ∈ jar.cookies, o.name = c.name ∧ o.value = c.value ∧ o.host = c.host ∧ o.httpOnly = c.httpOnly) ∨
      (c.host = site.host ∧ c.httpOnly = false) := by
  unfold setFromScript at h
  split at h
  · exact .inl ⟨c, h, rfl, rfl, rfl, rfl⟩
  · rename_i n hp
    have hn := parse_keeps_host site now text n hp
    have old : ∀ x, x ∈ jar.cookies.filter (fun o => !sameKey o n && !expired o now) → x ∈ jar.cookies :=
      fun x hx => (List.mem_filter.mp hx).1
    split at h
    · exact .inl ⟨c, h, rfl, rfl, rfl, rfl⟩
    · split at h
      · exact .inl ⟨c, old c h, rfl, rfl, rfl, rfl⟩
      · simp only at h
        rcases List.mem_append.mp h with hk | hk
        · have hin : c ∈ jar.cookies.filter (fun o => !sameKey o n && !expired o now) := by
            split at hk
            · exact List.mem_of_mem_drop hk
            · exact hk
          exact .inl ⟨c, old c hin, rfl, rfl, rfl, rfl⟩
        · simp only [List.mem_singleton] at hk
          rw [hk]
          exact .inr ⟨hn.1, hn.2.1⟩

/-! ## Checks (RFC 6265bis and the cases of WPT cookies/) -/

private def site : Site := { host := "www.example.com", path := "/dir/page.html", secure := true }
private def plain : Site := { site with secure := false }
private def set1 (j : Jar) (t : String) (s : Site := site) (now : Nat := 1000) : Jar := setFromScript j s now t
private def j1 : Jar := set1 (set1 {} "a=1") "b=2; Path=/"

#guard forScript j1 site 1000 == "a=1; b=2"
#guard forScript (set1 j1 "a=3") site 1000 == "a=3; b=2"
-- deletion: Max-Age=0, or an Expires in the past
#guard forScript (set1 j1 "a=; Max-Age=0") site 1000 == "b=2"
#guard forScript (set1 j1 "b=; Path=/; expires=Thu, 01 Jan 1970 00:00:00 GMT") site 1000 == "a=1"
#guard forScript (set1 j1 "c=9; Max-Age=10") site 1009 == "a=1; c=9; b=2"
#guard forScript (set1 j1 "c=9; Max-Age=10") site 1010 == "a=1; b=2"
-- the default path is the directory of the page; another path does not see the cookie
#guard forScript j1 { site with path := "/other" } 1000 == "b=2"
#guard forScript j1 { site with path := "/dir/sub/x" } 1000 == "a=1; b=2"
-- another host sees nothing; a Domain for another site is refused; a parent domain keeps the host
#guard forScript j1 { site with host := "evil.example" } 1000 == ""
#guard forScript (set1 {} "x=1; Domain=evil.example") site 1000 == ""
#guard forScript (set1 {} "x=1; Domain=.example.com") site 1000 == "x=1"
#guard forScript (set1 {} "x=1; Domain=example.com") { site with host := "other.example.com" } 1000 == ""
-- HttpOnly is not a script's to set; Secure needs a secure page and is not shown to a plain one
#guard forScript (set1 {} "x=1; HttpOnly") site 1000 == ""
#guard forScript (set1 {} "x=1; Secure" plain) plain 1000 == ""
#guard forScript (set1 {} "x=1; Secure") plain 1000 == "" && forScript (set1 {} "x=1; Secure") site 1000 == "x=1"
-- prefixes
#guard forScript (set1 {} "__Secure-x=1") site 1000 == "" && forScript (set1 {} "__Secure-x=1; Secure") site 1000 == "__Secure-x=1"
#guard forScript (set1 {} "__Host-x=1; Secure; Path=/") site 1000 == "__Host-x=1"
#guard forScript (set1 {} "__Host-x=1; Secure; Path=/; Domain=www.example.com") site 1000 == ""
#guard forScript (set1 {} "__HoSt-x=1; Secure") site 1000 == ""
-- names and values
#guard forScript (set1 {} "  a  =  b  ") site 1000 == "a=b" && forScript (set1 {} "novalue") site 1000 == "novalue"
#guard forScript (set1 {} "=") site 1000 == "" && forScript (set1 {} "a=b\x01c") site 1000 == ""
#guard forScript (set1 {} "a=b=c; x") site 1000 == "a=b=c"
-- dates
#guard parseDate "Thu, 01 Jan 1970 00:00:00 GMT" == some 0
#guard parseDate "Wed, 09 Jun 2021 10:18:14 GMT" == some 1623233894
#guard parseDate "Sun, 06 Nov 1994 08:49:37 GMT" == some 784111777
#guard parseDate "01-Jan-70 00:00:10 GMT" == some 10 && parseDate "not a date" == none
#guard parseDate "Fri, 31 Dec 9999 23:59:59 GMT" == some 253402300799
#guard domainMatch "www.example.com" "example.com" && !domainMatch "badexample.com" "example.com" && !domainMatch "1.2.3.4" "3.4"
#guard pathMatch "/a/b" "/a" && pathMatch "/a/b" "/a/" && !pathMatch "/ab" "/a" && pathMatch "/a" "/a"
#guard siteOf "https://WWW.Example.com:8443" true "/a" == some { host := "www.example.com", path := "/a", secure := true }
#guard siteOf "http://[::1]:8000" false "" == some { host := "[::1]", path := "/", secure := false }
#guard siteOf "null" false "/" == none && siteOf "file://" false "/" == none
#guard defaultPath "/dir/page.html" == "/dir" && defaultPath "/page" == "/" && defaultPath "" == "/" && defaultPath "/a/b/" == "/a/b"

end L4Factoidal.Net.Cookies
