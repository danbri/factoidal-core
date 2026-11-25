import WebHistory
import L4Factoidal.Syntax.IriResolve

/-! Where a link goes: the link traversal rules of the browser, with their theorems
(owner, 2026-11-08: "need link traversal rules as theorem?").

`route` takes the `href` of a link, the address of the page it is on and the site the
browser loads pages from, and gives the FINAL action. The hosts (the Hub worker and the
native browser) do what it says and test no URL themselves. Before this, `WebShell.link`
answered `foafnaut:graph` as a page and the Hub made a second decision of its own ("not
on this site, so hand it to the host browser"), and the click bounced back (issue 1268).

The theorems at the end hold for every href, page address and site:
* `foafnaut_never_system`, `foafnaut_scheme_never_system`: a `foafnaut:` link is never
  handed to the system;
* `system_only_pressed`, `no_system_unpressed`: a link hands an address to the system (the
  host's default browser, or the mail, phone or messages app) only when the tab shows the
  browser's own Outside page for that address and the person pressed its button; no host
  and no scheme goes there by itself (owner, 2026-11-16: no host list sends links out);
* `native_web_navigates`: the native browser, which loads every web site itself, opens
  every web address in the tab;
* `settings_only_from_settings`: a link on a page other than Settings can not choose the
  search engine (a page could otherwise send the words typed later to a site of its own);
* `builtin_resolves`, `graph_resolves`: every built-in page name routes to its page;
* `same_site_navigates`: an http(s) address of the site's own origin navigates in the tab;
* `relative_resolves_against_base`: a relative href is the page address and the href,
  resolved by RFC 3986 (`Syntax.resolveIri`), and nothing else;
* `history_roundtrip`, `graph_history_roundtrip`: back after a built-in page link gives
  the page before it, and forward gives the built-in page again, with the session history
  as the hosts keep it (`WebHistory`).

How an href becomes an address follows the URL Standard where browsers agree: spaces
and controls at the ends go, tabs and line breaks inside go, a backslash is a slash in a
web address, scheme and host are lower case, a default port goes, and characters outside
the URL code points are percent-encoded (`^` in a path is not: browsers differ). Where browsers read an address in ways this
module does not (IPv6 and numeric hosts other than a dotted quad, user names, encoded dot
segments), the link is refused with a reason. `link_route_test.ts` checks the addresses
against the URL parser of the JavaScript host on a few thousand links. -/
namespace WebRoute
open L4Factoidal.Syntax

/-- Schemes of other apps (mail, phone, messages). A link with one shows the browser's
Outside page; only its button hands the address to the system. There is no list of web
hosts that go to the system: an earlier list (github.com, duckduckgo.com) sent those links
out of the browser without asking, and is gone (owner, 2026-11-16). -/
def systemSchemes : List String := ["mailto","tel","sms"]

/-- The pages of the browser itself, `foafnaut:NAME`, and whether a page takes an
argument after a slash (`foafnaut:sparql/q=...`, `foafnaut:wasm/NAME.wasm#export`).
The graph page is `graphURL`: the graph app draws it. -/
def builtinPages : List (String × Bool) :=
  [("bookmarks",false),("history",false),("settings",false),("wasm",true),("sparql",true),("console",true),("about",false),
   ("search",true),("accessibility",false)]

/-- The FOAF graph is a page of the browser, drawn by the graph app (issue 1268). -/
def graphURL : String := "foafnaut:graph"

/-- Browser commands a `foafnaut:` link may name, with an argument after a slash
(`foafnaut:theme/arcade`, `foafnaut:zoom/150`). -/
def commands : List String :=
  ["back","forward","reload","new","close","home","source","theme","zoom",
   "bookmark","unbookmark","pod","sync","sparql-step","classic","liberal","encoding","search-engine"]

/-- Commands a link may give only on the Settings page; the address bar may type them
(`:search-engine ...`). A page of any site could otherwise choose the search engine. -/
def settingsOnly : List String := ["search-engine"]

/-- What the browser loads itself. -/
structure Site where
  /-- The origin pages come from, `scheme://host[:port]`. Empty: the browser loads every
  web site itself (the native browser). -/
  origin : String := ""
  /-- The folder of the browser's own pages, which has `settings.html`. -/
  pages : String := ""
  /-- The browser reads local files: a link on a local file may open another one. -/
  files : Bool := false
  /-- The address whose Outside page (`Route.outside`) the tab shows now, "" when it shows
  any other page. The host sets it only for the page the browser itself wrote, so a link
  to this address is the press of that page's button. -/
  outside : String := ""
  deriving Repr, BEq

/-- The final action for a link. -/
inductive Route where
  /-- Show the built-in page `name` at `url`, and push `url` on the history. -/
  | page (name url : String)
  /-- Run the graph app in the tab, at `graphURL`. -/
  | graph
  /-- Load `url` in the tab. -/
  | navigate (url : String)
  /-- Show the browser's Outside page for `url`: what the address is, and one button that
  opens it in the host's default browser or another app. The Hub first reads a web address
  in the tab when the site allows it. Nothing leaves the browser by this route. -/
  | outside (url : String)
  /-- Hand `url` to the system: the host's default browser or another app. Only the press
  of the Outside page's button gives it (`system_only_pressed`), or `:open URL` typed in
  the address bar. -/
  | system (url : String)
  /-- A browser command (`back`, `theme`, `zoom`, ...). -/
  | command (name argument : String)
  /-- Do nothing with `url`, and say why. -/
  | refuse (url reason : String)
  deriving Repr, BEq, DecidableEq

/-- The address the tab shows and its history keeps after the route, if it has one. -/
def Route.url? : Route → Option String
  | .page _ url => some url
  | .graph => some graphURL
  | .navigate url => some url
  | _ => none

def Route.isSystem : Route → Bool
  | .system _ => true
  | _ => false

/-! ### Search engines

None is chosen until the person picks one in Settings (owner, 2026-11-16): words typed in
the address bar then go to no one. The list is in alphabetical order and none is first by
choice; a custom engine is an address with `%s` where the words go. -/

/-- A search engine of the Settings list: `%s` in `template` is where the words go. -/
structure SearchEngine where
  id : String
  name : String
  template : String
  deriving Repr, BEq

def searchEngines : List SearchEngine :=
  [⟨"bing","Bing","https://www.bing.com/search?q=%s"⟩,
   ⟨"brave","Brave Search","https://search.brave.com/search?q=%s"⟩,
   ⟨"duckduckgo","DuckDuckGo","https://duckduckgo.com/?q=%s"⟩,
   ⟨"ecosia","Ecosia","https://www.ecosia.org/search?q=%s"⟩,
   ⟨"google","Google","https://www.google.com/search?q=%s"⟩,
   ⟨"kagi","Kagi","https://kagi.com/search?q=%s"⟩,
   ⟨"mojeek","Mojeek","https://www.mojeek.com/search?q=%s"⟩,
   ⟨"qwant","Qwant","https://www.qwant.com/?q=%s"⟩,
   ⟨"startpage","Startpage","https://www.startpage.com/do/search?query=%s"⟩,
   ⟨"wikipedia","Wikipedia (English)","https://en.wikipedia.org/w/index.php?search=%s"⟩]

/-- The longest custom template kept. -/
def maxTemplate : Nat := 512

/-- A custom template: an http or https address with `%s`, no space or control, at most
`maxTemplate` characters. -/
def validTemplate (t : String) : Bool :=
  (t.startsWith "https://" || t.startsWith "http://") && (t.splitOn "%s").length ≥ 2 &&
    t.length ≤ maxTemplate && t.toList.all (fun c => c.toNat > 32 && c.toNat < 127)

/-- The setting as it is kept: an engine's id, a valid custom template, or "" (none, also
for "none" and anything else). -/
def searchSetting (v : String) : String :=
  if (searchEngines.find? (·.id == v)).isSome then v
  else if validTemplate v then v
  else ""

/-- The template of a setting, if a search engine is chosen. -/
def searchTemplate (setting : String) : Option String :=
  if setting.isEmpty then none else
  match searchEngines.find? (·.id == setting) with
  | some e => some e.template
  | none => if validTemplate setting then some setting else none

/-- The name of a setting, for Settings and the search page. -/
def searchName (setting : String) : String :=
  match searchEngines.find? (·.id == setting) with
  | some e => e.name
  | none => if validTemplate setting then "Your own: " ++ setting else "None"

/-- Words for a query: UTF-8, letters, digits and `-_.` as they are, a space as `+`, the
rest percent-encoded. -/
def encodeQuery (value : String) : String :=
  String.join (value.toUTF8.toList.map fun b =>
    let c := Char.ofNat b.toNat
    if c.isAlphanum || c == '-' || c == '_' || c == '.' then c.toString
    else if c == ' ' then "+"
    else
      let digit := fun (n : Nat) => "0123456789ABCDEF".toList[n]!
      String.ofList ['%',digit (b.toNat/16),digit (b.toNat%16)])

private def hexValue (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - 48)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 87)
  else if 'A' ≤ c && c ≤ 'F' then some (c.toNat - 55)
  else none

/-- Where `decodeBytes` is: no `%` pending, a `%` seen, or a `%` and one hex digit seen. -/
inductive Pending where
  | none
  | percent
  | digit (a : Char) (x : Nat)

/-- One character of a query, with no `%` pending: `+` a space, `%` starts a byte. -/
private def plainStep (acc : List UInt8) (c : Char) : Pending × List UInt8 :=
  if c == '%' then (.percent, acc)
  else if c == '+' then (.none, 32 :: acc)
  else (.none, (String.singleton c).toUTF8.toList.reverse ++ acc)

private def decodeStep : Pending × List UInt8 → Char → Pending × List UInt8
  | (.none, acc), c => plainStep acc c
  | (.percent, acc), c =>
    match hexValue c with
    | some x => (.digit c x, acc)
    | none => plainStep (37 :: acc) c
  | (.digit a x, acc), c =>
    match hexValue c with
    | some y => (.none, (x*16+y).toUInt8 :: acc)
    | none => plainStep ((String.singleton a).toUTF8.toList.reverse ++ 37 :: acc) c

/-- The bytes of a query, `+` a space and `%XX` a byte; a `%` without two hex digits is
itself. A left fold, so a long typed line needs no stack. -/
def decodeBytes (cs : List Char) : List UInt8 :=
  match cs.foldl decodeStep (.none, []) with
  | (.none, acc) => acc.reverse
  | (.percent, acc) => (37 :: acc).reverse
  | (.digit a _, acc) => ((String.singleton a).toUTF8.toList.reverse ++ 37 :: acc).reverse

/-- The words of `encodeQuery`, read back; bytes that are not UTF-8 leave the text as it is. -/
def decodeQuery (s : String) : String :=
  (String.fromUTF8? (ByteArray.mk (decodeBytes s.toList).toArray)).getD s

/-- A Wikipedia article title for the words: spaces are `_`, and anything but letters,
digits and `-_.` is percent-encoded. -/
def encodeTitle (words : String) : String :=
  encodeQuery (String.ofList ((words.trimAscii.toString).toList.map fun c => if c == ' ' then '_' else c))

/-- The address a template makes for the words: every `%s` is the encoded words. -/
def expandSearch (template words : String) : String :=
  (encodeQuery words).intercalate (template.splitOn "%s")

/-- The browser's own page for words typed in the address bar, made by the browser from
its own data: nothing is sent anywhere to show it. -/
def searchPageURL (words : String) : String := "foafnaut:search/" ++ encodeQuery words

#guard searchSetting "" == "" && searchSetting "none" == "" && searchSetting "mojeek" == "mojeek"
#guard searchSetting "https://example.org/?q=%s" == "https://example.org/?q=%s"
#guard searchSetting "https://example.org/?q=" == "" && searchSetting "javascript:%s" == ""
#guard searchSetting "https://exa mple.org/?q=%s" == ""
#guard searchTemplate "" == none && searchTemplate "none" == none
#guard expandSearch "https://example.org/?q=%s&x=%s" "a b&c" == "https://example.org/?q=a+b%26c&x=a+b%26c"
#guard searchPageURL "lean browser" == "foafnaut:search/lean+browser"
#guard decodeQuery (encodeQuery "lean browser é&%") == "lean browser é&%" && decodeQuery "a%zz+b%" == "a%zz b%" && decodeQuery "%%41%4" == "%A%4"
#guard encodeTitle " Lean (prover) " == "Lean_%28prover%29"
-- No engine is chosen by default: an empty setting has no template.
theorem no_default_search : searchTemplate "" = none := by decide

/-! ### Reading an href -/

def isSpaceOrControl (c : Char) : Bool := c.toNat ≤ 32
def isTabOrNewline (c : Char) : Bool := c == '\t' || c == '\n' || c == '\r'

/-- Drop spaces and controls at the end. Two reversals and a `dropWhile`, which all run
in a loop: an href can be as long as a page (1 MiB), and the stack is not. -/
def trimEnd (cs : List Char) : List Char := (cs.reverse.dropWhile isSpaceOrControl).reverse

/-- An href as a browser reads it: no space or control at either end, and no tab or line
break inside. -/
def clean (cs : List Char) : List Char :=
  (trimEnd (cs.dropWhile isSpaceOrControl)).filter (!isTabOrNewline ·)

def foafnautPrefix : List Char := ['f','o','a','f','n','a','u','t',':']

def lower (s : String) : String := String.ofList (s.toList.map Char.toLower)

/-- The scheme of an address, in lower case; none for a relative reference. -/
def schemeOf (cs : List Char) : Option String := (parseIri (String.ofList cs)).scheme.map lower

def isSpecial (scheme : String) : Bool := scheme == "http" || scheme == "https" || scheme == "file"

/-- In a web or file address a backslash is a slash, up to the query or fragment. -/
def slashes (cs : List Char) : List Char :=
  let (head, tail) := cs.span (fun c => c != '?' && c != '#')
  head.map (fun c => if c == '\\' then '/' else c) ++ tail

/-! ### Percent-encoding (URL Standard, section 1.3) -/

private def hexDigit (n : Nat) : Char := ("0123456789ABCDEF".toList).getD n '0'
private def percent (c : Char) : List Char :=
  (String.singleton c).toUTF8.toList.flatMap fun b => ['%',hexDigit (b.toNat/16),hexDigit (b.toNat%16)]
/-- Encode controls, everything past `~`, and the characters of `set`. -/
def encode (set : List Char) (s : String) : String :=
  String.ofList (s.toList.flatMap fun c => if c.toNat < 32 || c.toNat > 126 || set.contains c then percent c else [c])
def fragmentSet : List Char := [' ','"','<','>','`']
def querySet : List Char := [' ','"','#','<','>']
def specialQuerySet : List Char := querySet ++ ['\'']
def pathSet : List Char := querySet ++ ['?','`','{','}']

private def optional (mark : String) : Option String → String
  | some value => mark ++ value
  | none => ""

/-! ### Targets -/

/-- An http or https address, read and made canonical. -/
structure Web where
  secure : Bool
  /-- Lower case, never empty. -/
  host : String
  /-- Empty for the scheme's default port. -/
  port : String
  /-- Path, query and fragment, encoded. -/
  rest : String
  deriving Repr, BEq, DecidableEq

def Web.scheme (w : Web) : String := if w.secure then "https" else "http"
def Web.origin (w : Web) : String := w.scheme ++ "://" ++ w.host ++ (if w.port.isEmpty then "" else ":" ++ w.port)
def Web.url (w : Web) : String := w.origin ++ w.rest

/-- What an href points at. -/
inductive Target where
  | foafnaut (rest : List Char)
  | web (w : Web)
  | file (url : String)
  | other (scheme url : String)
  deriving Repr, BEq

private def allDigits (s : String) : Bool := !s.isEmpty && s.toList.all Char.isDigit
private def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')
/-- A label a URL parser reads as a number (URL Standard: "ends in a number"). -/
private def numeric (label : String) : Bool :=
  allDigits label || (label.startsWith "0x" && (label.toList.drop 2).all isHex)
private def octet (label : String) : Bool :=
  allDigits label && (label == "0" || !label.startsWith "0") && label.toNat! ≤ 255
private def hostChar (c : Char) : Bool := c.isAlphanum || c == '-' || c == '_' || c == '.'

/-- The host of a web address: lower case letters, digits, `-`, `_` and dots, with no
empty label; a numeric host only as a dotted quad. -/
def readHost (raw : String) : Except String String := do
  let host := lower raw
  if host.isEmpty then throw "the address has no host"
  if host.startsWith "[" then throw "IPv6 hosts are not opened by this browser"
  unless host.toList.all hostChar do throw "the host has characters this browser does not read"
  let labels := host.splitOn "."
  if labels.any (·.isEmpty) then throw "the host has an empty label"
  if numeric (labels.getLastD "") then
    unless labels.length == 4 && labels.all octet do throw "numeric hosts other than a dotted quad are not opened"
  return host

/-- The port: digits, none past 65535; empty for the default port of the scheme. -/
def readPort (secure : Bool) (raw : String) : Except String String := do
  if raw.isEmpty then return ""
  unless allDigits raw do throw "the port is not a number"
  let n := raw.toNat!
  if n > 65535 then throw "the port is past 65535"
  return if n == (if secure then 443 else 80) then "" else toString n

/-- A path segment that a URL parser reads as `.` or `..`. -/
private def encodedDot (segment : String) : Bool :=
  let s := lower segment
  s.contains '%' && [ "%2e",".%2e","%2e.","%2e%2e" ].contains s

def readWeb (secure : Bool) (p : IriParts) : Except String Web := do
  let some authority := p.authority | throw "a web address needs // and a host"
  if authority.contains '@' then throw "addresses with a user name are not followed"
  let (hostRaw, portRaw) := match authority.toList.span (· != ':') with
    | (h, []) => (String.ofList h, "")
    | (h, _ :: port) => (String.ofList h, String.ofList port)
  let host ← readHost hostRaw
  let port ← readPort secure portRaw
  if (p.path.splitOn "/").any encodedDot then throw "the path has an encoded dot segment"
  let path := if p.path.isEmpty then "/" else p.path
  return {secure := secure,host := host,port := port,rest := encode pathSet path ++ optional "?" (p.query.map (encode specialQuerySet)) ++ optional "#" (p.fragment.map (encode fragmentSet))}

/-- A local file: `file:///path`, or on `localhost`. -/
def readFile (p : IriParts) : Except String String := do
  let host := lower (p.authority.getD "")
  unless host.isEmpty || host == "localhost" do throw "a file on another host is not opened"
  if (p.path.splitOn "/").any encodedDot then throw "the path has an encoded dot segment"
  let path := if p.path.startsWith "/" then p.path else "/" ++ p.path
  return "file://" ++ encode pathSet path ++ optional "?" (p.query.map (encode specialQuerySet)) ++ optional "#" (p.fragment.map (encode fragmentSet))

/-- An absolute address: what it points at. -/
def readAbsolute (address : String) : Except String Target :=
  let p := parseIri address
  match p.scheme.map lower with
  | some "http" => .web <$> readWeb false p
  | some "https" => .web <$> readWeb true p
  | some "file" => .file <$> readFile p
  | some "foafnaut" => .ok (.foafnaut ((address.toList.dropWhile (· != ':')).drop 1))
  | some scheme =>
    -- The system gets the address as a URL parser writes it; a refused one is shown as written.
    if systemSchemes.contains scheme then
      .ok (.other scheme (scheme ++ ":" ++ optional "//" p.authority ++ encode [] p.path ++
        optional "?" (p.query.map (encode querySet)) ++ optional "#" (p.fragment.map (encode fragmentSet))))
    else .ok (.other scheme (scheme ++ ":" ++ String.ofList ((address.toList.dropWhile (· != ':')).drop 1)))
  | none => .error "the address has no scheme"

/-- A base a relative href resolves against: a web or file address. -/
def baseScheme (base : String) : Option String := schemeOf (clean base.toList)

/-- What `href`, on the page at `base`, points at. -/
def analyze (base href : String) : Except String Target :=
  let cs := clean href.toList
  if foafnautPrefix.isPrefixOf cs then .ok (.foafnaut (cs.drop 9)) else
  match schemeOf cs with
  | some scheme =>
    if scheme == "foafnaut" then .ok (.foafnaut ((cs.dropWhile (· != ':')).drop 1))
    else if isSpecial scheme then
      -- `http:x` and `http:/x` mean other things to other parsers: a web address needs `//`.
      let prepared := slashes cs
      if (prepared.dropWhile (· != ':')).take 3 != [':','/','/'] then .error "a web address needs // and a host"
      else readAbsolute (resolveIri base (String.ofList prepared))
    -- Another app's address is opaque: no dot segment is removed from it.
    else readAbsolute (String.ofList cs)
  | none =>
    match baseScheme base with
    | some b => if isSpecial b then readAbsolute (resolveIri base (String.ofList (slashes cs)))
      else .error "a relative link needs a web page or a local file around it"
    | none => .error "a relative link needs a web page or a local file around it"

/-! ### The route -/

/-- The address the tab shows for a built-in page. Settings is a page of the site. -/
def pageURL (site : Site) (name : String) : String :=
  if name == "settings" && !site.pages.isEmpty then resolveIri site.pages "settings.html" else "foafnaut:" ++ name

/-- What a `foafnaut:` address names, by what follows the colon. -/
inductive Builtin where
  /-- A built-in page, with its argument. -/
  | page (name : String) (argument : Option String)
  | graph
  | command (name argument : String)
  | refuse (reason : String)
  deriving Repr, DecidableEq

/-- The argument a page takes from a form's GET (`foafnaut:NAME?QUERY`, HTML §4.10.21.3
"mutate action URL"): the search page takes the words of field `q`, as the address bar gives
them (`searchPageURL`); another page takes the query as it is (`q=QUERY&step=N` for SPARQL). -/
def formArgument (page : String) (query : List Char) : List Char :=
  if page == "search" then
    ((((String.ofList query).splitOn "&").find? (·.startsWith "q=")).map (·.toList.drop 2)).getD []
  else query

def builtin (rest : List Char) : Builtin :=
  let (name, after) := rest.span (· != '/')
  let argument := after.drop 1
  -- A form's GET to a page: `foafnaut:NAME?QUERY` is `foafnaut:NAME/ARGUMENT`.
  let (name, after, argument) := match name.span (· != '?') with
    | (page, '?' :: query) =>
      if after.isEmpty && (builtinPages.find? (·.1.toList == page)).any (·.2) then
        let arg := formArgument (String.ofList page) query
        (page, (if arg.isEmpty then [] else '/' :: arg), arg)
      else (name, after, argument)
    | _ => (name, after, argument)
  if name == "graph".toList then
    if after.isEmpty then .graph else .refuse "foafnaut:graph takes no argument"
  else match builtinPages.find? (·.1.toList == name) with
  | some (page,takes) =>
    if argument.isEmpty then .page page none
    else if takes then .page page (some (String.ofList argument))
    else .refuse s!"foafnaut:{page} takes no argument"
  | none =>
    match commands.find? (·.toList == name) with
    | some command => .command command (String.ofList argument)
    | none => if name == "help".toList then .page "settings" none else .refuse "this browser has no such page"

def Builtin.route (site : Site) (url : String) : Builtin → Route
  | .page name none => .page name (pageURL site name)
  | .page name (some argument) => .page name ("foafnaut:" ++ name ++ "/" ++ argument)
  | .graph => .graph
  | .command name argument => .command name argument
  | .refuse reason => .refuse url reason

/-- A `foafnaut:` address, by what follows the colon. Never the system, never a load. -/
def foafnautRoute (site : Site) (rest : List Char) : Route :=
  (builtin rest).route site (String.ofList (foafnautPrefix ++ rest))

/-- Same origin as the site. -/
def sameSite (site : Site) (w : Web) : Bool := !site.origin.isEmpty && w.origin == site.origin

/-- Another site that this browser does not load itself (the Hub): its Outside page. -/
def otherSite (site : Site) (w : Web) : Bool := !site.origin.isEmpty && !sameSite site w

/-- An address that leaves the browser only by a press: the system when the tab shows the
browser's own Outside page for it (the link is that page's button), else that page. -/
def outsideOrPress (site : Site) (url : String) : Route :=
  if !site.outside.isEmpty && site.outside == url then .system url else .outside url

/-- A settings-only command from a link on any page but Settings is refused. -/
def fromPage (site : Site) (base : String) : Route → Route
  | .command name argument =>
    if settingsOnly.contains name && base != pageURL site "settings" then
      .refuse ("foafnaut:" ++ name ++ (if argument.isEmpty then "" else "/" ++ argument))
        "only the Settings page, or the address bar, chooses a search engine"
    else .command name argument
  | r => r

/-- The route for a target. -/
def decide (site : Site) (base : String) : Target → Route
  | .foafnaut rest => fromPage site base (foafnautRoute site rest)
  | .web w =>
    if sameSite site w then .navigate w.url
    else if site.origin.isEmpty then .navigate w.url
    else outsideOrPress site w.url
  | .file url =>
    if site.files && baseScheme base == some "file" then .navigate url
    else .refuse url "a web page can not open local files"
  | .other scheme url =>
    if systemSchemes.contains scheme then outsideOrPress site url
    else if scheme == "javascript" then .refuse url "a link that runs a script is not followed"
    else if scheme == "data" then .refuse url "data URLs are not opened as pages"
    else .refuse url s!"this browser does not open {scheme}: links"

/-- Where a link goes: the href of the link, the address of the page it is on (its base
URL), and the site. -/
def route (site : Site) (base href : String) : Route :=
  match analyze base href with
  | .ok target => decide site base target
  | .error reason => .refuse (String.ofList (clean href.toList)) reason

/-- `route`, with `about:foafnaut` (version and build) as the page `foafnaut:about`. -/
def routeAddress (site : Site) (base href : String) : Route :=
  if clean href.toList == "about:foafnaut".toList then foafnautRoute site "about".toList
  else route site base href

/-- A browser command or page typed as `:NAME ARGUMENT` routes as `foafnaut:NAME/ARGUMENT`. -/
def commandRoute (site : Site) (name argument : String) : Route :=
  foafnautRoute site (name.toList ++ (if argument.isEmpty then [] else '/' :: argument.toList))

/-! ### Checks -/

private def hub : Site := {origin := "https://danbri.github.io",pages := "https://danbri.github.io/factoidal-core/web/hub/foafnaut/pages/"}
private def here : String := "https://danbri.github.io/factoidal-core/web/hub/foafnaut/pages/index.html"
private def native : Site := {pages := "file:///lab/pages/",files := true}
#guard route hub here "foafnaut:graph" == .graph
#guard routeAddress native "file:///lab/pages/index.html" "about:foafnaut" == .page "about" "foafnaut:about"
#guard routeAddress native "file:///lab/pages/index.html" "foafnaut:graph" == route native "file:///lab/pages/index.html" "foafnaut:graph"
#guard route hub here "FOAFNAUT:graph" == .graph && route hub here " foafnaut:graph\n" == .graph
#guard route hub here "foafnaut:settings" == .page "settings" "https://danbri.github.io/factoidal-core/web/hub/foafnaut/pages/settings.html"
#guard route hub here "foafnaut:sparql/q=ASK+%7B%7D" == .page "sparql" "foafnaut:sparql/q=ASK+%7B%7D"
#guard route hub here "foafnaut:wasm" == .page "wasm" "foafnaut:wasm"
#guard route hub here "foafnaut:console" == .page "console" "foafnaut:console"
#guard route hub here "foafnaut:accessibility" == .page "accessibility" "foafnaut:accessibility"
#guard route hub here "foafnaut:console/2" == .page "console" "foafnaut:console/2"
-- A form's GET (the new tab page): the query is the page's argument; search takes field q.
#guard route hub here "foafnaut:sparql?q=ASK+%7B%7D" == .page "sparql" "foafnaut:sparql/q=ASK+%7B%7D"
#guard route hub here "foafnaut:search?q=lean+browser" == .page "search" "foafnaut:search/lean+browser"
#guard route hub here "foafnaut:search?x=1&q=a" == .page "search" "foafnaut:search/a"
#guard route hub here "foafnaut:search?q=" == .page "search" "foafnaut:search"
#guard route hub here "foafnaut:settings?x=1" == .refuse "foafnaut:settings?x=1" "this browser has no such page"
#guard route hub here "foafnaut:theme?x=dark" == .refuse "foafnaut:theme?x=dark" "this browser has no such page"
#guard route hub here "foafnaut:search-engine?q=x" == .refuse "foafnaut:search-engine?q=x" "this browser has no such page"
#guard route hub here "foafnaut:liberal/on" == .command "liberal" "on"
#guard route hub here "foafnaut:theme/arcade" == .command "theme" "arcade"
#guard route hub here "foafnaut:classic/off" == .command "classic" "off"
#guard route hub here "foafnaut:nothing" == .refuse "foafnaut:nothing" "this browser has no such page"
#guard route hub here "status.html" == .navigate "https://danbri.github.io/factoidal-core/web/hub/foafnaut/pages/status.html"
#guard route hub here "../x/./y.html?a b#c d" == .navigate "https://danbri.github.io/factoidal-core/web/hub/foafnaut/x/y.html?a%20b#c%20d"
#guard route hub here "HTTPS://DANBRI.github.io:443" == .navigate "https://danbri.github.io/"
-- Another site, mail: the Outside page, and the system only for a press of its button.
#guard route hub here "https://example.org/a" == .outside "https://example.org/a"
#guard route hub here "https://github.com/danbri/factoidal-core" == .outside "https://github.com/danbri/factoidal-core"
#guard route hub here "https://duckduckgo.com/?q=x" == .outside "https://duckduckgo.com/?q=x"
#guard route hub here "mailto:someone@example.org" == .outside "mailto:someone@example.org"
#guard route {hub with outside := "https://example.org/a"} "https://example.org/a" "https://example.org/a" == .system "https://example.org/a"
#guard route {hub with outside := "https://example.org/a"} "https://example.org/a" "https://example.org/b" == .outside "https://example.org/b"
#guard route {native with outside := "mailto:a@example.org"} "mailto:a@example.org" "mailto:a@example.org" == .system "mailto:a@example.org"
#guard route native "https://example.org/" "tel:+44" == .outside "tel:+44"
-- The search engine is chosen on Settings, or typed; a link elsewhere can not choose it.
#guard route hub here "foafnaut:search-engine/mojeek" == .refuse "foafnaut:search-engine/mojeek" "only the Settings page, or the address bar, chooses a search engine"
#guard route hub (pageURL hub "settings") "foafnaut:search-engine/mojeek" == .command "search-engine" "mojeek"
#guard route native (pageURL native "settings") "foafnaut:search-engine/none" == .command "search-engine" "none"
#guard commandRoute hub "search-engine" "mojeek" == .command "search-engine" "mojeek"
#guard route hub here "foafnaut:search/lean+browser" == .page "search" "foafnaut:search/lean+browser"
#guard (route hub here "javascript:alert(1)").isSystem == false
#guard route hub here "file:///etc/passwd" == .refuse "file:///etc/passwd" "a web page can not open local files"
#guard route hub here "https://user@danbri.github.io/" == .refuse "https://user@danbri.github.io/" "addresses with a user name are not followed"
#guard route hub here "http:x" == .refuse "http:x" "a web address needs // and a host"
#guard route hub "foafnaut:sparql/x" "a.html" == .refuse "a.html" "a relative link needs a web page or a local file around it"
#guard route native "file:///lab/pages/index.html" "showcase.html" == .navigate "file:///lab/pages/showcase.html"
#guard route native "https://example.org/" "https://example.org/b" == .navigate "https://example.org/b"
#guard route native "https://example.org/" "file:///etc/hosts" == .refuse "file:///etc/hosts" "a web page can not open local files"
#guard route native "https://example.org/" "https://www.github.com/x" == .navigate "https://www.github.com/x"
#guard route native "https://example.org/" "https://duckduckgo.com/" == .navigate "https://duckduckgo.com/"
#guard route native "https://example.org/" "http://127.0.0.1:8080/x" == .navigate "http://127.0.0.1:8080/x"
#guard route native "https://example.org/" "http://0x7f.1/" == .refuse "http://0x7f.1/" "numeric hosts other than a dotted quad are not opened"
#guard commandRoute hub "zoom" "150" == .command "zoom" "150" && commandRoute hub "help" "" == route hub here "foafnaut:settings"

/-! ### Theorems -/

theorem foafnautRoute_not_system (site : Site) (rest : List Char) (u : String) :
    foafnautRoute site rest ≠ .system u := by
  unfold foafnautRoute
  cases builtin rest with
  | page name argument => cases argument <;> simp [Builtin.route]
  | _ => simp [Builtin.route]

theorem foafnautRoute_not_navigate (site : Site) (rest : List Char) (u : String) :
    foafnautRoute site rest ≠ .navigate u := by
  unfold foafnautRoute
  cases builtin rest with
  | page name argument => cases argument <;> simp [Builtin.route]
  | _ => simp [Builtin.route]

/-- `fromPage` only ever refuses a command: it makes no system route. -/
theorem fromPage_system (site : Site) (base : String) (r : Route) (u : String)
    (h : fromPage site base r = .system u) : r = .system u := by
  cases r with
  | command name argument =>
    simp only [fromPage] at h
    split at h <;> simp at h
  | _ => simpa [fromPage] using h

theorem foafnaut_decide_not_system (site : Site) (base : String) (rest : List Char) (u : String) :
    decide site base (.foafnaut rest) ≠ .system u := by
  intro h
  exact foafnautRoute_not_system site rest u (fromPage_system _ _ _ _ h)

private theorem trimEnd_append (pre rest : List Char) (h : pre.all (!isSpaceOrControl ·) = true) :
    trimEnd (pre ++ rest) = pre ++ trimEnd rest := by
  unfold trimEnd
  rw [List.reverse_append, List.dropWhile_append]
  split
  · rename_i hr
    have hpre : pre.reverse.dropWhile isSpaceOrControl = pre.reverse := by
      cases hp : pre.reverse with
      | nil => rfl
      | cons c cs =>
        have hc : c ∈ pre := by rw [← List.mem_reverse, hp]; simp
        have : isSpaceOrControl c = false := by
          have := List.all_eq_true.mp h c hc; simpa using this
        simp [this]
    rw [hpre, List.reverse_reverse]
    have : rest.reverse.dropWhile isSpaceOrControl = [] := by simpa using hr
    rw [this]; simp
  · simp [List.reverse_append]

private theorem prefix_plain : foafnautPrefix.all (!isSpaceOrControl ·) = true := by decide

private theorem clean_foafnaut (rest : List Char) :
    clean (foafnautPrefix ++ rest) = foafnautPrefix ++ (trimEnd rest).filter (!isTabOrNewline ·) := by
  have hd : (foafnautPrefix ++ rest).dropWhile isSpaceOrControl = foafnautPrefix ++ rest := by
    have : isSpaceOrControl 'f' = false := by decide
    simp only [foafnautPrefix, List.cons_append, List.dropWhile_cons, this]; rfl
  have ht : trimEnd (foafnautPrefix ++ rest) = foafnautPrefix ++ trimEnd rest := trimEnd_append _ _ prefix_plain
  have hf : foafnautPrefix.filter (!isTabOrNewline ·) = foafnautPrefix := by decide
  simp only [clean, hd, ht, List.filter_append, hf]

private theorem prefix_self (rest : List Char) : foafnautPrefix.isPrefixOf (foafnautPrefix ++ rest) = true := by
  simp [foafnautPrefix, List.isPrefixOf]

private theorem foafnaut_toList : "foafnaut:".toList = foafnautPrefix := by decide

/-- An href that starts with `foafnaut:` points at a page of the browser, by what follows. -/
theorem analyze_foafnaut (base rest : String) :
    analyze base ("foafnaut:" ++ rest) = .ok (.foafnaut ((trimEnd rest.toList).filter (!isTabOrNewline ·))) := by
  have hl : ("foafnaut:" ++ rest).toList = foafnautPrefix ++ rest.toList := by
    rw [String.toList_append, foafnaut_toList]
  simp only [analyze, hl, clean_foafnaut, prefix_self, if_true]
  simp [foafnautPrefix]

/-- No `foafnaut:` href is ever handed to the system. -/
theorem foafnaut_never_system (site : Site) (base rest u : String) :
    route site base ("foafnaut:" ++ rest) ≠ .system u := by
  simp only [route, analyze_foafnaut]
  exact foafnaut_decide_not_system _ _ _ _

/-- Nor any href whose scheme, as a browser reads it (any case, spaces at the ends), is
`foafnaut`. -/
theorem foafnaut_scheme_never_system (site : Site) (base href u : String)
    (h : schemeOf (clean href.toList) = some "foafnaut") : route site base href ≠ .system u := by
  simp only [route, analyze]
  by_cases hp : foafnautPrefix.isPrefixOf (clean href.toList) = true
  · simp only [hp, if_true]; exact foafnaut_decide_not_system _ _ _ _
  · simp only [hp, h, Bool.false_eq_true, if_false, beq_self_eq_true, if_true]
    exact foafnaut_decide_not_system _ _ _ _

theorem outsideOrPress_system (site : Site) (url u : String) (h : outsideOrPress site url = .system u) :
    u = url ∧ site.outside = url ∧ site.outside ≠ "" := by
  unfold outsideOrPress at h
  by_cases hc : (!site.outside.isEmpty && site.outside == url) = true
  · rw [if_pos hc] at h
    injection h with h
    rw [Bool.and_eq_true] at hc
    obtain ⟨h1, h2⟩ := hc
    have heq : site.outside = url := by simpa using h2
    refine ⟨h.symm, heq, ?_⟩
    intro h0
    rw [h0] at h1
    exact absurd h1 (by decide)
  · rw [if_neg hc] at h
    cases h

/-- A link hands an address to the system only when the tab shows the browser's own
Outside page for that very address (`site.outside`), so the link is that page's button;
and the address is then a web address of another site when the browser loads only its own
site (the Hub), or an address of another app's scheme (`mailto:`, `tel:`, `sms:`). No web
host is on any list that goes to the system. -/
theorem system_only_pressed (site : Site) (base href u : String) (h : route site base href = .system u) :
    site.outside = u ∧ u ≠ "" ∧
    ((∃ w : Web, analyze base href = .ok (.web w) ∧ u = w.url ∧ sameSite site w = false ∧ otherSite site w = true) ∨
     (∃ scheme, analyze base href = .ok (.other scheme u) ∧ systemSchemes.contains scheme = true)) := by
  unfold route at h
  split at h
  · rename_i target ht
    cases target with
    | foafnaut rest => exact absurd h (foafnaut_decide_not_system _ _ _ _)
    | web w =>
      simp only [decide] at h
      by_cases hs : sameSite site w = true
      · simp [hs] at h
      · simp only [hs, Bool.false_eq_true, if_false] at h
        by_cases ho : site.origin.isEmpty = true
        · simp [ho] at h
        · simp only [ho, Bool.false_eq_true, if_false] at h
          obtain ⟨hu, hout, hne⟩ := outsideOrPress_system _ _ _ h
          subst hu
          refine ⟨hout, by rw [← hout]; exact hne, Or.inl ⟨w, ht, rfl, by simpa using hs, ?_⟩⟩
          simp only [otherSite, hs, ho]; rfl
    | file url =>
      simp only [decide] at h
      split at h <;> simp at h
    | other scheme url =>
      simp only [decide] at h
      by_cases hs : systemSchemes.contains scheme = true
      · simp only [hs, if_true] at h
        obtain ⟨hu, hout, hne⟩ := outsideOrPress_system _ _ _ h
        subst hu
        exact ⟨hout, by rw [← hout]; exact hne, Or.inr ⟨scheme, ht, hs⟩⟩
      · simp only [hs, Bool.false_eq_true, if_false] at h
        split at h
        · simp at h
        · split at h <;> simp at h
  · simp at h

/-- With no Outside page shown, no link goes to the system: every way out of the browser
is a page first, and a press on that page's button. -/
theorem no_system_unpressed (site : Site) (base href u : String) (h : site.outside = "") :
    route site base href ≠ .system u := by
  intro hr
  have hout := (system_only_pressed site base href u hr).1
  have hne := (system_only_pressed site base href u hr).2.1
  exact hne (by rw [← hout]; exact h)

/-- The native browser loads every web site itself: a web address of any host loads in the
tab, and is never handed to the system. -/
theorem native_web_navigates (site : Site) (base href : String) (w : Web)
    (h : analyze base href = .ok (.web w)) (ho : site.origin = "") :
    route site base href = .navigate w.url := by
  have he : site.origin.isEmpty = true := by rw [ho]; decide
  have hs : sameSite site w = false := by simp [sameSite, he]
  simp [route, h, decide, hs, he]

/-- A link on a page other than Settings never chooses the search engine. -/
theorem settings_only_from_settings (site : Site) (base href argument : String)
    (hb : base ≠ pageURL site "settings") : route site base href ≠ .command "search-engine" argument := by
  intro h
  unfold route at h
  split at h
  · rename_i target _
    cases target with
    | foafnaut rest =>
      simp only [decide] at h
      generalize foafnautRoute site rest = r at h
      cases r with
      | command name arg =>
        simp only [fromPage] at h
        split at h
        · simp at h
        · rename_i hc
          simp only [Route.command.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          apply hc
          simp [settingsOnly, hb]
      | _ => simp [fromPage] at h
    | web w =>
      simp only [decide] at h
      split at h
      · simp at h
      · split at h
        · simp at h
        · unfold outsideOrPress at h; split at h <;> simp at h
    | file url => simp only [decide] at h; split at h <;> simp at h
    | other scheme url =>
      simp only [decide] at h
      split at h
      · unfold outsideOrPress at h; split at h <;> simp at h
      · split at h
        · simp at h
        · split at h <;> simp at h
  · simp at h

/-- An http(s) address of the site's own origin always loads in the tab. -/
theorem same_site_navigates (site : Site) (base href : String) (w : Web)
    (h : analyze base href = .ok (.web w)) (hs : sameSite site w = true) :
    route site base href = .navigate w.url := by
  simp [route, h, decide, hs]

/-- A relative href (no scheme, as a browser reads it) is resolved against the address of
the page it is on, by RFC 3986, when that page is a web page or a local file; on any
other page it is refused. -/
theorem relative_resolves_against_base (base href : String)
    (hp : foafnautPrefix.isPrefixOf (clean href.toList) = false) (hr : schemeOf (clean href.toList) = none) :
    analyze base href =
      match baseScheme base with
      | some b => if isSpecial b then readAbsolute (resolveIri base (String.ofList (slashes (clean href.toList))))
        else .error "a relative link needs a web page or a local file around it"
      | none => .error "a relative link needs a web page or a local file around it" := by
  simp only [analyze, hp, hr, Bool.false_eq_true, if_false]

/-- Every built-in page name routes to its page, on every page and site. -/
theorem builtin_resolves (site : Site) (base : String) :
    ∀ p ∈ builtinPages, route site base ("foafnaut:" ++ p.1) = .page p.1 (pageURL site p.1) := by
  intro p hp
  simp only [builtinPages, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [route, analyze_foafnaut, decide, foafnautRoute]
  · rw [show builtin ((trimEnd "bookmarks".toList).filter (!isTabOrNewline ·)) = .page "bookmarks" none by decide]; rfl
  · rw [show builtin ((trimEnd "history".toList).filter (!isTabOrNewline ·)) = .page "history" none by decide]; rfl
  · rw [show builtin ((trimEnd "settings".toList).filter (!isTabOrNewline ·)) = .page "settings" none by decide]; rfl
  · rw [show builtin ((trimEnd "wasm".toList).filter (!isTabOrNewline ·)) = .page "wasm" none by decide]; rfl
  · rw [show builtin ((trimEnd "sparql".toList).filter (!isTabOrNewline ·)) = .page "sparql" none by decide]; rfl
  · rw [show builtin ((trimEnd "console".toList).filter (!isTabOrNewline ·)) = .page "console" none by decide]; rfl
  · rw [show builtin ((trimEnd "about".toList).filter (!isTabOrNewline ·)) = .page "about" none by decide]; rfl
  · rw [show builtin ((trimEnd "search".toList).filter (!isTabOrNewline ·)) = .page "search" none by decide]; rfl
  · rw [show builtin ((trimEnd "accessibility".toList).filter (!isTabOrNewline ·)) = .page "accessibility" none by decide]; rfl

/-- `foafnaut:graph` runs the graph app. -/
theorem graph_resolves (site : Site) (base : String) : route site base graphURL = .graph := by
  have : graphURL = "foafnaut:" ++ "graph" := rfl
  rw [this]; simp only [route, analyze_foafnaut, decide, foafnautRoute]
  rw [show builtin ((trimEnd "graph".toList).filter (!isTabOrNewline ·)) = .graph by decide]; rfl

/-! ### History

The hosts keep one `WebHistory.History` for each tab. After a route with an address
(`Route.url?`) they show the page and push the address (`historyPush`); back and forward
are `WebHistory.apply` with `backCommand` and `forwardCommand`, and load the address that
it answers. -/

open WebHistory in
private theorem push_shape (h : History) (prev url : String) (hc : h.current = some prev) (hn : prev ≠ url) :
    ∃ k : Array String, h.push url = {entries := k, index := k.size - 1} ∧ 2 ≤ k.size ∧
      k[k.size - 1]? = some url ∧ k[k.size - 2]? = some prev := by
  have hi : h.index < h.entries.size := by
    unfold History.current at hc
    exact (Array.getElem?_eq_some_iff.mp hc).1
  have hne : (h.current == some url) = false := by simp [hc, hn]
  unfold History.push
  simp only [hne, Bool.false_eq_true, if_false]
  refine ⟨_, rfl, ?_⟩
  have hs1 : ((h.entries.extract 0 (h.index + 1)).push url).size = h.index + 2 := by
    simp [Array.size_extract]; omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [Array.size_extract, hs1, maxEntries]; omega
  · rw [Array.getElem?_extract]
    simp only [Array.size_extract, hs1, maxEntries]
    rw [if_pos (by omega), Array.getElem?_push]
    rw [if_pos (by simp [Array.size_extract]; omega)]
  · rw [Array.getElem?_extract]
    simp only [Array.size_extract, hs1, maxEntries]
    rw [if_pos (by omega), Array.getElem?_push]
    rw [if_neg (by simp [Array.size_extract]; omega), Array.getElem?_extract]
    rw [if_pos (by omega)]
    unfold History.current at hc
    rw [← hc]; congr 1; omega
open WebHistory in
theorem apply_back (h : History) : apply backCommand h = (h.back, if h.canBack then h.back.current else none) := rfl

open WebHistory in
theorem apply_forward (h : History) :
    apply forwardCommand h = (h.forward, if h.canForward then h.forward.current else none) := rfl
open WebHistory in
/-- Push a new address on a history with a current entry: back answers that entry, and
forward after it answers the new address. -/
theorem push_back_forward (h : History) (prev url : String) (hc : h.current = some prev) (hn : prev ≠ url) :
    (apply backCommand (h.push url)).2 = some prev ∧
    (apply forwardCommand (apply backCommand (h.push url)).1).2 = some url := by
  obtain ⟨k, hk, h2, hlast, hprev⟩ := push_shape h prev url hc hn
  rw [hk, apply_back]
  have hb : ({entries := k, index := k.size - 1} : History).canBack = true := by
    simp [History.canBack]; omega
  have hback : ({entries := k, index := k.size - 1} : History).back = {entries := k, index := k.size - 2} := by
    simp only [History.back, hb, if_true]; congr 1
  have hf : ({entries := k, index := k.size - 2} : History).canForward = true := by
    simp [History.canForward]; omega
  have hfwd : ({entries := k, index := k.size - 2} : History).forward = {entries := k, index := k.size - 1} := by
    simp only [History.forward, hf, if_true]; congr 1; omega
  rw [if_pos hb, hback, apply_forward, if_pos hf, hfwd]
  exact ⟨hprev, hlast⟩

open WebHistory in
/-- Back after following a built-in page link returns to the previous entry, and forward
returns to the built-in page. -/
theorem history_roundtrip (site : Site) (base : String) (p : String × Bool) (hp : p ∈ builtinPages)
    (h : History) (prev : String) (hc : h.current = some prev) (hn : prev ≠ pageURL site p.1) :
    ∃ u, (route site base ("foafnaut:" ++ p.1)).url? = some u ∧
      (apply backCommand (h.push u)).2 = some prev ∧
      (apply forwardCommand (apply backCommand (h.push u)).1).2 = some u := by
  refine ⟨pageURL site p.1, by rw [builtin_resolves site base p hp]; rfl, ?_⟩
  exact push_back_forward h prev _ hc hn

open WebHistory in
/-- The same for the graph page. -/
theorem graph_history_roundtrip (site : Site) (base : String) (h : History) (prev : String)
    (hc : h.current = some prev) (hn : prev ≠ graphURL) :
    (route site base graphURL).url? = some graphURL ∧
    (apply backCommand (h.push graphURL)).2 = some prev ∧
    (apply forwardCommand (apply backCommand (h.push graphURL)).1).2 = some graphURL := by
  refine ⟨by rw [graph_resolves]; rfl, ?_⟩
  exact push_back_forward h prev _ hc hn

end WebRoute
