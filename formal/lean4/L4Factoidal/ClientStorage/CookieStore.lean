/-
L4Factoidal.ClientStorage.CookieStore — the Cookie Store API (WICG cookie-store):
`cookieStore.get`, `getAll`, `set` and `delete` of a document, over the session's cookie jar
(`Net.Cookies`, the jar `document.cookie` reads and writes).

## Decisions

* **One jar.** The cookie store reads and writes the jar of `Net.Cookies` through that
  module's own steps: a cookie is admitted by `Net.Cookies.admit` (host of the page, never
  `HttpOnly`, prefixes), stored by `store`, which is proved to be the storage step of
  `document.cookie = text` (`setFromScript_store`), and read by `visibleCookies`. So a cookie
  set by either API is read back by the other, and what `Net.Cookies` proves about the jar
  holds here: a set never adds a cookie for another host (`set_keeps_host`) and a read
  answers only the page's own host's cookies (`read_host`).
* **The page's host is never an argument.** The site comes from the session's page origin
  and its secure flag (`Net.Cookies.siteOf`); the arguments give only the name, value,
  attributes, the document's URL (for the default path and the `url` option's check), and
  the time.
* **The checks of "set a cookie" (cookie-store §7.1)**, in order, each a `TypeError`: name
  and value are trimmed of spaces and tabs; a control character or `;` in either; `=` in the
  name; an empty name with an empty value, a value holding `=`, or a value with a cookie
  prefix; a name with an HTTP-only prefix (`__Http-`, `__Host-Http-`); name and value over
  4096 bytes; a domain starting with `.`, not the host or a parent of it, over 1024 bytes,
  or given for a `__Host-` name; a path not starting with `/`, over 1024 bytes, or other than
  `/` for a `__Host-` name. A cookie of the store is always `Secure`.
* `delete` removes the cookies of that name, host and path (default `/`), as setting an
  expired cookie does, with the same domain and path checks.
* `get` and `getAll` with a `url`: in a window the URL (fragment excluded) must equal the
  document's URL, else `TypeError`; its path is the path cookies are matched against.
* Not modelled: `SameSite` and `Partitioned` (the jar has no such fields: every cookie is
  treated as `SameSite=Strict`, unpartitioned), the domain of a domain cookie (the jar keeps
  host-only cookies), and change events.

Commands (`web_api` op 204): the fields are the command, the document's URL, the time in
milliseconds, then: `get`/`getAll`: has-name (`1`/`0`), name, url (empty: none); `set`: name,
value, has-domain, domain, has-path, path, expires in milliseconds (empty: a session cookie);
`delete`: name, has-domain, domain, has-path, path. Answers: `ok` and name/value pairs, or
`!TypeError`.
-/
import L4Factoidal.Net.Cookies

namespace L4Factoidal.ClientStorage.CookieStore

open L4Factoidal.Net.Cookies

/-! ## The storage step shared with `document.cookie` -/

/-- Store an admitted cookie in the jar at `now` (RFC 6265bis §5.7 steps 22 to 24): it
replaces the cookie of its name, host and path (keeping its creation place), unless that one
is `HttpOnly`; an expired cookie only removes; at most `maxPerHost` cookies of a host. -/
def store (jar : Jar) (now : Nat) (c : Cookie) : Jar :=
  if jar.cookies.any (fun o => sameKey o c && o.httpOnly) then jar else
  let old := jar.cookies.find? (sameKey · c)
  let rest := jar.cookies.filter fun o => !sameKey o c && !expired o now
  if expired c now then { jar with cookies := rest } else
  let c := { c with created := (old.map (·.created)).getD jar.next }
  let kept := if (rest.filter (·.host == c.host)).length ≥ maxPerHost then rest.drop 1 else rest
  { cookies := kept ++ [c], next := jar.next + 1 }

/-- Kind: refinement. Says: `document.cookie = text` is "parse, then `store`": the cookie
store's writes go through the same storage step as `document.cookie`'s. -/
theorem setFromScript_store (jar : Jar) (site : Site) (now : Nat) (text : String) :
    setFromScript jar site now text =
      match parseForScript site now text with
      | none => jar
      | some c => store jar now c := rfl

/-! ## Checks of names, values and attributes -/

def isWs (c : Char) : Bool := c == ' ' || c == '\t'

/-- Without leading and trailing spaces and tabs. -/
def normalize (s : String) : String :=
  String.ofList ((s.toList.dropWhile isWs).reverse.dropWhile isWs).reverse

def forbidden (c : Char) : Bool := isCtl c || c == ';'

def startsCI (s p : String) : Bool := (lower s).startsWith p

/-- The cookie name prefixes a nameless cookie's value may not start with. -/
def prefixes : List String := ["__secure-", "__host-", "__http-", "__host-http-"]

/-- The checks of name and value (normalized). -/
def nameValueOk (name value : String) : Bool :=
  !(name.toList.any forbidden) && !(value.toList.any forbidden) &&
  !name.toList.contains '=' &&
  !(name.isEmpty && (value.isEmpty || value.toList.contains '=' || prefixes.any (startsCI value ·))) &&
  !(startsCI name "__http-" || startsCI name "__host-http-") &&
  name.utf8ByteSize + value.utf8ByteSize ≤ maxNameValue

/-- The checks of the domain and path attributes for a cookie of `name` on `host`. -/
def attrsOk (host name : String) (domain path : Option String) : Bool :=
  (match domain with
   | none => true
   | some d => !d.startsWith "." && !startsCI name "__host-" && (host == d || host.endsWith ("." ++ d)) &&
       d.utf8ByteSize ≤ maxAttribute) &&
  (match path with
   | none => true
   | some p => p.startsWith "/" && p.utf8ByteSize ≤ maxAttribute && (!startsCI name "__host-" || p == "/"))

/-- Seconds since the epoch of a time in milliseconds (a time before the epoch is 0). -/
def secondsOf (ms : String) : Nat :=
  match ms.toInt? with
  | some t => if t < 0 then 0 else t.toNat / 1000
  | none => 0

/-- `cookieStore.set`: the jar after it, or `none` for a `TypeError`. -/
def set (jar : Jar) (site : Site) (now : Nat) (name value : String) (domain path : Option String)
    (expires : Option Nat) : Option Jar :=
  let name := normalize name
  let value := normalize value
  if !nameValueOk name value || !attrsOk site.host name domain path then none else
  match admit site now name value { expires, domain, path := some (path.getD "/"), secure := true } with
  | none => none
  | some c => some (store jar now c)

/-- `cookieStore.delete`: the jar after it, or `none` for a `TypeError`. -/
def delete (jar : Jar) (site : Site) (now : Nat) (name : String) (domain path : Option String) : Option Jar :=
  let name := normalize name
  if !attrsOk site.host name domain path then none else
  some (store jar now { name, value := "", host := site.host, path := path.getD "/", secure := true, expires := some 0 })

/-! ## Reading -/

/-- A URL without its fragment. -/
def noFragment (u : String) : String := String.ofList (u.toList.takeWhile (· != '#'))

/-- The path of an absolute URL (`/` when it has none). -/
def pathOfUrl (u : String) : String :=
  let rest := match (noFragment u).splitOn "://" with
    | [_, r] => r
    | _ => ""
  let p := (rest.toList.dropWhile (· != '/')).takeWhile (· != '?')
  if p.isEmpty then "/" else String.ofList p

/-- `getAll` (and `get`, its first item): the cookies the document reads at the path of
`url`, of name `name` when one is given; `none` for a `TypeError` (a `url` other than the
document's). -/
def read (jar : Jar) (site : Site) (now : Nat) (docUrl : String) (name : Option String) (url : Option String) :
    Option (List Cookie) :=
  match url with
  | some u =>
    if noFragment u != noFragment docUrl then none
    else some ((visibleCookies jar { site with path := pathOfUrl u } now).filter fun c => name.all (c.name == normalize ·))
  | none => some ((visibleCookies jar site now).filter fun c => name.all (c.name == normalize ·))

/-! ## Change events -/

/-- What a change of the jar from `before` to `after` shows a document (cookie-store §6,
"process cookie changes"): the cookies it reads after that it did not read before with that
value (`changed`), and those it read before of a name, host and path it no longer reads
(`deleted`). Rewriting a cookie with its own value is no change. -/
def changes (before after : List Cookie) : List Cookie × List Cookie :=
  (after.filter fun c => !before.any fun b => sameKey b c && b.value == c.value,
   before.filter fun b => !after.any (sameKey b ·))

/-- The answer of a write: `ok`, then `+ name value` for each changed cookie and `- name` for
each deleted one, as the document at `site` sees them. -/
def written (old new : Jar) (site : Site) (now : Nat) : List ByteArray :=
  let (ch, de) := changes (visibleCookies old site now) (visibleCookies new site now)
  "ok".toUTF8 :: (ch.flatMap fun c => ["+".toUTF8, c.name.toUTF8, c.value.toUTF8]) ++
    (de.flatMap fun c => ["-".toUTF8, c.name.toUTF8])

/-! ## The command -/

abbrev Tok := ByteArray
def S (x : String) : Tok := x.toUTF8
def strAt (a : Array Tok) (i : Nat) : String := (String.fromUTF8? (a.getD i ByteArray.empty)).getD ""
def opt (a : Array Tok) (flag i : Nat) : Option String := if strAt a flag == "1" then some (strAt a i) else none
def typeError : List Tok := [S "!TypeError"]

/-- One command (`web_api` op 204) for the page of `origin` (`secure`: whether it is a secure
context); the jar after it and the answer. -/
def op (jar : Jar) (origin : String) (secure : Bool) (a : Array Tok) : Jar × List Tok :=
  let docUrl := strAt a 1
  let now := secondsOf (strAt a 2)
  match siteOf origin secure (pathOfUrl docUrl) with
  | none => (jar, typeError)
  | some site =>
    match strAt a 0 with
    | "get" | "getAll" =>
      let url := if strAt a 5 == "" then none else some (strAt a 5)
      match read jar site now docUrl (opt a 3 4) url with
      | none => (jar, typeError)
      | some cs => (jar, S "ok" :: cs.flatMap fun c => [S c.name, S c.value])
    | "set" =>
      let expires := if strAt a 9 == "" then none else some (secondsOf (strAt a 9))
      match set jar site now (strAt a 3) (strAt a 4) (opt a 5 6) (opt a 7 8) expires with
      | none => (jar, typeError)
      | some j => (j, written jar j site now)
    | "delete" =>
      match delete jar site now (strAt a 3) (opt a 4 5) (opt a 6 7) with
      | none => (jar, typeError)
      | some j => (j, written jar j site now)
    | _ => (jar, [S "!NotSupportedError"])

/-! ## Theorems -/

/-- Kind: privacy invariant (write side). Says: after `cookieStore.set`, every cookie in the
jar was there before or is for the host of the page that set it and is not `HttpOnly`: the
cookie store never adds a cookie for another host. -/
theorem store_keeps (jar : Jar) (now : Nat) (n : Cookie) (c : Cookie) (h : c ∈ (store jar now n).cookies) :
    c ∈ jar.cookies ∨ c.name = n.name ∧ c.host = n.host ∧ c.httpOnly = n.httpOnly := by
  unfold store at h
  have old : ∀ x, x ∈ jar.cookies.filter (fun o => !sameKey o n && !expired o now) → x ∈ jar.cookies :=
    fun x hx => (List.mem_filter.mp hx).1
  split at h
  · exact .inl h
  · simp only at h
    split at h
    · exact .inl (old c h)
    · rcases List.mem_append.mp h with hk | hk
      · split at hk
        · exact .inl (old c (List.mem_of_mem_drop hk))
        · exact .inl (old c hk)
      · simp only [List.mem_singleton] at hk
        rw [hk]; exact .inr ⟨rfl, rfl, rfl⟩

theorem set_keeps_host (jar j : Jar) (site : Site) (now : Nat) (name value : String) (domain path : Option String)
    (expires : Option Nat) (h : set jar site now name value domain path expires = some j) (c : Cookie) (hc : c ∈ j.cookies) :
    c ∈ jar.cookies ∨ (c.host = site.host ∧ c.httpOnly = false) := by
  unfold set at h
  simp only at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · rename_i n hn
      simp only [Option.some.injEq] at h
      subst h
      rcases store_keeps jar now n c hc with h1 | ⟨_, h2, h3⟩
      · exact .inl h1
      · have := admit_keeps_host _ _ _ _ _ _ hn
        exact .inr ⟨h2.trans this.1, h3.trans this.2.1⟩

/-- Kind: privacy invariant (read side). Says: every cookie that `get` or `getAll` answers is
for the host of the page's own origin and is not `HttpOnly`. -/
theorem read_host (jar : Jar) (site : Site) (now : Nat) (docUrl : String) (name url : Option String)
    (cs : List Cookie) (h : read jar site now docUrl name url = some cs) (c : Cookie) (hc : c ∈ cs) :
    c.host = site.host ∧ c.httpOnly = false := by
  unfold read at h
  split at h
  · split at h
    · simp at h
    · simp only [Option.some.injEq] at h
      subst h
      have hv := (List.mem_filter.mp hc).1
      have h1 := visible_host _ _ _ _ hv
      exact ⟨h1, visible_not_httpOnly _ _ _ _ hv⟩
  · simp only [Option.some.injEq] at h
    subst h
    have hv := (List.mem_filter.mp hc).1
    exact ⟨visible_host _ _ _ _ hv, visible_not_httpOnly _ _ _ _ hv⟩

/-- Kind: privacy invariant. Says: a change event lists only cookies the document reads
(before or after the change): the cookies of its own host, never `HttpOnly` ones. -/
theorem changes_sub (before after : List Cookie) :
    (∀ c ∈ (changes before after).1, c ∈ after) ∧ (∀ c ∈ (changes before after).2, c ∈ before) :=
  ⟨fun _ h => (List.mem_filter.mp h).1, fun _ h => (List.mem_filter.mp h).1⟩

/-- Kind: validity rule. Says: a name holding `=` is never set. -/
theorem set_refuses_eq (jar : Jar) (site : Site) (now : Nat) (name value : String) (domain path : Option String)
    (expires : Option Nat) (h : (normalize name).toList.contains '=' = true) :
    set jar site now name value domain path expires = none := by
  have h' : '=' ∈ (normalize name).toList := by simpa using h
  simp [set, nameValueOk, h']

/-! ## Checks (WPT cookiestore: set, get, getAll, delete arguments; special names) -/

private def T (xs : List String) : Array Tok := (xs.map String.toUTF8).toArray
private def shown (r : List Tok) : String := " ".intercalate (r.map fun t => (String.fromUTF8? t).getD "?")
private def run (cmds : List (List String)) : List String :=
  (cmds.foldl (fun (acc : Jar × List String) c =>
    let (j, r) := op acc.1 "https://web-platform.test:8443" true (T c); (j, acc.2 ++ [shown r])) ({}, [])).2

private def U : String := "https://web-platform.test:8443/cookiestore/t.html"
private def setC (n v : String) (dom path exp : Option String := none) : List String :=
  ["set", U, "1700000000000", n, v, if dom.isSome then "1" else "0", dom.getD "", if path.isSome then "1" else "0",
   path.getD "", exp.getD ""]
private def getC (n : String) (url : String := "") : List String := ["get", U, "1700000000000", "1", n, url]

#guard run [setC "cookie-name" "cookie-value", getC "cookie-name", getC " cookie-name \t"] ==
  ["ok + cookie-name cookie-value", "ok cookie-name cookie-value", "ok cookie-name cookie-value"]
#guard run [setC "" "", setC "" "suspicious-value=resembles-name-and-value", setC "a=b" "v", setC "cookie;name" "v",
  setC "n" "cookie\u0001value", setC "   " "   ", setC "__Http-cookie-name" "v", setC "  __Host-Http-x" "v",
  setC "" "__Host-nameless-cookie", setC "cookie-name\r1" "v"] ==
  ["!TypeError", "!TypeError", "!TypeError", "!TypeError", "!TypeError", "!TypeError", "!TypeError", "!TypeError",
   "!TypeError", "!TypeError"]
#guard run [setC "n" "v" (dom := some ".web-platform.test"), setC "n" "v" (dom := some "example.com"),
  setC "n" "v" (dom := some "sub.web-platform.test"), setC "n" "v" (dom := some "platform.test"),
  setC "n" "v" (dom := some "web-platform.test"), getC "n"] ==
  ["!TypeError", "!TypeError", "!TypeError", "!TypeError", "ok + n v", "ok n v"]
-- expires in the past: nothing is stored; in the future: kept
#guard run [setC "n" "v" (exp := some "1000"), getC "n", setC "n" "v" (exp := some "2000000000000"), getC "n"] ==
  ["ok", "ok", "ok + n v", "ok n v"]
-- path: must start with "/"; a subdirectory's cookie is not read here; no "/" is appended
#guard run [setC "n" "v" (path := some "cookiestore"), setC "n" "v" (path := some "/cookiestore/sub/"), getC "n",
  setC "n" "w" (path := some "/cookiestore/"), getC "n", setC "m" "v" (path := some "/cookiestore"), getC "m"] ==
  ["!TypeError", "ok", "ok", "ok + n w", "ok n w", "ok + m v", "ok m v"]
-- __Host-: no domain, path "/" only; __Secure-: fine on a secure page
#guard run [setC "__Host-c" "v" (dom := some "web-platform.test"), setC "__Host-c" "v" (path := some "/path"),
  setC "__Host-c" "v" (path := some "/"), getC "__Host-c", setC "__Secure-c" "v", getC "__Secure-c"] ==
  ["!TypeError", "!TypeError", "ok + __Host-c v", "ok __Host-c v", "ok + __Secure-c v", "ok __Secure-c v"]
-- delete: by name and path; an empty name is fine
#guard run [setC "n" "v", ["delete", U, "1700000000000", " n\t", "0", "", "0", ""], getC "n",
  ["delete", U, "1700000000000", "", "0", "", "0", ""], ["delete", U, "1700000000000", "n", "1", ".x", "0", ""]] ==
  ["ok + n v", "ok - n", "ok", "ok", "!TypeError"]
-- change events: rewriting a value is a change, rewriting the same value is none
#guard run [setC "n" "v", setC "n" "v", setC "n" "w", setC "a" "1" (exp := some "1000")] == ["ok + n v", "ok", "ok + n w", "ok"]
-- url option: the document's URL (a fragment aside), else TypeError
#guard run [setC "n" "v", getC "n" (U ++ "#foo"), getC "n" "https://web-platform.test:8443/different/path",
  getC "n" "https://www.example.com/cookiestore/t.html"] ==
  ["ok + n v", "ok n v", "!TypeError", "!TypeError"]
-- getAll order and document.cookie interplay: one jar
#guard (let j := setFromScript {} { host := "web-platform.test", path := "/cookiestore/t.html", secure := true } 1700000000
          "dc=1; path=/";
        (op j "https://web-platform.test:8443" true (T (getC "dc"))).2.map fun t => (String.fromUTF8? t).getD "") == ["ok", "dc", "1"]

end L4Factoidal.ClientStorage.CookieStore
