/-
L4Factoidal.Net.ServiceWorkerScope — the URL decisions of Service Workers
(https://w3c.github.io/ServiceWorker/): §3.4.3 `register()` with "Start Register" (§8.2),
the checks of "Register" (§8.3) and "Update" (§8.4) that depend on URLs only, and "Match
Service Worker Registration" (§8.13).

## Decisions

* A script URL and a scope URL are `http` or `https` and their paths name no encoded `/` or
  `\` (`%2f`, `%5c`, any case); the script's fragment and the scope's query and fragment
  are dropped. A scope that is not given is the script's directory (`./` against it).
* The script's origin is potentially trustworthy (Secure Contexts §3.1), and the script and
  the scope are of the registering document's origin: otherwise `SecurityError`.
* The scope lies within the script's directory (the "max scope" of §8.4 step 9 when the
  response has no `Service-Worker-Allowed` field). The engine does not widen it from that
  field: a registration it names is refused, the safe direction.
* A client URL matches the registration with the longest scope that is a prefix of it
  (§8.13): a page is never matched by a scope that is not a prefix of its URL.
* Registrations live in the page session's memory only; none is written to disk, and the
  worker has no `fetch` event: requests are never routed through a service worker.

## What is proved

`startRegister_ok`: an accepted registration has an `http`/`https` script whose origin is
trustworthy, script and scope of the document's origin, and the scope within the script's
directory. `matchScope_prefix`, `matchScope_longest`, `matchScope_none`: matching picks a
listed scope that is a prefix of the client URL and no shorter than any other such scope,
and finds none only when no scope is a prefix.
-/
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.Net.PageFetch

namespace L4Factoidal.Net.ServiceWorkerScope
open L4Factoidal.WHATWG

/-- ASCII lower case of a character. -/
def lowerChar (c : Char) : Char := if 'A' ≤ c ∧ c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- Does `pat` occur in the characters `cs`. -/
def hasInfix (pat : List Char) : List Char → Bool
  | [] => pat.isEmpty
  | c :: cs => pat.isPrefixOf (c :: cs) || hasInfix pat cs

/-- A scheme a service worker's script or scope may have. -/
def httpScheme (s : String) : Bool := s == "http" || s == "https"

/-- A path with an encoded `/` or `\` (§8.2 steps 4 and 9). -/
def badPath (u : URL.Url) : Bool :=
  let p := u.pathname.toList.map lowerChar
  hasInfix "%2f".toList p || hasInfix "%5c".toList p

/-- The directory of a script URL's path: the path of `./` against it (§8.4 step 9). -/
def maxScopePath (script : URL.Url) : String :=
  ((URL.parseUrl "./" (some script.serialize)).map URL.Url.pathname).getD "/"

/-- The first reason to refuse a registration of `script` for `scope` by the document at
`client`, as an exception name and a message; `none` when there is none. -/
def firstError (client script scope : URL.Url) : Option (String × String) :=
  if !httpScheme script.scheme then
    some ("TypeError", s!"The URL protocol of the script ('{script.serialize}') is not supported.")
  else if badPath script then
    some ("TypeError", "The provided scriptURL includes a disallowed escape character.")
  else if !httpScheme scope.scheme then
    some ("TypeError", s!"The URL protocol of the scope ('{scope.serialize}') is not supported.")
  else if badPath scope then
    some ("TypeError", "The provided scope includes a disallowed escape character.")
  else if !PageFetch.trustworthyUrl script then
    some ("SecurityError", "The URL protocol of the current origin is not supported.")
  else if script.origin != client.origin then
    some ("SecurityError", s!"The origin of the provided scriptURL ('{script.origin}') does not match the current origin ('{client.origin}').")
  else if scope.origin != client.origin then
    some ("SecurityError", s!"The origin of the provided scope ('{scope.origin}') does not match the current origin ('{client.origin}').")
  else if !scope.pathname.startsWith (maxScopePath script) then
    some ("SecurityError", s!"The path of the provided scope ('{scope.pathname}') is not under the max scope allowed ('{maxScopePath script}').")
  else none

/-- The URLs of a registration (§8.2 steps 1 to 8): the script against the document's base
URL without its fragment, the scope (given, against the base URL; else the script's
directory) without query and fragment. -/
def scriptAndScope (base script : String) (scope : Option String) :
    Except (String × String) (URL.Url × URL.Url) :=
  match URL.parseUrl script (some base) with
  | none => .error ("TypeError", s!"The provided scriptURL ('{script}') is invalid.")
  | some s0 =>
    let s := { s0 with fragment := none }
    let sc0 := match scope with
      | none => URL.parseUrl "./" (some s.serialize)
      | some t => URL.parseUrl t (some base)
    match sc0 with
    | none => .error ("TypeError", s!"The provided scope ('{scope.getD ""}') is invalid.")
    | some sc => .ok (s, { sc with query := none, fragment := none })

/-- The document's URL with the script and scope URLs (`scriptAndScope`). -/
def parsed (base client script : String) (scope : Option String) :
    Except (String × String) (URL.Url × URL.Url × URL.Url) :=
  match URL.parseUrl client with
  | none => .error ("SecurityError", "The document's URL is not one a service worker may serve.")
  | some c =>
    match scriptAndScope base script scope with
    | .error e => .error e
    | .ok (s, sc) => .ok (c, s, sc)

/-- `register()` up to the fetch of the script: the script and scope URLs to register, or the
exception. -/
def startRegister (base client script : String) (scope : Option String) :
    Except (String × String) (URL.Url × URL.Url) :=
  match parsed base client script scope with
  | .error e => .error e
  | .ok (c, s, sc) =>
    match firstError c s sc with
    | some e => .error e
    | none => .ok (s, sc)

/-- One step of matching: keep the longer of the best so far and `s`, when `s` is a prefix
of the client URL. -/
def better (client : String) (best : Option String) (s : String) : Option String :=
  if client.startsWith s then
    match best with
    | none => some s
    | some b => if b.length < s.length then some s else some b
  else best

/-- "Match Service Worker Registration" (§8.13): of the scopes (serialized URLs), the longest
that is a prefix of the client URL. -/
def matchScope (client : String) (scopes : List String) : Option String :=
  scopes.foldl (better client) none

/-- A field of a `web_api` call as a string. -/
def strAt (fs : Array ByteArray) (i : Nat) : String :=
  (String.fromUTF8? (fs.getD i ByteArray.empty)).getD ""

/-- `web_api` 154, `register()` (fields: the document's base URL, its URL, the script URL,
"1" when a scope is given, the scope): `ok NUL script NUL scope`, or `err NUL name NUL
message`. 155, matching (fields: the client URL, then the scopes): the scope, or "". -/
def op (code : Nat) (fs : Array ByteArray) : Except Int ByteArray :=
  match code with
  | 154 =>
    let scope := if strAt fs 3 == "1" then some (strAt fs 4) else none
    match startRegister (strAt fs 0) (strAt fs 1) (strAt fs 2) scope with
    | .ok (s, sc) => .ok ("ok\u0000" ++ s.serialize ++ "\u0000" ++ sc.serialize).toUTF8
    | .error (n, m) => .ok ("err\u0000" ++ n ++ "\u0000" ++ m).toUTF8
  | 155 =>
    let scopes := ((List.range fs.size).drop 1).map (strAt fs)
    .ok ((matchScope (strAt fs 0) scopes).getD "").toUTF8
  | _ => .error (-2)

/-! ## Examples (WPT service-workers/service-worker/registration-*.https.html) -/

private def reg (script : String) (scope : Option String) : String :=
  match startRegister "https://web-platform.test:8443/service-workers/r/page.html"
      "https://web-platform.test:8443/service-workers/r/page.html" script scope with
  | .ok (s, sc) => s.serialize ++ " " ++ sc.serialize
  | .error (n, _) => n

#guard reg "w.js" none == "https://web-platform.test:8443/service-workers/r/w.js https://web-platform.test:8443/service-workers/r/"
#guard reg "w.js#frag" (some "sub/x?q#f") == "https://web-platform.test:8443/service-workers/r/w.js https://web-platform.test:8443/service-workers/r/sub/x"
#guard reg "a/w.js" (some "./") == "SecurityError"
#guard reg "w.js" (some "/") == "SecurityError"
#guard reg "https://www.web-platform.test:8443/w.js" none == "SecurityError"
#guard reg "w.js" (some "https://www.web-platform.test:8443/service-workers/r/") == "SecurityError"
#guard reg "data:text/javascript,1" none == "TypeError"
#guard reg "w.js" (some "filesystem:x") == "TypeError"
#guard reg "a%2fb.js" none == "TypeError"
#guard reg "w.js" (some "sub%5Cx") == "TypeError"
#guard reg "http://[" none == "TypeError"
#guard (match startRegister "http://web-platform.test:8000/r/p.html" "http://web-platform.test:8000/r/p.html" "w.js" none with
  | .error (n, _) => n | .ok _ => "ok") == "SecurityError"
#guard (match startRegister "http://localhost:8000/r/p.html" "http://localhost:8000/r/p.html" "w.js" none with
  | .error (n, _) => n | .ok _ => "ok") == "ok"
#guard matchScope "https://a.test/s/x/page.html" ["https://a.test/s/", "https://a.test/s/x/", "https://a.test/t/"] == some "https://a.test/s/x/"
#guard matchScope "https://a.test/s/x/page.html" ["https://a.test/s/x/", "https://a.test/s/"] == some "https://a.test/s/x/"
#guard matchScope "https://a.test/u" ["https://a.test/s/"] == none

/-! ## Theorems -/

/-- Kind: lemma. Says: when no reason to refuse is found, the script is `http`/`https`, its
origin is potentially trustworthy, script and scope are of the client's origin and the
scope lies within the script's directory. -/
theorem firstError_none (c s sc : URL.Url) (h : firstError c s sc = none) :
    httpScheme s.scheme = true ∧ httpScheme sc.scheme = true ∧ badPath s = false ∧ badPath sc = false ∧
      PageFetch.trustworthyUrl s = true ∧ s.origin = c.origin ∧ sc.origin = c.origin ∧
      sc.pathname.startsWith (maxScopePath s) = true := by
  unfold firstError at h
  split at h; · simp at h
  rename_i h1
  split at h; · simp at h
  rename_i h2
  split at h; · simp at h
  rename_i h3
  split at h; · simp at h
  rename_i h4
  split at h; · simp at h
  rename_i h5
  split at h; · simp at h
  rename_i h6
  split at h; · simp at h
  rename_i h7
  split at h; · simp at h
  rename_i h8
  simp only [Bool.not_eq_true', Bool.eq_false_iff, ne_eq] at h1 h2 h3 h4 h5 h6 h7 h8
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa using h1
  · simpa using h3
  · simpa using h2
  · simpa using h4
  · simpa using h5
  · simpa using h6
  · simpa using h7
  · simpa using h8

/-- Kind: security theorem (registration). Says: `register()` accepts a script and a scope
only when the script is `http`/`https` with a potentially trustworthy origin, script and
scope are both of the registering document's origin, neither path names an encoded slash,
and the scope lies within the script's directory. Does not say: that the script's response
is JavaScript (the worker's fetch checks that). -/
theorem startRegister_ok (base client script : String) (scope : Option String) (s sc : URL.Url)
    (h : startRegister base client script scope = .ok (s, sc)) :
    ∃ c, URL.parseUrl client = some c ∧ httpScheme s.scheme = true ∧ httpScheme sc.scheme = true ∧
      badPath s = false ∧ badPath sc = false ∧ PageFetch.trustworthyUrl s = true ∧
      s.origin = c.origin ∧ sc.origin = c.origin ∧ sc.pathname.startsWith (maxScopePath s) = true := by
  unfold startRegister at h
  split at h
  · simp at h
  · rename_i c s' sc' hp
    split at h
    · simp at h
    · rename_i hf
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨c, ?_, firstError_none c s' sc' hf⟩
      unfold parsed at hp
      split at hp
      · simp at hp
      · rename_i c' hc
        split at hp
        · simp at hp
        · simp only [Except.ok.injEq, Prod.mk.injEq] at hp
          rw [← hp.1]; exact hc

/-- The invariant of matching over the scopes seen so far: the best is one of them and a
prefix of the client URL, and every prefix among them is no longer than the best. -/
def Inv (client : String) (seen : List String) (best : Option String) : Prop :=
  (∀ b, best = some b → b ∈ seen ∧ client.startsWith b = true) ∧
  (∀ t ∈ seen, client.startsWith t = true → ∃ b, best = some b ∧ t.length ≤ b.length)

theorem inv_step (client : String) (seen : List String) (best : Option String) (s : String)
    (h : Inv client seen best) : Inv client (seen ++ [s]) (better client best s) := by
  obtain ⟨h1, h2⟩ := h
  unfold better
  by_cases hs : client.startsWith s = true
  · simp only [hs, if_true]
    cases best with
    | none =>
      refine ⟨fun b hb => ?_, fun t ht hp => ?_⟩
      · simp only [Option.some.injEq] at hb; subst hb; exact ⟨by simp, hs⟩
      · rcases List.mem_append.mp ht with ht | ht
        · obtain ⟨b, hb, -⟩ := h2 t ht hp; simp at hb
        · simp only [List.mem_singleton] at ht; subst ht; exact ⟨t, rfl, Nat.le_refl _⟩
    | some b0 =>
      by_cases hl : b0.length < s.length
      · simp only [hl, if_true]
        refine ⟨fun b hb => ?_, fun t ht hp => ?_⟩
        · simp only [Option.some.injEq] at hb; subst hb; exact ⟨by simp, hs⟩
        · rcases List.mem_append.mp ht with ht | ht
          · obtain ⟨b, hb, hle⟩ := h2 t ht hp
            simp only [Option.some.injEq] at hb; subst hb
            exact ⟨s, rfl, Nat.le_of_lt (Nat.lt_of_le_of_lt hle hl)⟩
          · simp only [List.mem_singleton] at ht; subst ht; exact ⟨t, rfl, Nat.le_refl _⟩
      · simp only [hl, if_false]
        refine ⟨fun b hb => ?_, fun t ht hp => ?_⟩
        · obtain ⟨hm, hp'⟩ := h1 b hb; exact ⟨List.mem_append_left _ hm, hp'⟩
        · rcases List.mem_append.mp ht with ht | ht
          · exact h2 t ht hp
          · simp only [List.mem_singleton] at ht; subst ht
            exact ⟨b0, rfl, Nat.le_of_not_lt hl⟩
  · simp only [hs, if_false, Bool.false_eq_true]
    refine ⟨fun b hb => ?_, fun t ht hp => ?_⟩
    · obtain ⟨hm, hp'⟩ := h1 b hb; exact ⟨List.mem_append_left _ hm, hp'⟩
    · rcases List.mem_append.mp ht with ht | ht
      · exact h2 t ht hp
      · simp only [List.mem_singleton] at ht; subst ht; exact absurd hp hs

theorem inv_foldl (client : String) (rest seen : List String) (best : Option String)
    (h : Inv client seen best) : Inv client (seen ++ rest) (rest.foldl (better client) best) := by
  induction rest generalizing seen best with
  | nil => simpa using h
  | cons s rest ih =>
    have := ih (seen ++ [s]) (better client best s) (inv_step client seen best s h)
    simpa [List.foldl] using this

theorem inv_matchScope (client : String) (scopes : List String) :
    Inv client scopes (matchScope client scopes) := by
  have h0 : Inv client [] none := ⟨fun b hb => by simp at hb, fun t ht => by simp at ht⟩
  have := inv_foldl client scopes [] none h0
  rw [List.nil_append] at this
  exact this

/-- Kind: security theorem (matching). Says: the registration a client URL matches has a
scope that is one of the registered scopes and a prefix of the client URL. -/
theorem matchScope_prefix (client : String) (scopes : List String) (s : String)
    (h : matchScope client scopes = some s) : s ∈ scopes ∧ client.startsWith s = true :=
  (inv_matchScope client scopes).1 s h

/-- Kind: correctness theorem (matching). Says: no registered scope that is a prefix of the
client URL is longer than the one matched. -/
theorem matchScope_longest (client : String) (scopes : List String) (s : String)
    (h : matchScope client scopes = some s) (t : String) (ht : t ∈ scopes)
    (hp : client.startsWith t = true) : t.length ≤ s.length := by
  obtain ⟨b, hb, hle⟩ := (inv_matchScope client scopes).2 t ht hp
  rw [h] at hb
  simp only [Option.some.injEq] at hb
  subst hb; exact hle

/-- Kind: correctness theorem (matching). Says: no registration is matched only when no
registered scope is a prefix of the client URL. -/
theorem matchScope_none (client : String) (scopes : List String)
    (h : matchScope client scopes = none) (t : String) (ht : t ∈ scopes) : client.startsWith t = false := by
  cases hp : client.startsWith t
  · rfl
  · obtain ⟨b, hb, -⟩ := (inv_matchScope client scopes).2 t ht hp
    rw [h] at hb; simp at hb

end L4Factoidal.Net.ServiceWorkerScope
