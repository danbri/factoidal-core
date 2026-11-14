/-
L4Factoidal.Net.ReferrerPolicy — the referrer of a request (Referrer Policy,
https://w3c.github.io/webappsec-referrer-policy/): §3 the policies, §8.3 "determine
request's referrer", §8.4 "strip url for use as a referrer".

## Status

`Net.PageFetch` sends a `Referer` with the requests of `fetch` and `XMLHttpRequest`
(`PageFetch.referrerOf`, on the table `decide` of this file; `PageFetch.wire_referer` says
every `Referer` on a wire is that function's value). The policy is the request's, else its
document's or worker's (`ofHeader` for a `Referrer-Policy` response field, `ofMeta` for
`<meta name=referrer>`, `ofAttribute` for a `referrerpolicy` attribute), else the default.
A page still cannot set the field itself (`forbiddenRequestHeader`).

## What is proved

For every policy, source and target: the referrer is nothing, the source's origin, or the
source URL without credentials and fragment (`determine_cases`); it never carries a user name,
a password or a fragment (`determine_no_credentials`); under the default policy
(`strict-origin-when-cross-origin`) a cross-origin request gets no path and no query
(`strict_cross_origin_no_path`), and a request from a trustworthy origin to one that is not
gets nothing (`strict_downgrade_none`, also for `strict-origin` and
`no-referrer-when-downgrade`); `no-referrer` sends nothing; `same-origin` sends nothing
across origins. `determine` is the table `decide` applied to a source (`determine_decide`),
and a referrer made from a referrer (a redirect: Fetch §4.1 step 8 runs again on the
referrer the hop before carried) is still nothing, the first source's origin or the first
source stripped (`determine_chain`): a redirect never widens what is sent.
-/

namespace L4Factoidal.Net.ReferrerPolicy

/-- The parts of a URL that a referrer is made of. -/
structure Url where
  scheme : String
  host : String
  port : Option Nat := none
  path : String := "/"
  query : Option String := none
  fragment : Option String := none
  username : String := ""
  password : String := ""
  deriving DecidableEq, Repr, Inhabited

/-- Same origin: scheme, host and port (URL §4.5 for tuple origins). -/
def sameOrigin (a b : Url) : Bool := a.scheme == b.scheme && a.host == b.host && a.port == b.port

/-- A potentially trustworthy origin, as far as the scheme and host say (Secure Contexts
§3.1): `https`, `wss`, or a loopback host. It is a function of the origin only. -/
def trustworthy (u : Url) : Bool :=
  u.scheme == "https" || u.scheme == "wss" || u.host == "localhost" || u.host == "127.0.0.1" || u.host == "[::1]"

/-- A local scheme (Fetch §2.5): such a URL is never a referrer. -/
def localScheme (u : Url) : Bool := u.scheme == "about" || u.scheme == "blob" || u.scheme == "data"

/-- The referrer policies (§3); the empty string is `default`. -/
inductive Policy where
  | noReferrer | noReferrerWhenDowngrade | sameOrigin | origin | strictOrigin
  | originWhenCrossOrigin | strictOriginWhenCrossOrigin | unsafeUrl
  deriving DecidableEq, Repr, Inhabited

/-- A policy token (§3; `none` for a token that is not one, which leaves the policy as it was). -/
def Policy.ofToken (t : String) : Option Policy :=
  match t with
  | "no-referrer" => some .noReferrer
  | "no-referrer-when-downgrade" => some .noReferrerWhenDowngrade
  | "same-origin" => some .sameOrigin
  | "origin" => some .origin
  | "strict-origin" => some .strictOrigin
  | "origin-when-cross-origin" => some .originWhenCrossOrigin
  | "strict-origin-when-cross-origin" => some .strictOriginWhenCrossOrigin
  | "unsafe-url" => some .unsafeUrl
  | _ => none

/-- The default referrer policy (§3). -/
def Policy.default : Policy := .strictOriginWhenCrossOrigin

/-- §8.4 "strip url for use as a referrer": no credentials, no fragment; with `originOnly`
also no path and no query. -/
def strip (u : Url) (originOnly : Bool) : Url :=
  if originOnly then { u with username := "", password := "", fragment := none, path := "/", query := none }
  else { u with username := "", password := "", fragment := none }

/-- The request goes from a trustworthy origin to one that is not (a "downgrade"). -/
def downgrade (source target : Url) : Bool := trustworthy source && !trustworthy target

/-- §8.3 "determine request's referrer" for a request of a context whose URL is `source` to
`target`, under `policy`; `none` is "no referrer". `long`: the stripped source URL is
longer than 4096 characters as serialized (step 6: then only the origin is sent). -/
def determine (policy : Policy) (source target : Url) (long : Bool := false) : Option Url :=
  if localScheme source then none else
  let origin := strip source true
  let full := if long then origin else strip source false
  match policy with
  | .noReferrer => none
  | .origin => some origin
  | .unsafeUrl => some full
  | .strictOrigin => if downgrade source target then none else some origin
  | .strictOriginWhenCrossOrigin =>
    if sameOrigin source target then some full
    else if downgrade source target then none else some origin
  | .sameOrigin => if sameOrigin source target then some full else none
  | .originWhenCrossOrigin => if sameOrigin source target then some full else some origin
  | .noReferrerWhenDowngrade => if downgrade source target then none else some full

/-- What of its source a referrer carries. -/
inductive Sent where
  | nothing
  /-- The origin only: no path, no query. -/
  | origin
  /-- The source without credentials and fragment. -/
  | full
  deriving DecidableEq, Repr, Inhabited

/-- §8.3 steps 8 and on as a table: what a policy lets a request carry, from whether its
source and target are same-origin (`same`) and whether it is a downgrade (`down`). Every
caller that makes a `Referer` (`Net.PageFetch.referrerOf`) reads this table. -/
def decide (policy : Policy) (same down : Bool) : Sent :=
  match policy with
  | .noReferrer => .nothing
  | .origin => .origin
  | .unsafeUrl => .full
  | .strictOrigin => if down then .nothing else .origin
  | .strictOriginWhenCrossOrigin => if same then .full else if down then .nothing else .origin
  | .sameOrigin => if same then .full else .nothing
  | .originWhenCrossOrigin => if same then .full else .origin
  | .noReferrerWhenDowngrade => if down then .nothing else .full

/-- ASCII lower case. -/
def lowerAscii (s : String) : String :=
  s.map fun c => if 'A' ≤ c ∧ c ≤ 'Z' then Char.ofNat (c.toNat + 32) else c

/-- §8.1 "parse a referrer policy from a `Referrer-Policy` header": the last token of the
field's values (joined with commas by the caller) that is a policy; unknown tokens and the
empty string are skipped, so a newer policy a server lists last wins only when it is known. -/
def Policy.ofHeader (value : String) : Option Policy :=
  ((value.splitOn ",").map fun t => Policy.ofToken (lowerAscii t.trimAscii.toString)).foldl
    (fun acc p => match p with | some q => some q | none => acc) none

/-- A `referrerpolicy` content attribute (HTML §2.3.3 enumerated attribute over the policies:
ASCII case-insensitive, no legacy keywords; a value that is not a policy is the empty state). -/
def Policy.ofAttribute (value : String) : Option Policy := Policy.ofToken (lowerAscii value)

/-- `<meta name=referrer content=…>` (HTML §4.2.5.1): the content in ASCII lower case, with
the four legacy keywords. `none`: the document's policy stays as it was. -/
def Policy.ofMeta (content : String) : Option Policy :=
  match lowerAscii content.trimAscii.toString with
  | "never" => some .noReferrer
  | "default" => some .strictOriginWhenCrossOrigin
  | "always" => some .unsafeUrl
  | "origin-when-crossorigin" => some .originWhenCrossOrigin
  | v => Policy.ofToken v

/-- The token of a policy (the value `Request.referrerPolicy` shows). -/
def Policy.token : Policy → String
  | .noReferrer => "no-referrer"
  | .noReferrerWhenDowngrade => "no-referrer-when-downgrade"
  | .sameOrigin => "same-origin"
  | .origin => "origin"
  | .strictOrigin => "strict-origin"
  | .originWhenCrossOrigin => "origin-when-cross-origin"
  | .strictOriginWhenCrossOrigin => "strict-origin-when-cross-origin"
  | .unsafeUrl => "unsafe-url"

/-! ## Theorems -/

/-- Kind: privacy bound. Says: whatever the policy, the referrer is nothing, the source's
origin (no path, no query), or the source URL stripped of credentials and fragment: nothing
else of the source or of anything else is ever sent. -/
theorem determine_cases (p : Policy) (s t : Url) (long : Bool) :
    determine p s t long = none ∨ determine p s t long = some (strip s true) ∨
      determine p s t long = some (strip s false) := by
  cases hl : localScheme s
  · cases hs : sameOrigin s t <;> cases hd : downgrade s t <;> cases p <;> cases long <;>
      simp [determine, hl, hs, hd]
  · simp [determine, hl]

/-- Kind: privacy invariant. Says: a referrer never has a user name, a password or a
fragment, under any policy. -/
theorem determine_no_credentials (p : Policy) (s t r : Url) (long : Bool)
    (h : determine p s t long = some r) : r.username = "" ∧ r.password = "" ∧ r.fragment = none := by
  rcases determine_cases p s t long with h' | h' | h' <;> rw [h'] at h
  · simp at h
  · simp only [Option.some.injEq] at h
    rw [← h]
    simp [strip]
  · simp only [Option.some.injEq] at h
    rw [← h]
    simp [strip]

/-- Kind: privacy theorem (the default policy). Says: under
`strict-origin-when-cross-origin`, a request to another origin gets at most the source's
origin: no path and no query of the page that asks. Does not say: anything of same-origin
requests (they get the stripped URL). -/
theorem strict_cross_origin_no_path (s t r : Url) (long : Bool) (hc : sameOrigin s t = false)
    (h : determine .strictOriginWhenCrossOrigin s t long = some r) : r.path = "/" ∧ r.query = none := by
  cases hl : localScheme s
  · cases hd : downgrade s t <;> simp [determine, hl, hc, hd] at h
    rw [← h]
    simp [strip]
  · simp [determine, hl] at h

/-- Kind: lemma. Says: a downgrade is a cross-origin request (trust is the origin's). -/
theorem downgrade_cross_origin (s t : Url) (h : downgrade s t = true) : sameOrigin s t = false := by
  unfold downgrade trustworthy at h
  unfold sameOrigin
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_eq_eq_not, Bool.not_true, Bool.or_eq_false_iff,
    beq_eq_false_iff_ne] at h
  cases hs : s.scheme == t.scheme <;> cases hh : s.host == t.host <;> simp
  rw [beq_iff_eq] at hs hh
  rcases h with ⟨h1, ⟨⟨⟨⟨h2, h3⟩, h4⟩, h5⟩, h6⟩⟩
  rw [hs, hh] at h1
  simp_all

/-- Kind: privacy theorem (downgrade). Says: under `strict-origin`,
`strict-origin-when-cross-origin` and `no-referrer-when-downgrade`, a request from a
trustworthy origin to one that is not gets no referrer at all. -/
theorem strict_downgrade_none (p : Policy) (s t : Url) (long : Bool) (hd : downgrade s t = true)
    (hp : p = .strictOrigin ∨ p = .strictOriginWhenCrossOrigin ∨ p = .noReferrerWhenDowngrade) :
    determine p s t long = none := by
  have hc := downgrade_cross_origin s t hd
  cases hl : localScheme s <;> rcases hp with hp | hp | hp <;> subst hp <;> simp [determine, hl, hd, hc]

/-- Kind: privacy theorem. Says: `no-referrer` sends nothing. -/
theorem noReferrer_none (s t : Url) (long : Bool) : determine .noReferrer s t long = none := by
  cases hl : localScheme s <;> simp [determine, hl]

/-- Kind: privacy theorem. Says: `same-origin` sends nothing to another origin. -/
theorem sameOrigin_cross_none (s t : Url) (long : Bool) (hc : sameOrigin s t = false) :
    determine .sameOrigin s t long = none := by
  cases hl : localScheme s <;> simp [determine, hl, hc]

/-- Kind: refinement. Says: `determine` is the table `decide` applied to the source: nothing
for a local scheme; else nothing, the origin, or the stripped source (the origin when it is
too long) as the table says for same-origin and downgrade. -/
theorem determine_decide (p : Policy) (s t : Url) (long : Bool) :
    determine p s t long =
      if localScheme s then none else
      match decide p (sameOrigin s t) (downgrade s t) with
      | .nothing => none
      | .origin => some (strip s true)
      | .full => some (if long then strip s true else strip s false) := by
  cases hl : localScheme s <;> cases hs : sameOrigin s t <;> cases hd : downgrade s t <;> cases p <;>
    simp [determine, decide, hl, hs, hd]

/-- Kind: round trip. Says: a policy's token names that policy. -/
theorem ofToken_token (p : Policy) : Policy.ofToken p.token = some p := by
  cases p <;> rfl

/-- Kind: lemma. Says: stripping twice is stripping once to the narrower form. -/
theorem strip_strip (u : Url) (a b : Bool) : strip (strip u a) b = strip u (a || b) := by
  cases a <;> cases b <;> simp [strip]

/-- Kind: privacy theorem (redirects). Says: a referrer computed from a referrer (the next
hop of a redirect, under any policy, to any target) is nothing, the first source's origin,
or the first source stripped: a redirect never adds to what the first hop could carry, and
once only the origin was sent, the path and query are gone for the rest of the chain. -/
theorem determine_chain (p p' : Policy) (s t t' r : Url) (long long' : Bool)
    (h : determine p s t long = some r) :
    determine p' r t' long' = none ∨ determine p' r t' long' = some (strip s true) ∨
      (determine p' r t' long' = some (strip s false) ∧ r = strip s false) := by
  rcases determine_cases p' r t' long' with h' | h' | h'
  · exact Or.inl h'
  · rcases determine_cases p s t long with hs | hs | hs <;> rw [hs] at h
    · simp at h
    · simp only [Option.some.injEq] at h
      rw [h', ← h, strip_strip]
      exact Or.inr (Or.inl rfl)
    · simp only [Option.some.injEq] at h
      rw [h', ← h, strip_strip]
      exact Or.inr (Or.inl rfl)
  · rcases determine_cases p s t long with hs | hs | hs <;> rw [hs] at h
    · simp at h
    · simp only [Option.some.injEq] at h
      rw [h', ← h, strip_strip]
      exact Or.inr (Or.inl rfl)
    · simp only [Option.some.injEq] at h
      rw [h', ← h, strip_strip]
      exact Or.inr (Or.inr ⟨rfl, rfl⟩)

/-- Kind: privacy theorem (the table). Says: under the default policy the table gives the
full source only to the same origin, and nothing on a downgrade. -/
theorem decide_default (same down : Bool) :
    (decide .default same down = .full ↔ same = true) ∧
      (same = false → down = true → decide .default same down = .nothing) := by
  cases same <;> cases down <;> simp [decide, Policy.default]

/-! ## Checks (the cases of WPT referrer-policy/generic/test-case.sub.js) -/

private def page : Url :=
  { scheme := "https", host := "a.example", path := "/dir/page.html", query := some "q=1", fragment := some "f",
    username := "u", password := "p" }
private def same : Url := { scheme := "https", host := "a.example", path := "/x" }
private def cross : Url := { scheme := "https", host := "b.example", path := "/x" }
private def insecure : Url := { scheme := "http", host := "b.example", path := "/x" }
private def full : Url := { scheme := "https", host := "a.example", path := "/dir/page.html", query := some "q=1" }
private def originOnly : Url := { scheme := "https", host := "a.example" }

#guard determine .default page same == some full
#guard determine .default page cross == some originOnly
#guard determine .default page insecure == none
#guard determine .unsafeUrl page insecure == some full
#guard determine .origin page insecure == some originOnly
#guard determine .strictOrigin page cross == some originOnly && determine .strictOrigin page insecure == none
#guard determine .sameOrigin page same == some full && determine .sameOrigin page cross == none
#guard determine .originWhenCrossOrigin page same == some full && determine .originWhenCrossOrigin page insecure == some originOnly
#guard determine .noReferrerWhenDowngrade page cross == some full && determine .noReferrerWhenDowngrade page insecure == none
#guard determine .noReferrer page same == none
-- a URL over 4096 characters: the origin only, even to the same origin
#guard determine .unsafeUrl page same (long := true) == some originOnly
-- a local scheme is never a referrer
#guard determine .unsafeUrl { scheme := "data", host := "" } cross == none
#guard Policy.ofToken "origin" == some .origin && Policy.ofToken "Origin" == none && Policy.ofToken "" == none

-- the Referrer-Policy header: the last known token wins; unknown ones and "" are skipped
#guard Policy.ofHeader "no-referrer, origin" == some .origin
#guard Policy.ofHeader "origin, never-heard-of-it" == some .origin
#guard Policy.ofHeader "Unsafe-URL" == some .unsafeUrl && Policy.ofHeader "" == none && Policy.ofHeader "always" == none
-- meta: the legacy keywords; an attribute has none
#guard Policy.ofMeta " Always " == some .unsafeUrl && Policy.ofMeta "never" == some .noReferrer
#guard Policy.ofMeta "origin-when-crossorigin" == some .originWhenCrossOrigin && Policy.ofMeta "bogus" == none
#guard Policy.ofAttribute "ORIGIN" == some .origin && Policy.ofAttribute "always" == none
-- a redirect chain: origin only after a cross-origin hop, even back to the first origin
#guard (determine .originWhenCrossOrigin page cross).bind (determine .originWhenCrossOrigin · same) == some originOnly

end L4Factoidal.Net.ReferrerPolicy
