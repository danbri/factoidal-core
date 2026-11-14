/-
L4Factoidal.Net.ReferrerPolicy — the referrer of a request (Referrer Policy,
https://w3c.github.io/webappsec-referrer-policy/): §3 the policies, §8.3 "determine
request's referrer", §8.4 "strip url for use as a referrer".

## Status

The engine sends no `Referer` at all: a page cannot set one (`Net.PageFetch`:
`forbiddenRequestHeader`, `plan_wire_forbidden`) and the engine adds none, which every
policy allows (§8.3: a user agent may send less). This module is the computation for the day
it sends one, with what it may then send proved now, so that the privacy bound is a theorem
before the feature exists: `determine` is not called by any host.

## What is proved

For every policy, source and target: the referrer is nothing, the source's origin, or the
source URL without credentials and fragment (`determine_cases`); it never carries a user name,
a password or a fragment (`determine_no_credentials`); under the default policy
(`strict-origin-when-cross-origin`) a cross-origin request gets no path and no query
(`strict_cross_origin_no_path`), and a request from a trustworthy origin to one that is not
gets nothing (`strict_downgrade_none`, also for `strict-origin` and
`no-referrer-when-downgrade`); `no-referrer` sends nothing; `same-origin` sends nothing
across origins.
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

end L4Factoidal.Net.ReferrerPolicy
