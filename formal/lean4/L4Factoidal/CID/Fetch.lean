/-
L4Factoidal.CID.Fetch — §3.3 Retrieve Verification Method of Controlled
Identifiers v1.0 (https://www.w3.org/TR/cid-1.0/) with the fetch of step 4
done by a host, under the private-address guard of the authorization server
and with the `Content-Type` of the answer checked
(https://github.com/danbri/factoidal/issues/1100, items 7 and 9).

## Who decides, who fetches

The engine does no I/O (iron rule 7). `step` is a pure function of what the
host has passed so far (`Request`). It answers one of:

  * `resolve host`: resolve this name and pass back every address;
  * `fetch url accept address`: GET this URL with this `Accept`, connecting
    to this address (`none`: the host cannot resolve names, see below);
  * `method m`: §3.3 returned `m`;
  * `failure f`: a §3.5 processing error, or a failure of step 4.

The host loop: call, do what is named, add the answer to the request, call
again. At most one resolution and one fetch.

## The guard (the authorization server's, `Authz/Fetch.lean`)

* The document URL is `https`, or `http` only with `allowHttp`.
* The address decision is `Authz.chooseAddress` on every address of the
  host: an IP literal is its own address, a `localhost` name (RFC 6761 §6.3)
  is loopback, a name has the addresses the host resolved. Unless
  `allowPrivateFetch`, a loopback, unspecified, link-local or private
  address refuses the fetch (`Authz.privateAddr`). The fetch answer names
  the address to connect to, so the host does not resolve the name again.
* A host that cannot resolve names (`resolver := false`: a browser page)
  gets `fetch url accept none` for a name. The guard then covers IP
  literals and `localhost` names only; the browser chooses the address.
  This is the one difference from the authorization server, which always
  resolves.
* The host does not follow redirects; a redirect is a status other than 200.

The guard is checked before a fetched document is read: a document the host
passes for a URL the guard refuses is never used (`step_method_sound`).

## The answer (item 7)

A document is read only when the status is 200 and the `Content-Type` is
one of `acceptedMediaTypes` (`application/cid`, Appendix A.1, and
`application/cid+json`, `application/ld+json`, `application/json`, which
the LWS suites use). No `Content-Type` is not accepted.

## In force (§2.2)

§3.3 does not read `expires` or `revoked`. When the request has `now`
(seconds since the epoch), a method that is not `methodInForce now` is a
failure: §2.2, "a verifier ... SHOULD NOT verify proofs ... at or after"
`expires`, and `revoked` "MUST NOT be used".

## Failures that are not §3.5 errors

§3.5 names no error for step 4 (the dereference) or for §2.2 expiry. Those
four failures have their own names and an RFC 9457 `type` that is a tag URI
(RFC 4151), so they are not mistaken for the `https://w3id.org/security#`
types of §3.5: `FETCH_REFUSED` (the guard), `FETCH_FAILED` (no answer, or
not 200), `UNSUPPORTED_MEDIA_TYPE`, `VERIFICATION_METHOD_NOT_IN_FORCE`.
-/
import L4Factoidal.CID.Retrieve
import L4Factoidal.Authz.Fetch

namespace L4Factoidal.CID.Fetch

open L4Factoidal.JSON
open L4Factoidal.CID
open L4Factoidal.LWS.InboxGuard (addr? authority? localhostName)
open L4Factoidal.Authz (FetchPolicy chooseAddress schemeOf privateAddr)

/-- What the host passed back for one GET. `status` 0: no answer. -/
structure Fetched where
  url : String
  status : Nat
  contentType : String
  body : String
  deriving Repr, DecidableEq

/-- Everything the engine knows: the call and what the host passed back. -/
structure Request where
  vm : String
  rel : Relationship
  now : Option Int := none
  allowHttp : Bool := false
  allowPrivateFetch : Bool := false
  /-- Can the host resolve names? -/
  resolver : Bool := true
  /-- Host name and every address the host resolved for it. -/
  resolved : List (String × List String) := []
  fetched : List Fetched := []
  deriving Repr

/-- Why there is no method. -/
inductive Failure where
  | processing (e : ProcessingError)
  | refused (url why : String)
  | fetchFailed (url : String) (status : Nat)
  | mediaType (url contentType : String)
  | notInForce (vm : String) (now : Int)
  deriving Repr, DecidableEq

/-- The answer of `step`. -/
inductive Step where
  | resolve (host : String)
  | fetch (url accept : String) (address : Option String)
  | method (m : Method)
  | failure (f : Failure)
  deriving Repr, DecidableEq

def Request.policy (q : Request) : FetchPolicy :=
  { allowHttp := q.allowHttp, allowPrivateFetch := q.allowPrivateFetch }

/-- Is the scheme of the document URL allowed? -/
def schemeAllowed (allowHttp : Bool) (url : String) : Bool :=
  let s := schemeOf url
  s == "https" || (s == "http" && allowHttp)

/-- The address decision for a host. `.error`: refused; `.ok none`: the
host must resolve the name; `.ok (some a)`: connect to `a` (`none` inside:
the host cannot resolve, the name is passed as it is). -/
def target (q : Request) (host : String) : Except String (Option (Option String)) :=
  let decide (texts : List String) : Except String (Option (Option String)) :=
    match chooseAddress q.policy host texts with
    | .error w => .error w
    | .ok a => .ok (some (some a))
  match addr? host with
  | some _ => decide [host]
  | none =>
      if localhostName host then decide ["127.0.0.1"]
      else match q.resolved.lookup host with
        | some texts => decide texts
        | none => if q.resolver then .ok none else .ok (some none)

/-- What the host passed back, read: status, `Content-Type`, §3.3 steps
5–12, then §2.2 with `now`. -/
def judge (q : Request) (f : Fetched) : Step :=
  if f.status != 200 then .failure (.fetchFailed f.url f.status)
  else if !mediaTypeAccepted f.contentType then .failure (.mediaType f.url f.contentType)
  else match retrieveFromText q.vm q.rel f.body with
    | .error e => .failure (.processing e)
    | .ok m =>
        match q.now with
        | some n => if methodInForce n m then .method m else .failure (.notInForce q.vm n)
        | none => .method m

/-- **One step of §3.3 with the host.** -/
def step (q : Request) : Step :=
  match documentUrlOf q.vm with
  | .error e => .failure (.processing e)
  | .ok (u, _) =>
      if !schemeAllowed q.allowHttp u then
        .failure (.refused u s!"{u} is not an https URL{if schemeOf u == "http" then " (http needs allowHttp)" else ""}")
      else match authority? u with
        | none => .failure (.refused u s!"{u} has no host")
        | some (host, _) =>
            match target q host with
            | .error w => .failure (.refused u w)
            | .ok none => .resolve host
            | .ok (some a) =>
                match q.fetched.find? (·.url == u) with
                | none => .fetch u acceptHeader a
                | some f => judge q f

/-! ## Names and RFC 9457 objects -/

def tagBase : String := "tag:danbri.github.io,2026:factoidal/cid#"

def Failure.code : Failure → String
  | .processing e => e.name
  | .refused _ _ => "FETCH_REFUSED"
  | .fetchFailed _ _ => "FETCH_FAILED"
  | .mediaType _ _ => "UNSUPPORTED_MEDIA_TYPE"
  | .notInForce _ _ => "VERIFICATION_METHOD_NOT_IN_FORCE"

/-- The RFC 9457 problem details object. -/
def Failure.problem : Failure → Json
  | .processing e => e.problem
  | .refused _ why => obj "The controlled identifier document may not be fetched" why "FETCH_REFUSED"
  | .fetchFailed u s =>
      obj "The controlled identifier document could not be retrieved"
        (if s == 0 then s!"GET {u} answered nothing" else s!"GET {u} answered {s}") "FETCH_FAILED"
  | .mediaType u ct =>
      obj "The controlled identifier document has an unsupported media type"
        s!"GET {u} answered Content-Type '{ct}', not one of {acceptHeader}" "UNSUPPORTED_MEDIA_TYPE"
  | .notInForce vm n =>
      obj "The verification method is not in force"
        s!"{vm} has expired or been revoked at or before {n} seconds since 1970-01-01T00:00:00Z"
        "VERIFICATION_METHOD_NOT_IN_FORCE"
where
  obj (title detail name : String) : Json :=
    .object [("type", .string (tagBase ++ name)), ("title", .string title), ("detail", .string detail)]

/-! ## Theorems -/

/-- A method is returned only from a document the host fetched from the
document URL of `vm`, with status 200 and an accepted `Content-Type`, that
§3.3 steps 5–12 accept; and only when the URL passed the scheme check. -/
theorem step_method_sound {q : Request} {m : Method} (h : step q = .method m) :
    ∃ u frag f, documentUrlOf q.vm = .ok (u, frag) ∧ schemeAllowed q.allowHttp u = true ∧
      f ∈ q.fetched ∧ f.url = u ∧ f.status = 200 ∧ mediaTypeAccepted f.contentType = true ∧
      retrieveFromText q.vm q.rel f.body = .ok m := by
  unfold step at h
  split at h
  · simp at h
  · rename_i u frag hu
    split at h
    · simp at h
    · rename_i hs
      split at h
      · simp at h
      · split at h
        · simp at h
        · simp at h
        · split at h
          · simp at h
          · rename_i f hf
            have hmem := List.mem_of_find?_eq_some hf
            have hurl : f.url = u := by simpa using List.find?_some hf
            unfold judge at h
            split at h
            · simp at h
            · rename_i hst
              split at h
              · simp at h
              · rename_i hct
                split at h
                · simp at h
                · rename_i m' hr
                  have hm : m' = m := by
                    split at h
                    · split at h
                      · simpa using h
                      · simp at h
                    · simpa using h
                  subst hm
                  refine ⟨u, frag, f, hu, by simpa using hs, hmem, hurl, by simpa using hst,
                    by simpa using hct, hr⟩

/-- **The guard.** Without `allowPrivateFetch`, when a resolved address of a
name host is private, `step` neither fetches nor returns a method. -/
theorem target_refuses_private {q : Request} {host : String} {texts : List String} {a : L4Factoidal.LWS.InboxGuard.Addr}
    (hp : q.allowPrivateFetch = false) (hname : addr? host = none) (hl : localhostName host = false)
    (hr : q.resolved.lookup host = some texts) (ha : a ∈ texts.filterMap addr?) (hpriv : privateAddr a = true) :
    ∃ w, target q host = .error w := by
  have hpol : q.policy.allowPrivateFetch = false := by simp [Request.policy, hp]
  unfold target
  simp only [hname, hl, hr, Bool.false_eq_true, if_false]
  cases hc : chooseAddress q.policy host texts with
  | error w => exact ⟨w, rfl⟩
  | ok x => exact absurd hc (L4Factoidal.Authz.chooseAddress_refuses_private hpol ha hpriv x)

/-- An IP literal that is private is refused the same way, resolver or not. -/
theorem target_refuses_private_literal {q : Request} {host : String} {a : L4Factoidal.LWS.InboxGuard.Addr}
    (hp : q.allowPrivateFetch = false) (ha : addr? host = some a) (hpriv : privateAddr a = true) :
    ∃ w, target q host = .error w := by
  have hpol : q.policy.allowPrivateFetch = false := by simp [Request.policy, hp]
  have hmem : a ∈ [host].filterMap addr? := by simp [ha]
  unfold target
  simp only [ha]
  cases hc : chooseAddress q.policy host [host] with
  | error w => exact ⟨w, rfl⟩
  | ok x => exact absurd hc (L4Factoidal.Authz.chooseAddress_refuses_private hpol hmem hpriv x)

/-- A refused target gives neither a fetch nor a method. -/
theorem step_refused_target {q : Request} {u frag host : String} {port : Nat} {w : String}
    (hu : documentUrlOf q.vm = .ok (u, frag)) (hs : schemeAllowed q.allowHttp u = true)
    (ha : authority? u = some (host, port)) (ht : target q host = .error w) :
    step q = .failure (.refused u w) := by
  unfold step
  simp [hu, hs, ha, ht]

/-- Without `allowHttp`, an `http` document URL is refused. -/
theorem step_http_refused {q : Request} {u frag : String}
    (hp : q.allowHttp = false) (hu : documentUrlOf q.vm = .ok (u, frag)) (hs : schemeOf u = "http") :
    ∃ w, step q = .failure (.refused u w) := by
  unfold step
  simp [hu, schemeAllowed, hs, hp]

end L4Factoidal.CID.Fetch
