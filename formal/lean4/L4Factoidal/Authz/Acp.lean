/-
L4Factoidal.Authz.Acp — Access Control Policy (ACP) as one policy form, and
Web Access Control (WAC) rules translated into it.

Draft, theorem first. Read the theorems' doc comments first.

## Source

"Access Control Policy (ACP)", Version 0.9.0, Editor's Draft, W3C Solid
Community Group, https://solidproject.org/TR/acp (read 2026-11-11). A
Community Group draft, not a W3C Recommendation. Verbatim:

§6.3: "An Access Mode MUST be granted if and only if in the set of
Effective Policies: a satisfied policy allows the Access Mode; and, no
satisfied policy denies it."

§6.4: "A Policy MUST be satisfied if and only if: it references at least
one Matcher via an acp:allOf or acp:anyOf property; and, all of its
acp:allOf Matchers are satisfied; and, at least one of its acp:anyOf
Matchers is satisfied; and, none of its acp:noneOf Matchers are
satisfied."

§6.5: "A Matcher MUST be satisfied if and only if: it defines at least one
attribute; and, at least one value of each defined attribute matches the
Context."

§6.2: a Policy controls a resource if "it is applied by an Access Control
of an ACR of the resource; or, it is applied by a member Access Control of
an ACR of an ancestor of the resource."

## A defect in §6.4, and the reading taken

Read literally, "at least one of its acp:anyOf Matchers is satisfied" is
false when a policy has no `acp:anyOf`, so a policy with only `acp:allOf`
could never be satisfied. The spec's own example (§4.3.1, policy A:
`acp:allow acl:Read ; acp:allOf ex:matcherB, ex:matcherC`) needs it to be.
The pseudocode (§6.4.2) intends the same but ends
`return policy.allOfMatchers.size !== 0 && policy.anyOfMatchers === 0`,
which compares a Set with 0 and is always false. Reading here: the anyOf
condition applies only when the policy has anyOf matchers (`anyOk`). The
theorem `allOf_only_satisfiable` pins this reading; `#guard` cases show it
on the spec's example.

## What is in the model

* Context: the requesting agent (or none), client, issuer, the resource's
  creators and owners, the credential types presented, and the request
  origin (an extension, §3.2, for WAC's `acl:origin`).
* Matchers with the named individuals PublicAgent, AuthenticatedAgent,
  CreatorAgent, OwnerAgent, PublicClient, PublicIssuer, and
  AlwaysSatisfiedRestriction.
* Policies (allow, deny, allOf, anyOf, noneOf) and granted modes (§6.3).
* Effective policies of a resource from its ACR and its ancestors' member
  Access Controls (§6.2).
* A decision under uncertainty: credential types whose status could not
  be decided (`vcUnknown`).
* WAC authorizations, their translation into policies, and WAC's own
  inheritance (nearest ACL, no merging), which ACP's does not reproduce.

## What it cannot do (stated so nobody assumes otherwise)

* `acp:vc` names a credential TYPE only. ACP says the VC must be "valid"
  and does not say who may issue it. Here a type enters the context only
  through `CredentialMatch` with a trust list scoped to that type (see
  issue 1298); a server that fills `vcs` from any well-signed credential
  lets any issuer vouch for anything.
* Deny and noneOf make decisions non-monotonic: learning MORE about a
  request can REMOVE access (`noneOf_not_monotone`). This is why unknown
  facts must be handled by `grantedSafe`, never by treating them as absent.
* Who may read or change an ACR (WAC's acl:Control) is not modelled: ACP
  leaves it to the server.
* Matching is IRI equality (§6.5). No canonical forms are applied here;
  those belong to `Identity.Binding` before a context is built.
* Being in force is the storage's registry (`Storage`), not a file's name
  or place: `copies_are_inert`. WAC as written, and Factoidal's WAC today,
  activate an ACL by its name (`<resource>.acl`); `byName` and its `#guard`
  show a copied file taking effect.
* WAC `acl:origin` is modelled only as "if the rule names origins, the
  request's origin must be one of them". WAC's full origin rules (trusted
  apps in the owner's profile) are not.

No `sorry`, no `axiom`, no `partial`. Core Lean only.
-/

namespace L4Factoidal.Authz.Acp

inductive Mode where
  | read | append | write | control
deriving DecidableEq, Repr

/-- One instance of resource access (§3.1). `agent = none` is an
unauthenticated request. -/
structure Context where
  agent : Option String
  client : Option String
  issuer : Option String
  creators : List String
  owners : List String
  vcs : List String
  origin : Option String
deriving Repr

inductive AgentVal where
  | iri (a : String) | publicAgent | authenticatedAgent | creatorAgent | ownerAgent
deriving DecidableEq, Repr

inductive OpenVal where
  | iri (a : String) | anyone
deriving DecidableEq, Repr

/-- A matcher. An empty list means the attribute is not defined. -/
structure Matcher where
  agents : List AgentVal := []
  clients : List OpenVal := []
  issuers : List OpenVal := []
  vcs : List String := []
  origins : List String := []
  always : Bool := false
deriving Repr

structure Policy where
  allow : List Mode := []
  deny : List Mode := []
  allOf : List Matcher := []
  anyOf : List Matcher := []
  noneOf : List Matcher := []
deriving Repr

/-! ## Satisfaction (§6.5, §6.4) and granted modes (§6.3) -/

def agentOk (c : Context) : AgentVal → Bool
  | .iri a => c.agent == some a
  | .publicAgent => true
  | .authenticatedAgent => c.agent.isSome
  | .creatorAgent => c.agent.any (fun a => c.creators.contains a)
  | .ownerAgent => c.agent.any (fun a => c.owners.contains a)

def openOk (v : Option String) : OpenVal → Bool
  | .iri a => v == some a
  | .anyone => true

/-- One defined attribute: some value matches. -/
def attrOk {α} (xs : List α) (ok : α → Bool) : Bool := xs.isEmpty || xs.any ok

def defined (m : Matcher) : Bool :=
  !m.agents.isEmpty || !m.clients.isEmpty || !m.issuers.isEmpty || !m.vcs.isEmpty ||
  !m.origins.isEmpty || m.always

def matcherSat (c : Context) (m : Matcher) : Bool :=
  defined m && attrOk m.agents (agentOk c) && attrOk m.clients (openOk c.client) &&
  attrOk m.issuers (openOk c.issuer) && attrOk m.vcs (fun t => c.vcs.contains t) &&
  attrOk m.origins (fun o => c.origin == some o)

def anyOk (c : Context) (p : Policy) : Bool := p.anyOf.isEmpty || p.anyOf.any (matcherSat c)

def policySat (c : Context) (p : Policy) : Bool :=
  (!p.allOf.isEmpty || !p.anyOf.isEmpty) && p.allOf.all (matcherSat c) && anyOk c p &&
  !p.noneOf.any (matcherSat c)

def granted (ps : List Policy) (c : Context) (mode : Mode) : Bool :=
  ps.any (fun p => policySat c p && p.allow.contains mode) &&
  !ps.any (fun p => policySat c p && p.deny.contains mode)

/-! ## Theorems: the spec's rules, as stated -/

/-- **§6.3, both directions.** A mode is granted exactly when a satisfied
policy allows it and no satisfied policy denies it. -/
theorem granted_iff {ps c mode} :
    granted ps c mode = true ↔
      (∃ p ∈ ps, policySat c p = true ∧ mode ∈ p.allow) ∧
      ¬ ∃ p ∈ ps, policySat c p = true ∧ mode ∈ p.deny := by
  simp [granted, List.any_eq_true, List.contains_iff_mem]

/-- **Deny overrules allow.** -/
theorem deny_overrides {ps c mode p} (hp : p ∈ ps) (hs : policySat c p = true)
    (hd : mode ∈ p.deny) : granted ps c mode = false := by
  have : ¬ granted ps c mode = true := fun h => (granted_iff.mp h).2 ⟨p, hp, hs, hd⟩
  simpa using this

/-- **No policy, no access.** -/
theorem nothing_granted_without_policies (c : Context) (mode : Mode) : granted [] c mode = false := by
  simp [granted]

/-- **A matcher that defines nothing matches nothing** (§6.5, "the default
behaviour of a Matcher is to not be satisfied"). -/
theorem empty_matcher_unsatisfied (c : Context) : matcherSat c {} = false := by
  simp [matcherSat, defined]

/-- **noneOf alone is not "everyone except".** A policy with only noneOf
matchers is never satisfied, so it grants nothing and denies nothing. -/
theorem noneOf_only_unsatisfied (c : Context) (ms : List Matcher) (a d : List Mode) :
    policySat c { allow := a, deny := d, noneOf := ms } = false := by
  simp [policySat]

/-- **The reading of §6.4 taken here:** a policy with only allOf matchers
is satisfied when all of them are and no noneOf matcher is. -/
theorem allOf_only_satisfiable {c ms ns a d} (hne : ms ≠ [])
    (hall : ∀ m ∈ ms, matcherSat c m = true) (hnone : ∀ n ∈ ns, matcherSat c n = false) :
    policySat c { allow := a, deny := d, allOf := ms, noneOf := ns } = true := by
  simp only [policySat, anyOk, List.isEmpty_nil, Bool.true_or, Bool.and_true, Bool.and_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', List.isEmpty_eq_false_iff, List.all_eq_true,
    List.any_eq_false]
  refine ⟨⟨Or.inl hne, hall⟩, ?_⟩
  intro n hn; simp [hnone n hn]

/-- **Public means public, authenticated means signed in.** A matcher
naming PublicAgent matches every context; AuthenticatedAgent matches
exactly the contexts with an agent. -/
theorem public_and_authenticated (c : Context) :
    matcherSat c { agents := [.publicAgent] } = true ∧
    matcherSat c { agents := [.authenticatedAgent] } = c.agent.isSome := by
  simp [matcherSat, defined, attrOk, agentOk]

/-! ## Theorems: monotonicity, and where it fails -/

/-- Context `c'` knows at least what `c` knows about credentials. -/
def moreVcs (c c' : Context) : Prop :=
  c'.agent = c.agent ∧ c'.client = c.client ∧ c'.issuer = c.issuer ∧ c'.creators = c.creators ∧
  c'.owners = c.owners ∧ c'.origin = c.origin ∧ ∀ t ∈ c.vcs, t ∈ c'.vcs

theorem matcherSat_mono {c c' m} (h : moreVcs c c') (hs : matcherSat c m = true) :
    matcherSat c' m = true := by
  obtain ⟨ha, hc, hi, hcr, ho, hor, hv⟩ := h
  simp only [matcherSat, attrOk, agentOk, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true,
    List.contains_iff_mem] at hs ⊢
  obtain ⟨⟨⟨⟨⟨hd, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := hs
  refine ⟨⟨⟨⟨⟨hd, ?_⟩, ?_⟩, ?_⟩, ?_⟩, ?_⟩
  · rcases h1 with h1 | ⟨x, hx, hxs⟩
    · exact Or.inl h1
    · exact Or.inr ⟨x, hx, by cases x <;> simp_all [agentOk]⟩
  · simpa [hc] using h2
  · simpa [hi] using h3
  · rcases h4 with h4 | ⟨t, ht, htv⟩
    · exact Or.inl h4
    · exact Or.inr ⟨t, ht, hv t htv⟩
  · simpa [hor] using h5

/-- A positive policy: it allows, never denies, and has no noneOf. -/
def positive (p : Policy) : Bool := p.deny.isEmpty && p.noneOf.isEmpty

/-- **Positive policies are monotone.** With no deny and no noneOf,
presenting more credentials can only add access. WAC rules translate to
positive policies (`toPolicy_positive`). -/
theorem granted_mono_positive {ps c c' mode} (hpos : ∀ p ∈ ps, positive p = true)
    (h : moreVcs c c') (hg : granted ps c mode = true) : granted ps c' mode = true := by
  rw [granted_iff] at hg ⊢
  obtain ⟨⟨p, hp, hs, ha⟩, _⟩ := hg
  have hpp := hpos p hp
  simp only [positive, Bool.and_eq_true, List.isEmpty_iff] at hpp
  refine ⟨⟨p, hp, ?_, ha⟩, ?_⟩
  · simp only [policySat, anyOk, Bool.and_eq_true, Bool.or_eq_true, List.all_eq_true,
      List.any_eq_true, Bool.not_eq_true', List.any_eq_false, hpp.2] at hs ⊢
    obtain ⟨⟨⟨hne, hall⟩, hany⟩, _⟩ := hs
    refine ⟨⟨⟨hne, fun m hm => matcherSat_mono h (hall m hm)⟩, ?_⟩, by simp⟩
    rcases hany with hany | ⟨m, hm, hms⟩
    · exact Or.inl hany
    · exact Or.inr ⟨m, hm, matcherSat_mono h hms⟩
  · rintro ⟨q, hq, _, hd⟩
    have hqp := hpos q hq
    simp only [positive, Bool.and_eq_true, List.isEmpty_iff] at hqp
    simp [hqp.1] at hd

/-! ## Deciding when some credential statuses are unknown -/

/-- The context with these credential types. -/
def withVcs (c : Context) (vs : List String) : Context := { c with vcs := vs }

/-- Allow only on what surely holds; deny on what possibly holds. `sure`
has the credential types known valid; `maybe` adds those whose status
could not be decided. -/
def policySure (c : Context) (unknown : List String) (p : Policy) : Bool :=
  (!p.allOf.isEmpty || !p.anyOf.isEmpty) && p.allOf.all (matcherSat c) && anyOk c p &&
  !p.noneOf.any (matcherSat (withVcs c (c.vcs ++ unknown)))

def policyMaybe (c : Context) (unknown : List String) (p : Policy) : Bool :=
  let c' := withVcs c (c.vcs ++ unknown)
  (!p.allOf.isEmpty || !p.anyOf.isEmpty) && p.allOf.all (matcherSat c') && anyOk c' p &&
  !p.noneOf.any (matcherSat c)

def grantedSafe (ps : List Policy) (c : Context) (unknown : List String) (mode : Mode) : Bool :=
  ps.any (fun p => policySure c unknown p && p.allow.contains mode) &&
  !ps.any (fun p => policyMaybe c unknown p && p.deny.contains mode)

theorem anyOk_mono {c c' p} (h : moreVcs c c') (hs : anyOk c p = true) : anyOk c' p = true := by
  simp only [anyOk, Bool.or_eq_true, List.any_eq_true] at hs ⊢
  rcases hs with hs | ⟨m, hm, hms⟩
  · exact Or.inl hs
  · exact Or.inr ⟨m, hm, matcherSat_mono h hms⟩

/-- **Safe under uncertainty.** If `grantedSafe` allows a mode, then
`granted` allows it however each unknown status turns out: for every set
of credential types between "known valid" and "known valid or unknown".
An unreachable status list never opens a door, through allow or through a
noneOf or deny that it would have triggered. -/
theorem grantedSafe_sound {ps c unknown mode} {vs : List String}
    (hlo : ∀ t ∈ c.vcs, t ∈ vs) (hhi : ∀ t ∈ vs, t ∈ c.vcs ∨ t ∈ unknown)
    (h : grantedSafe ps c unknown mode = true) : granted ps (withVcs c vs) mode = true := by
  have lo : moreVcs c (withVcs c vs) := ⟨rfl, rfl, rfl, rfl, rfl, rfl, hlo⟩
  have hi : moreVcs (withVcs c vs) (withVcs c (c.vcs ++ unknown)) :=
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, fun t ht => by
      simp only [withVcs, List.mem_append]; exact hhi t ht⟩
  simp only [grantedSafe, Bool.and_eq_true, Bool.not_eq_true', List.any_eq_true,
    List.any_eq_false, List.contains_iff_mem] at h
  obtain ⟨⟨p, hp, hsure, ha⟩, hnodeny⟩ := h
  rw [granted_iff]
  constructor
  · refine ⟨p, hp, ?_, ha⟩
    simp only [policySure, policySat, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
      List.any_eq_false] at hsure ⊢
    obtain ⟨⟨⟨hne, hall⟩, hany⟩, hnone⟩ := hsure
    refine ⟨⟨⟨hne, fun m hm => matcherSat_mono lo (hall m hm)⟩, anyOk_mono lo hany⟩, ?_⟩
    intro n hn
    cases hx : matcherSat (withVcs c vs) n
    · simp
    · have := matcherSat_mono hi hx; simp [hnone n hn] at this
  · rintro ⟨q, hq, hqs, hd⟩
    have hm : policyMaybe c unknown q = true := by
      simp only [policySat, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
        List.any_eq_false] at hqs
      simp only [policyMaybe, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
        List.any_eq_false]
      obtain ⟨⟨⟨hne, hall⟩, hany⟩, hnone⟩ := hqs
      refine ⟨⟨⟨hne, fun m hm => matcherSat_mono hi (hall m hm)⟩, anyOk_mono hi hany⟩, ?_⟩
      intro n hn
      cases hx : matcherSat c n
      · simp
      · have := matcherSat_mono lo hx; simp [hnone n hn] at this
    have := hnodeny q hq
    simp [hm, hd] at this

/-! ## WAC rules as policies -/

/-- One WAC authorization that applies to the resource (after WAC's own
inheritance has chosen the ACL). `groupMembers` are the members of its
`acl:agentGroup`s, read by the host. -/
structure WacAuth where
  agents : List String := []
  groupMembers : List String := []
  publicClass : Bool := false
  authenticatedClass : Bool := false
  origins : List String := []
  modes : List Mode := []
deriving Repr

/-- WAC: Write implies Append ("acl:Append is a subclass of acl:Write"). -/
def expand (ms : List Mode) : List Mode := if ms.contains .write then ms ++ [.append] else ms

def wacAgentOk (c : Context) (a : WacAuth) : Bool :=
  a.publicClass || (a.authenticatedClass && c.agent.isSome) ||
  c.agent.any (fun x => a.agents.contains x || a.groupMembers.contains x)

def wacGranted (as : List WacAuth) (c : Context) (mode : Mode) : Bool :=
  as.any (fun a => wacAgentOk c a && (a.origins.isEmpty || a.origins.any (fun o => c.origin == some o)) &&
    (expand a.modes).contains mode)

def agentVals (a : WacAuth) : List AgentVal :=
  (if a.publicClass then [.publicAgent] else []) ++
  (if a.authenticatedClass then [.authenticatedAgent] else []) ++
  (a.agents ++ a.groupMembers).map .iri

/-- The policy for one WAC authorization. An authorization that names no
agent becomes a policy whose matcher defines no agent; it then matches only
by origin, or (with no origin either) not at all. -/
def toPolicy (a : WacAuth) : Policy :=
  { allow := expand a.modes,
    allOf := [{ agents := agentVals a, origins := a.origins,
                always := (agentVals a).isEmpty && a.origins.isEmpty }] }

theorem toPolicy_positive (a : WacAuth) : positive (toPolicy a) = true := by
  simp [positive, toPolicy]

theorem anyEq (l : List String) (v : String) : (l.any fun x => v == x) = decide (v ∈ l) := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, beq_iff_eq, decide_eq_true_eq]
  constructor
  · rintro ⟨x, hx, rfl⟩; exact hx
  · intro h; exact ⟨v, h, rfl⟩

theorem agentVals_any (c : Context) (a : WacAuth) :
    (agentVals a).any (agentOk c) = wacAgentOk c a := by
  unfold agentVals wacAgentOk
  cases ha : c.agent <;> cases a.publicClass <;> cases a.authenticatedClass <;>
    simp [agentOk, ha, List.any_map, Function.comp_def, List.any_append, List.any_eq_true,
      List.contains_iff_mem, Option.any, anyEq]

theorem policySat_toPolicy {c a} (hv : agentVals a ≠ []) :
    policySat c (toPolicy a) =
      (wacAgentOk c a && (a.origins.isEmpty || a.origins.any (fun o => c.origin == some o))) := by
  have hv' : (agentVals a).isEmpty = false := by simpa using hv
  simp only [policySat, toPolicy, anyOk, matcherSat, defined, attrOk, hv', List.all_cons,
    List.all_nil, List.isEmpty_nil, List.any_nil, Bool.not_false, Bool.and_true, Bool.true_and,
    Bool.or_false, Bool.not_true, Bool.false_or, Bool.true_or, Bool.and_false, List.isEmpty_cons,
    Bool.or_true, agentVals_any]

/-- **WAC rules keep their meaning as policies**, for every authorization
that names at least one agent, group member or class. -/
theorem wac_translation {as c mode} (hnamed : ∀ a ∈ as, agentVals a ≠ []) :
    granted (as.map toPolicy) c mode = wacGranted as c mode := by
  have hdeny : (as.map toPolicy).any (fun p => policySat c p && p.deny.contains mode) = false := by
    simp [toPolicy]
  simp only [granted, hdeny, Bool.not_false, Bool.and_true, wacGranted, List.any_map,
    Function.comp_def]
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨a, ha, hs, hm⟩
    rw [policySat_toPolicy (hnamed a ha)] at hs
    simp only [Bool.and_eq_true] at hs
    exact ⟨a, ha, hs, by simpa [toPolicy] using hm⟩
  · rintro ⟨a, ha, hs, hm⟩
    refine ⟨a, ha, ?_, by simpa [toPolicy] using hm⟩
    rw [policySat_toPolicy (hnamed a ha)]
    simpa only [Bool.and_eq_true] using hs

/-! ## Inheritance: WAC's and ACP's differ -/

/-- A resource's ACR and its ancestors' ACRs, nearest first: each is (own
Access Control policies, member Access Control policies). -/
def effective (own : List Policy × List Policy) (ancestors : List (List Policy × List Policy)) :
    List Policy :=
  own.1 ++ (ancestors.map Prod.snd).flatten

/-- **ACP inheritance accumulates** (§6.2): a member policy of ANY
ancestor controls the resource. WAC instead uses only the nearest ACL. So
a WAC `acl:default` cannot be copied to `acp:memberAccessControl` of the
same container and keep its meaning: a deeper ACL that WAC would use alone
is, in ACP, added to every default above it. The faithful translation is
`toPolicy` over the authorizations WAC's own walk chose, applied as the
resource's own Access Control. -/
theorem acp_accumulates {own anc p} (hp : ∃ a ∈ anc, p ∈ (a : List Policy × List Policy).2) :
    p ∈ effective own anc := by
  obtain ⟨a, ha, hpa⟩ := hp
  simp only [effective, List.mem_append, List.mem_flatten, List.mem_map]
  exact Or.inr ⟨a.2, ⟨a, ha, rfl⟩, hpa⟩

/-! ## In force versus merely present: a copied policy file does nothing -/

/-- A storage. `files` is every document, parsed as policies where it
parses. `own` and `members` are the storage's REGISTRY: for each
resource, the paths of the policy documents in force for it, and for each
container, those in force for its members. The registry is not a file:
it changes only through the access-control API, by an agent with Control,
so copying, syncing or restoring files (WebDAV, Finder, a backup) never
writes it. `ancestors r` lists r's containers, nearest first. -/
structure Storage where
  files : List (String × List Policy)
  own : String → List String
  members : String → List String
  ancestors : String → List String

def look (fs : List (String × List Policy)) (path : String) : List Policy :=
  ((fs.find? (fun f => f.1 == path)).map Prod.snd).getD []

def resolve (fs : List (String × List Policy)) (paths : List String) : List Policy :=
  paths.flatMap (look fs)

/-- §6.2 over the registry: the resource's own documents, and the member
documents of every ancestor. -/
def inForce (st : Storage) (r : String) : List Policy :=
  resolve st.files (st.own r) ++ (st.ancestors r).flatMap (fun a => resolve st.files (st.members a))

def decideAt (st : Storage) (r : String) (c : Context) (mode : Mode) : Bool :=
  granted (inForce st r) c mode

/-- The paths whose contents can matter for resource `r`. -/
def registered (st : Storage) (r : String) (path : String) : Prop :=
  path ∈ st.own r ∨ ∃ a ∈ st.ancestors r, path ∈ st.members a

theorem flatMap_congr' {α β} {l : List α} {f g : α → List β} (h : ∀ x ∈ l, f x = g x) :
    l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]

theorem resolve_congr {fs fs' : List (String × List Policy)} {paths : List String}
    (h : ∀ p ∈ paths, look fs p = look fs' p) : resolve fs paths = resolve fs' paths := by
  unfold resolve
  exact flatMap_congr' h

/-- **Copies are inert.** Two storages with the same registry whose files
agree on every registered path give the same decision for `r`, whatever
else they hold. A `.acl`, ACR or policy file copied into a folder, synced
from another pod, or left by a restore is just data until the registry
names it. -/
theorem copies_are_inert {st st' : Storage} {r c mode}
    (hown : st'.own = st.own) (hmem : st'.members = st.members) (hanc : st'.ancestors = st.ancestors)
    (hfiles : ∀ path, registered st r path → look st.files path = look st'.files path) :
    decideAt st' r c mode = decideAt st r c mode := by
  have : inForce st' r = inForce st r := by
    unfold inForce
    rw [hown, hmem, hanc]
    congr 1
    · exact (resolve_congr (fun p hp => hfiles p (Or.inl hp))).symm
    · exact flatMap_congr' (fun a ha => (resolve_congr (fun p hp => hfiles p (Or.inr ⟨a, ha, hp⟩))).symm)
  simp [decideAt, this]

/-- Activation by NAME, as WAC's effective-ACL walk does today
(`Solid/Server/WAC.lean`, `aclPathOf`: the ACL of `r` is the file at
`r ++ ".acl"`). -/
def byName (fs : List (String × List Policy)) (r : String) (c : Context) (mode : Mode) : Bool :=
  granted (look fs (r ++ ".acl")) c mode

/-! ## Worked cases -/

def bob : Context :=
  ⟨some "https://bob.example/#me", some "https://app.example", some "https://idp.example", [], [], [], none⟩

-- §6.3.1: B allows Read and Write, C denies Write; both satisfied → Read only.
def always : Matcher := { always := true }
#guard granted [{ allow := [.read, .write], allOf := [always] }, { deny := [.write], allOf := [always] }] bob .read
#guard !granted [{ allow := [.read, .write], allOf := [always] }, { deny := [.write], allOf := [always] }] bob .write
-- §4.3.1 policy A: allOf only is satisfiable (the reading of §6.4 taken here).
#guard policySat bob { allow := [.read], allOf := [{ agents := [.iri "https://bob.example/#me"] }, { clients := [.anyone] }] }
-- An issuer matcher: only Google sign-ins.
#guard !matcherSat bob { issuers := [.iri "https://accounts.google.com"] }
-- noneOf makes access non-monotonic: presenting a "Suspended" credential removes it.
def doctorsNotSuspended : Policy :=
  { allow := [.read], allOf := [{ vcs := ["MedicalLicence"] }], noneOf := [{ vcs := ["Suspended"] }] }
#guard granted [doctorsNotSuspended] (withVcs bob ["MedicalLicence"]) .read
#guard !granted [doctorsNotSuspended] (withVcs bob ["MedicalLicence", "Suspended"]) .read
-- With "Suspended" undecidable, the safe decision refuses.
#guard !grantedSafe [doctorsNotSuspended] (withVcs bob ["MedicalLicence"]) ["Suspended"] .read
-- WAC: Write implies Append, and the translated policy agrees.
#guard wacGranted [{ agents := ["https://bob.example/#me"], modes := [.write] }] bob .append
#guard granted ([({ agents := ["https://bob.example/#me"], modes := [.write] } : WacAuth)].map toPolicy) bob .append

-- Copied in: an ACL that gives everyone Write, inside a restored folder.
def everyoneWrites : List Policy := [{ allow := [.write], allOf := [{ agents := [.publicAgent] }] }]
def pod0 : Storage :=
  Storage.mk [("/pics/.acr", [])] (fun r => if r == "/pics/a.jpg" then ["/pics/.acr"] else [])
    (fun _ => []) (fun _ => ["/pics/"])
def podCopied : Storage := { pod0 with files := pod0.files ++ [("/pics/a.jpg.acl", everyoneWrites)] }
-- By registry: nothing changes.
#guard !decideAt pod0 "/pics/a.jpg" bob .write && !decideAt podCopied "/pics/a.jpg" bob .write
-- By name: the copied file is in force at once.
#guard !byName pod0.files "/pics/a.jpg" bob .write && byName podCopied.files "/pics/a.jpg" bob .write

end L4Factoidal.Authz.Acp
