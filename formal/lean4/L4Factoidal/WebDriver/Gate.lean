/-
L4Factoidal.WebDriver.Gate: who may use the WebDriver endpoint.

A WebDriver endpoint is remote control of the browser: whoever can send it a request can
read every page the browser shows and act as its user. This module decides, before any
command is looked at, whether the endpoint exists at all and whether a request is let in.
The host (the listener) opens the socket this module allows and passes each request's
method, path and two headers; it decides nothing.

Threat model (record: docs/designissues/2026-11-14-input-webdriver.md, "Security"):

1. A web page in any browser on this machine (this one included) can make its browser
   send HTTP requests to a loopback port (a form post or a `fetch` with a simple content
   type). Such a request carries an `Origin` header, cannot set a path it does not know,
   and after a DNS rebinding carries another `Host`. Refused: any request with an `Origin`
   header, any request whose `Host` is not this endpoint on a loopback name, any request
   whose path does not start with the secret.
2. Another process or user of this machine can connect to a loopback port. Refused
   without the secret: 128 bits from the machine's generator, made at start, given only
   to the process that asked for the endpoint (the host prints it for that process or
   writes it to a file only the user can read). The secret is compared without an early
   exit, and after `maxFailures` refused requests the endpoint is locked until it is
   started again, so guessing or timing the comparison gets at most `maxFailures` tries.
3. Another machine. The endpoint is bound to a loopback address only (`start` refuses
   any other), so no packet from outside reaches it.
4. A user who did not ask for it. The endpoint is off by default: `start` refuses unless
   the user's flag is set, and refuses when the machine has no generator.

Proved: `start_off`, `start_not_loopback`, `start_no_entropy` (the three refusals of
`start`), `start_secret_length` (a started endpoint has a 32 character secret),
`sameText_iff` (the comparison is equality), `admit_ok` (a request that is let in
carried the secret, no `Origin`, and this endpoint's loopback `Host`), `admit_no_secret`,
`admit_origin`, `admit_locked` (the refusals), `admit_failures_mono` (the count of
refusals never falls), `admit_refused_counts` (every refusal but the lock's is counted).
Not shown: that the compiled comparison takes the same time for every input (it reads
every character; the branch on each is data-dependent). The lock bounds what that leaks.
-/

import L4Factoidal.Risk

namespace L4Factoidal.WebDriver.Gate

/-! ## Starting the endpoint -/

/-- A loopback address: the only kind the endpoint may be bound to. -/
def isLoopback (address : String) : Bool := address == "127.0.0.1" || address == "::1"

/-- What the host asks to start an endpoint with. -/
structure Launch where
  /-- The user's flag: the risk accepted by name (`Risk.webdriverEndpoint`; the test
  runner's `--dangerously-enable-webdriver-endpoint` is the only caller of
  `Risk.dangerouslyAccept` for it). Off unless the user set it. -/
  enabled : Option (Risk.Accepted .webdriverEndpoint) := none
  /-- The address to bind. -/
  address : String := "127.0.0.1"
  /-- Bytes of the machine's generator; empty when it has none. -/
  entropy : ByteArray := ByteArray.empty

/-- The secret needs this many bytes of the generator (128 bits). -/
def secretBytes : Nat := 16

def hexDigit (n : Nat) : Char := if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- The first `secretBytes` bytes as lower-case hexadecimal. -/
def secretOf (entropy : ByteArray) : String :=
  String.ofList ((List.range secretBytes).flatMap fun i =>
    let b := (entropy.get! i).toNat
    [hexDigit (b / 16), hexDigit (b % 16)])

inductive StartRefusal where
  | off | notLoopback | noEntropy
  deriving DecidableEq, Repr, Inhabited

/-- Whether the endpoint starts, and with which secret. -/
def start (l : Launch) : Except StartRefusal String :=
  if l.enabled.isNone then .error .off
  else if !isLoopback l.address then .error .notLoopback
  else if l.entropy.size < secretBytes then .error .noEntropy
  else .ok (secretOf l.entropy)

/-! ## Letting a request in -/

/-- The characters that differ at the same place in two lists of the same length. -/
def mismatches : List Char → List Char → Nat
  | a :: as, b :: bs => (if a == b then 0 else 1) + mismatches as bs
  | _, _ => 0

/-- Equality of two texts that reads every character (no early exit on the first
difference). -/
def sameText (a b : String) : Bool :=
  a.length == b.length && mismatches a.toList b.toList == 0

structure Config where
  secret : String
  port : Nat

/-- What the gate reads of a request: its path and two headers. -/
structure Request where
  path : String
  host : String := ""
  origin : Option String := none

/-- The gate's own state: how many requests it refused. -/
structure State where
  failures : Nat := 0
  deriving DecidableEq, Repr, Inhabited

/-- Refused requests before the endpoint locks. -/
def maxFailures : Nat := 16

inductive Refusal where
  | locked | origin | host | secret
  deriving DecidableEq, Repr, Inhabited

/-- The `Host` header names this endpoint on a loopback name. -/
def hostOk (port : Nat) (host : String) : Bool :=
  let p := ":" ++ toString port
  host == "127.0.0.1" ++ p || host == "localhost" ++ p || host == "[::1]" ++ p

/-- The first segment of a path and the segments after it, without the query. -/
def splitPath (path : String) : String × List String :=
  let noQuery := String.ofList (path.toList.takeWhile (· != '?'))
  match noQuery.splitOn "/" with
  | "" :: first :: rest => (first, rest.filter (· != ""))
  | _ => ("", [])

/-- Let a request in or refuse it. In: the path segments after the secret. -/
def admit (cfg : Config) (g : State) (r : Request) : State × Except Refusal (List String) :=
  if g.failures ≥ maxFailures then (g, .error .locked)
  else if r.origin.isSome then ({ failures := g.failures + 1 }, .error .origin)
  else if !hostOk cfg.port r.host then ({ failures := g.failures + 1 }, .error .host)
  else if sameText (splitPath r.path).1 cfg.secret then (g, .ok (splitPath r.path).2)
  else ({ failures := g.failures + 1 }, .error .secret)

/-! ## Theorems -/

/-- Off by default. Says: without the user's flag no endpoint starts, whatever the address
and the entropy. Does not say: who may set the flag (the host's command line). -/
theorem start_off (l : Launch) (h : l.enabled = none) : start l = .error .off := by
  simp [start, h]

/-- Default launch. Says: a launch nobody configured is refused. Does not say: more than
`start_off` (it is the default's instance). -/
theorem start_default : start {} = .error .off := rfl

/-- Loopback only. Says: an address that is not 127.0.0.1 or ::1 is refused, so the
endpoint is never reachable from another machine. Does not say: that the host binds
exactly the address it asked about (host plumbing; read the listener). -/
theorem start_not_loopback (l : Launch) (h : isLoopback l.address = false) :
    ∃ r, start l = .error r := by
  unfold start
  split
  · exact ⟨_, rfl⟩
  · rw [if_pos (by simp [h])]
    exact ⟨_, rfl⟩

/-- Needs a generator. Says: with fewer than 16 bytes of entropy no endpoint starts: there
is never an endpoint with a guessable secret. Does not say: that the bytes are random
(the machine's generator is trusted). -/
theorem start_no_entropy (l : Launch) (h : l.entropy.size < secretBytes) :
    ∃ r, start l = .error r := by
  unfold start
  split
  · exact ⟨_, rfl⟩
  · split
    · exact ⟨_, rfl⟩
    · exact ⟨_, rfl⟩

/-- Secret size. Says: a started endpoint's secret has 32 characters (128 bits as
hexadecimal). Does not say: that they are unpredictable (as above). -/
theorem start_secret_length (l : Launch) (s : String) (h : start l = .ok s) : s.length = 32 := by
  unfold start at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h
        subst h
        simp [secretOf, secretBytes, List.length_flatMap]
        rfl

theorem mismatches_zero_iff : ∀ (a b : List Char), a.length = b.length → (mismatches a b = 0 ↔ a = b)
  | [], [], _ => by simp [mismatches]
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h
  | x :: xs, y :: ys, h => by
    have ih := mismatches_zero_iff xs ys (by simpa using h)
    by_cases hxy : x = y
    · subst hxy
      simp [mismatches, ih]
    · simp [mismatches, hxy]

/-- Comparison. Says: `sameText` answers true exactly for equal texts: a request is let in
only with the whole secret, and the whole secret always lets it in. Does not say: how
long the comparison takes. -/
theorem sameText_iff (a b : String) : sameText a b = true ↔ a = b := by
  unfold sameText
  constructor
  · intro h
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    have hl : a.toList.length = b.toList.length := by
      have := h.1
      simp only [String.length_toList] at *
      exact this
    exact String.toList_inj.mp ((mismatches_zero_iff _ _ hl).mp h.2)
  · intro h
    subst h
    simp [(mismatches_zero_iff a.toList a.toList rfl).mpr rfl]

/-- Let in. Says: a request that is let in had the secret as its first path segment, no
`Origin` header, the endpoint's own loopback `Host`, and the gate was not locked. Does
not say: that the request is a valid command. -/
theorem admit_ok (cfg : Config) (g : State) (r : Request) (g' : State) (segs : List String)
    (h : admit cfg g r = (g', .ok segs)) :
    (splitPath r.path).1 = cfg.secret ∧ r.origin = none ∧ hostOk cfg.port r.host = true ∧
      g.failures < maxFailures ∧ g' = g := by
  unfold admit at h
  split at h
  · simp at h
  · rename_i hlock
    split at h
    · simp at h
    · rename_i horigin
      split at h
      · simp at h
      · rename_i hhost
        split at h
        · rename_i hsecret
          simp only [Prod.mk.injEq, Except.ok.injEq] at h
          refine ⟨(sameText_iff _ _).mp hsecret, ?_, ?_, ?_, h.1.symm⟩
          · simpa using horigin
          · simpa using hhost
          · omega
        · simp at h

/-- No secret. Says: a request whose first path segment is not the secret is refused,
whatever else it carries and whatever the gate's state. Does not say: which refusal it
gets (the lock, the `Origin`, the `Host` or the secret, in that order). -/
theorem admit_no_secret (cfg : Config) (g : State) (r : Request) (h : (splitPath r.path).1 ≠ cfg.secret) :
    ∃ g' why, admit cfg g r = (g', .error why) := by
  unfold admit
  split
  · exact ⟨_, _, rfl⟩
  · split
    · exact ⟨_, _, rfl⟩
    · split
      · exact ⟨_, _, rfl⟩
      · split
        · rename_i hs
          exact absurd ((sameText_iff _ _).mp hs) h
        · exact ⟨_, _, rfl⟩

/-- Pages. Says: a request with an `Origin` header (every request a page's script or form
makes across origins) is refused even with the right secret. Does not say: anything of a
client that sends no `Origin` (a WebDriver client does not). -/
theorem admit_origin (cfg : Config) (g : State) (r : Request) (o : String) (h : r.origin = some o) :
    ∃ g' why, admit cfg g r = (g', .error why) := by
  unfold admit
  split
  · exact ⟨_, _, rfl⟩
  · simp [h]

/-- Lock. Says: after `maxFailures` refusals every request is refused, the right secret
included, until the endpoint is started again: a guesser has at most `maxFailures` tries.
Does not say: that the owner is told (the host logs it). -/
theorem admit_locked (cfg : Config) (g : State) (r : Request) (h : maxFailures ≤ g.failures) :
    admit cfg g r = (g, .error .locked) := by
  simp [admit, h]

/-- The count never falls. Says: no request lowers the count of refusals, so the lock,
once reached, stays. Does not say: that it rises on every request (not on one let in). -/
theorem admit_failures_mono (cfg : Config) (g : State) (r : Request) :
    g.failures ≤ (admit cfg g r).1.failures := by
  unfold admit
  repeat' split
  all_goals simp

/-- Refusals count. Says: a request refused for its `Origin`, its `Host` or its secret
raises the count by one. Does not say: anything of the lock's own refusals (the count is
already at the limit). -/
theorem admit_refused_counts (cfg : Config) (g : State) (r : Request) (g' : State) (why : Refusal)
    (h : admit cfg g r = (g', .error why)) (hw : why ≠ .locked) : g'.failures = g.failures + 1 := by
  unfold admit at h
  split at h
  · simp only [Prod.mk.injEq, Except.error.injEq] at h
    exact absurd h.2.symm hw
  · split at h
    · simp only [Prod.mk.injEq] at h
      rw [← h.1]
    · split at h
      · simp only [Prod.mk.injEq] at h
        rw [← h.1]
      · split at h
        · simp at h
        · simp only [Prod.mk.injEq] at h
          rw [← h.1]

/-! ## Tests -/

private def cfg : Config := { secret := "00112233445566778899aabbccddeeff", port := 4444 }
private def ok (path : String) (host : String := "127.0.0.1:4444") (origin : Option String := none) (failures : Nat := 0) : Bool :=
  match (admit cfg { failures } { path, host, origin }).2 with
  | .ok _ => true
  | .error _ => false

#guard ok "/00112233445566778899aabbccddeeff/session"
#guard ok "/00112233445566778899aabbccddeeff/status" "localhost:4444"
#guard !ok "/session"
#guard !ok "/00112233445566778899aabbccddeef0/session"
#guard !ok "/00112233445566778899aabbccddeeff/session" "evil.example:4444"
#guard !ok "/00112233445566778899aabbccddeeff/session" "127.0.0.1:4445"
#guard !ok "/00112233445566778899aabbccddeeff/session" "127.0.0.1:4444" (some "https://evil.example")
#guard !ok "/00112233445566778899aabbccddeeff/session" "127.0.0.1:4444" none 16
#guard (admit cfg {} { path := "/00112233445566778899aabbccddeeff/session/abc/element?x=1", host := "127.0.0.1:4444" }).2.toOption == some ["session", "abc", "element"]
#guard (start { enabled := some (Risk.dangerouslyAccept .webdriverEndpoint), entropy := ByteArray.mk (Array.range 16 |>.map (·.toUInt8)) }).toOption == some "000102030405060708090a0b0c0d0e0f"
#guard (start { enabled := some (Risk.dangerouslyAccept .webdriverEndpoint), address := "0.0.0.0", entropy := ByteArray.mk (Array.range 16 |>.map (·.toUInt8)) }).toOption == none
#guard (start { enabled := some (Risk.dangerouslyAccept .webdriverEndpoint) }).toOption == none
#guard sameText "abc" "abc" && !sameText "abc" "abd" && !sameText "abc" "ab" && !sameText "" "a"

end L4Factoidal.WebDriver.Gate
