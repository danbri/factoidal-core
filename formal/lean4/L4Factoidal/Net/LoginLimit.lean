/-
L4Factoidal.Net.LoginLimit — the failed-login limit that the login surfaces
share: the WebDAV listener login (`L4Factoidal.WebDAV.Login`, on TCP and on
HTTP over XMPP) and the SASL login of `xmpp-serve`
(`L4Factoidal.XMPP.Server`).

https://github.com/danbri/factoidal/issues/1119 (the limit, WebDAV),
https://github.com/danbri/factoidal/issues/1128 (keys per requester; the
SASL limit), audit row C2 of
`docs/designissues/2026-10-28-feature-combination-safety.md` (invariant I2).

Owner, 2026-10-28, verbatim: "Does “no rate limit” expose our server
passwords to automated hacking tools? In which case default to protection
but have a —dangerously-disable-ratelimits option ?" So `Limits.enabled` is
`true` by default.

The counters (moved here from `WebDAV/Login.lean` unchanged):

* A key has a fixed window that starts at its first failure: at most
  `Limits.maxFailures` failures (default 5) in `Limits.window` seconds
  (default 60). A key with that many failures in a live window is blocked.
* `Failures.check`: `some seconds` (the caller refuses, with no password
  check) when a key of the attempt is blocked, or when the table has no
  place for the keys of the attempt.
* `Failures.record`: one failure for each key. At most `Limits.maxKeys`
  live counters; a new key evicts the counter with the oldest window that is
  not blocked and not a key of this attempt; a blocked counter is never
  evicted.

The requester (invariant I2): each failure counts against a key that names
the requester on its transport, never against an empty key, and the keys of
two transports never collide.

* `Requester.tcp address`: the client address as the socket gives it; the
  key is `address:` ++ `clientPrefix address` (an IPv4 address, or the /64
  prefix of an IPv6 address).
* `Requester.xmpp bareJid`: the bare JID of the sender, from the `from`
  that the XMPP server stamps (HTTP over XMPP); the key is `jid:` ++ the
  bare JID. The caller gives the bare JID already in the form of
  `HttpOverXmpp.bareKey` (domain part in lower case).
* `Requester.valid`: the part after the prefix is not empty. A caller that
  cannot name the requester does not run a login (`WebDAV.Login.admit`
  answers 401 with no derivation and counts nothing).

Theorems: `requesterKey_injective_kind`, `requesterKey_xmpp_injective`,
`requesterKey_length`, `loginKeys_nonempty`.

The address tag (`addressTag`, 2026-11-07): `xmpp-serve` keeps no client
address. At start the host makes a random key that lives in memory only (a new
one at each restart), and the engine keys the client's address part
(`clientPrefix`: the IPv4 address, or the /64 of an IPv6 address) with
HMAC-SHA-256 under it. The counters then hold `address:` and 64 hexadecimal
digits. `clientPrefix` stays the one place that groups addresses: theorem
`addressTag_prefix`. The address can come from the socket or from a PROXY
protocol header (`Net.ProxyProtocol`). Theorems `addressTag_prefix`,
`addressTag_empty`.

No `sorry`, no `axiom`, no `partial`.
-/
import L4Factoidal.Crypto.Hmac

namespace L4Factoidal.Net.LoginLimit

/-- A decimal count: digits only, at most 9 of them. -/
def decimal? (s : String) : Option Nat :=
  if s.isEmpty || s.length > 9 || !s.all Char.isDigit then none else s.toNat?

/-- An IPv4 address in dotted decimal, each part 0 to 255. -/
def ipv4Parts? (h : String) : Option (List Nat) :=
  let ps := h.splitOn "."
  if ps.length != 4 then none
  else ps.mapM (fun p => match decimal? p with
    | some v => if v ≤ 255 && p.length ≤ 3 then some v else none
    | none => none)

/-- The default count of failures per key in one window. -/
def defaultLimitFailures : Nat := 5
/-- The default window, in seconds. -/
def defaultLimitWindow : Nat := 60
/-- The most keys that have a counter at one time. -/
def maxTrackedKeys : Nat := 10000
/-- The largest `--login-limit`. -/
def maxLimitFailures : Nat := 1000
/-- The largest `--login-window` (one day). -/
def maxLimitWindow : Nat := 86400

structure Limits where
  enabled : Bool := true
  maxFailures : Nat := defaultLimitFailures
  window : Nat := defaultLimitWindow
  maxKeys : Nat := maxTrackedKeys
deriving Inhabited

/-- The failures of one key in its window. -/
structure Counter where
  key : String
  start : Nat
  failures : Nat
deriving Inhabited

structure Failures where
  counters : Array Counter := #[]
deriving Inhabited

def Counter.live (l : Limits) (now : Nat) (c : Counter) : Bool := decide (now < c.start + l.window)

def Counter.blocked (l : Limits) (now : Nat) (c : Counter) : Bool :=
  c.live l now && decide (c.failures ≥ l.maxFailures)

def hexDigit? (c : Char) : Option Nat :=
  if c.isDigit then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c && c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

/-- One IPv6 group: one to four hexadecimal digits (lower case). -/
def hexGroup? (g : String) : Option Nat :=
  if g.isEmpty || g.length > 4 then none
  else g.foldl (fun acc c => acc.bind (fun n => (hexDigit? c).map (fun d => n * 16 + d))) (some 0)

/-- The eight groups of an IPv6 address in text form (RFC 4291 §2.2, forms 1
and 2; an address with an IPv4 tail other than `::ffff:` is `none`). -/
def ipv6Groups? (h : String) : Option (List Nat) :=
  let parts (t : String) : List String := if t.isEmpty then [] else t.splitOn ":"
  match h.splitOn "::" with
  | [a] => if (parts a).length == 8 then (parts a).mapM hexGroup? else none
  | [a, b] =>
    let n := (parts a).length + (parts b).length
    if n ≤ 7 then ((parts a) ++ List.replicate (8 - n) "0" ++ (parts b)).mapM hexGroup? else none
  | _ => none

/-- The part of a client address that a counter keys on: an IPv4 address
(also from `::ffff:a.b.c.d`), the /64 prefix of an IPv6 address, or the text
as given when it is neither. -/
def clientPrefix (addr : String) : String :=
  let h := (if addr.startsWith "[" && addr.endsWith "]" then ((addr.drop 1).dropEnd 1).toString else addr).toLower
  let v4 := if h.startsWith "::ffff:" then (h.drop 7).toString else h
  if (ipv4Parts? v4).isSome then v4
  else match ipv6Groups? h with
    | some gs => ":".intercalate ((gs.take 4).map (fun g => String.ofList (Nat.toDigits 16 g))) ++ "::/64"
    | none => h

/-! ## The address tag -/

/-- The tag of a client address under the host's key: lower-case hexadecimal
of HMAC-SHA-256(key, `clientPrefix address`), or `""` when there is no
address. A host that logs a connection logs a prefix of this, never the
address. -/
def addressTag (key : ByteArray) (address : String) : String :=
  let p := clientPrefix address
  if address.isEmpty || p.isEmpty then "" else L4Factoidal.Crypto.bytesToHex (L4Factoidal.Crypto.hmacSha256 key p.toUTF8)

/-- Two addresses with one prefix (one IPv4 address, one IPv6 /64) have one
tag: the grouping is `clientPrefix`'s, and the tag adds none of its own. -/
theorem addressTag_prefix (key : ByteArray) (a b : String) (ha : a.isEmpty = false)
    (hb : b.isEmpty = false) (h : clientPrefix a = clientPrefix b) :
    addressTag key a = addressTag key b := by
  simp only [addressTag, h, ha, hb]

/-- No address, no tag: a session with no address counts per account only. -/
theorem addressTag_empty (key : ByteArray) : addressTag key "" = "" := by
  simp [addressTag]

/-! ## The requester (invariant I2) -/

/-- Who sent a login attempt, as its transport authenticated it. -/
inductive Requester where
  /-- A TCP client: its address as the socket gives it. -/
  | tcp (address : String)
  /-- An XMPP sender: its bare JID, from the `from` the server stamps. -/
  | xmpp (bareJid : String)
deriving Inhabited, DecidableEq, Repr

/-- The prefix of a requester's key; one per transport. -/
def Requester.kindPrefix : Requester → String
  | .tcp _ => "address:"
  | .xmpp _ => "jid:"

/-- The part of a requester's key after its prefix. -/
def Requester.part : Requester → String
  | .tcp a => clientPrefix a
  | .xmpp j => j

/-- A requester the limit can count against: the part is not empty. -/
def Requester.valid (q : Requester) : Bool := !q.part.isEmpty

/-- The key of a requester. -/
def requesterKey (q : Requester) : String := q.kindPrefix ++ q.part

/-- The two keys of a login attempt: the user name as sent, and the
requester. -/
def loginKeys (user : String) (q : Requester) : List String :=
  ["name:" ++ user, requesterKey q]

/-- A TCP key never equals an XMPP key: the prefixes differ in the first
character. -/
theorem requesterKey_injective_kind (a j : String) :
    requesterKey (.tcp a) ≠ requesterKey (.xmpp j) := by
  intro h
  have h2 := congrArg (fun s => s.toList.head?) h
  simp [requesterKey, Requester.kindPrefix, Requester.part] at h2

/-- Two XMPP requesters with one key are one bare JID. -/
theorem requesterKey_xmpp_injective (j j' : String)
    (h : requesterKey (.xmpp j) = requesterKey (.xmpp j')) : j = j' := by
  simp only [requesterKey, Requester.kindPrefix, Requester.part] at h
  have h2 := congrArg String.toList h
  simp only [String.toList_append] at h2
  exact String.toList_inj.mp (List.append_cancel_left h2)

/-- A key is its transport's prefix and then the requester's part; for a
valid requester the key is longer than its prefix (the requester's part is
not empty). -/
theorem requesterKey_length (q : Requester) (h : q.valid = true) :
    (requesterKey q).length > q.kindPrefix.length := by
  have hp : q.part ≠ "" := by
    simp only [Requester.valid, Bool.not_eq_true', String.isEmpty_eq_false_iff] at h
    exact h
  have hl : q.part.length > 0 := by
    rcases Nat.eq_zero_or_pos q.part.length with h0 | h0
    · exact absurd (String.length_eq_zero_iff.mp h0) hp
    · exact h0
  simp only [requesterKey, String.length_append]
  omega

/-- Every key of a login attempt by a valid requester is longer than its
prefix: the name key holds `name:` and the user name; the requester key
holds a part that is not empty. So no attempt counts against the bare
prefix `address:` or `jid:`. -/
theorem loginKeys_nonempty (u : String) (q : Requester) (h : q.valid = true) :
    ∀ k ∈ loginKeys u q, k = "name:" ++ u ∨ (k = requesterKey q ∧ k.length > q.kindPrefix.length) := by
  intro k hk
  simp only [loginKeys, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with hk | hk
  · exact Or.inl hk
  · exact Or.inr ⟨hk, hk ▸ requesterKey_length q h⟩

/-! ## The counters -/

def Failures.blocked (l : Limits) (f : Failures) (now : Nat) (k : String) : Bool :=
  f.counters.any (fun c => c.key == k && c.blocked l now)

/-- The seconds until the last blocked window of `keys` ends (at least 1). -/
def Failures.retryAfter (l : Limits) (f : Failures) (now : Nat) (keys : List String) : Nat :=
  max 1 (f.counters.foldl (fun acc c =>
    if keys.contains c.key && c.blocked l now then max acc (c.start + l.window - now) else acc) 0)

/-- The seconds until the first live window ends (at least 1). -/
def Failures.soonest (l : Limits) (f : Failures) (now : Nat) : Nat :=
  max 1 (f.counters.foldl (fun acc c =>
    if c.live l now then
      (if acc == 0 then c.start + l.window - now else min acc (c.start + l.window - now))
    else acc) 0)

/-- How many new counters fit: free places, plus live counters that are not
blocked and are not in `keep`. -/
def Failures.room (l : Limits) (f : Failures) (now : Nat) (keep : List String) : Nat :=
  let live := f.counters.filter (·.live l now)
  (l.maxKeys - live.size) + (live.filter (fun c => !c.blocked l now && !keep.contains c.key)).size

/-- `some seconds` when an attempt with these keys is refused before any
password check: a key is blocked, or the keys that have no counter would
not fit. -/
def Failures.check (l : Limits) (f : Failures) (now : Nat) (keys : List String) : Option Nat :=
  if !l.enabled then none
  else if keys.any (f.blocked l now) then some (f.retryAfter l now keys)
  else
    let untracked := keys.filter (fun k => !f.counters.any (fun c => c.key == k && c.live l now))
    if f.room l now keys < untracked.length then some (f.soonest l now) else none

/-- The index of the counter to evict: the oldest window that is not
blocked and not one of `keep`. -/
def evictable (l : Limits) (now : Nat) (keep : List String) (cs : Array Counter) : Option Nat := Id.run do
  let mut best : Option (Nat × Nat) := none
  for i in [0:cs.size] do
    let c := cs[i]!
    if !c.blocked l now && !keep.contains c.key then
      match best with
      | some (_, s) => if c.start < s then best := some (i, c.start)
      | none => best := some (i, c.start)
  return best.map (·.1)

/-- One failure for each of `keys`: expired counters dropped, live ones
counted up, a new counter for a key that has none. -/
def Failures.record (l : Limits) (f : Failures) (now : Nat) (keys : List String) : Failures := Id.run do
  if !l.enabled then return f
  let mut cs := f.counters.filter (·.live l now)
  for k in keys do
    match cs.findIdx? (·.key == k) with
    | some i => cs := cs.modify i (fun c => { c with failures := c.failures + 1 })
    | none =>
      if cs.size ≥ l.maxKeys then
        match evictable l now keys cs with
        | some i => cs := cs.eraseIdxIfInBounds i
        | none => pure ()
      if cs.size < l.maxKeys then cs := cs.push { key := k, start := now, failures := 1 }
  return { counters := cs }

/-- With the limit on, a blocked key among the attempt's keys makes the
check refuse. -/
theorem check_blocked (l : Limits) (f : Failures) (now : Nat) (keys : List String) (k : String)
    (he : l.enabled = true) (hk : k ∈ keys) (hb : f.blocked l now k = true) :
    (f.check l now keys).isSome = true := by
  have hany : keys.any (f.blocked l now) = true := List.any_eq_true.mpr ⟨k, hk, hb⟩
  simp [Failures.check, he, hany]

/-- With the limit off, the check never refuses. -/
theorem check_disabled (l : Limits) (f : Failures) (now : Nat) (keys : List String)
    (he : l.enabled = false) : f.check l now keys = none := by
  simp [Failures.check, he]

/-! ## Checks -/

#guard requesterKey (.tcp "10.0.0.1") == "address:10.0.0.1"
#guard requesterKey (.tcp "2001:db8:1:2:3:4:5:6") == "address:2001:db8:1:2::/64"
#guard requesterKey (.xmpp "alice@example.org") == "jid:alice@example.org"
#guard (Requester.tcp "").valid == false && (Requester.xmpp "").valid == false
#guard (Requester.tcp "[]").valid == false
#guard (Requester.xmpp "alice@example.org").valid && (Requester.tcp "::1").valid
#guard loginKeys "alice" (.xmpp "carol@example.org") == ["name:alice", "jid:carol@example.org"]
-- A JID that looks like an address keys apart from that address.
#guard requesterKey (.xmpp "10.0.0.1") != requesterKey (.tcp "10.0.0.1")

-- The failures of JID A do not block JID B for another name; one JID that
-- tries many names is blocked by its own key.
def lDefault : Limits := {}
def failMany (f : Failures) (keys : Nat → List String) (n t0 : Nat) : Failures := Id.run do
  let mut f := f
  for i in [0:n] do
    f := f.record lDefault (t0 + i) (keys i)
  return f
def jidA : Requester := .xmpp "a@example.org"
def jidB : Requester := .xmpp "b@example.org"
-- Five failures for alice from JID A: bob from JID B is not refused.
#guard (failMany {} (fun _ => loginKeys "alice" jidA) 5 100).check lDefault 105 (loginKeys "bob" jidB) == none
-- ... alice is refused from JID B too (the name key), and JID A for bob.
#guard (failMany {} (fun _ => loginKeys "alice" jidA) 5 100).check lDefault 105 (loginKeys "alice" jidB) == some 55
#guard (failMany {} (fun _ => loginKeys "alice" jidA) 5 100).check lDefault 105 (loginKeys "bob" jidA) == some 55
-- Five names from JID A, one failure each: the sixth name is refused.
#guard (failMany {} (fun i => loginKeys s!"user{i}" jidA) 5 100).check lDefault 105 (loginKeys "user5" jidA) == some 55
#guard (failMany {} (fun i => loginKeys s!"user{i}" jidA) 5 100).check lDefault 105 (loginKeys "user5" jidB) == none

-- The tag: one per IPv4 address and per IPv6 /64, 64 hexadecimal digits,
-- and a tag reads as itself where a requester key is made.
def tagKey : ByteArray := "test key, not a secret".toUTF8
#guard (addressTag tagKey "2001:db8:1:2:3:4:5:6") == addressTag tagKey "2001:db8:1:2:ffff:4:5:7"
#guard (addressTag tagKey "2001:db8:1:2:3:4:5:6") != addressTag tagKey "2001:db8:1:3:3:4:5:6"
#guard (addressTag tagKey "203.0.113.7") == addressTag tagKey "::ffff:203.0.113.7"
#guard (addressTag tagKey "203.0.113.7") != addressTag tagKey "203.0.113.8"
#guard (addressTag tagKey "203.0.113.7") != addressTag "another key".toUTF8 "203.0.113.7"
#guard (addressTag tagKey "203.0.113.7").length == 64
#guard addressTag tagKey "" == ""
#guard clientPrefix (addressTag tagKey "203.0.113.7") == addressTag tagKey "203.0.113.7"
#guard requesterKey (.tcp (addressTag tagKey "203.0.113.7")) == "address:" ++ addressTag tagKey "203.0.113.7"
-- RFC 4231 test case 2 through this path: the tag is HMAC-SHA-256 itself.
#guard L4Factoidal.Crypto.bytesToHex (L4Factoidal.Crypto.hmacSha256 "Jefe".toUTF8 "what do ya want for nothing?".toUTF8)
  == "5bdcc146bf60754e6a042426089575c75a003f089d2739839dec58b964ec3843"

end L4Factoidal.Net.LoginLimit
