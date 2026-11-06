/-
L4Factoidal.Net.Egress — the one decision for an outbound request whose URL
a remote party can choose: may this server connect to this host, and to
which address (https://github.com/danbri/factoidal/issues/1126; invariant
I5 and row C5 of
`docs/designissues/2026-10-28-feature-combination-safety.md`).

Users: the authorization server fetch (`L4Factoidal.Authz.Fetch`, subject
`sub`, OpenID Connect discovery, `jwks_uri`), CID retrieval
(`L4Factoidal.CID.Fetch`), and every LWS delivery: webhook inboxes,
access-request and access-grant inboxes, the controller inbox
(`L4Factoidal.LWS.Notifications.egressOf`, wasm op `lwsEgress`).

## The rules

* The engine knows every address of the host before the request. An IP
  literal is its own address. A name is resolved BY THE HOST, which passes
  back every address it got. A `localhost` name (RFC 6761 §6.3) is refused
  without `allowPrivate`, whatever the resolution says.
* Unless `allowPrivate` is set, the request is refused when ANY address is
  special-purpose (`specialPurpose`). One special address among public
  ones refuses the host: the host's resolver may give any of them.
* The answer names the address to connect to. The host connects to that
  address and does not resolve the name again, so a second answer from a
  name server (DNS rebinding) cannot move the request.

## Special-purpose addresses (`specialPurpose`)

IPv4: every block of the IANA IPv4 Special-Purpose Address Registry
(https://www.iana.org/assignments/iana-ipv4-special-registry/), also the
blocks that the registry marks "Globally Reachable", because no inbox or
subject document is served from them: 0.0.0.0/8, 10.0.0.0/8,
100.64.0.0/10, 127.0.0.0/8, 169.254.0.0/16, 172.16.0.0/12, 192.0.0.0/24,
192.0.2.0/24, 192.31.196.0/24, 192.52.193.0/24, 192.88.99.0/24,
192.168.0.0/16, 192.175.48.0/24, 198.18.0.0/15, 198.51.100.0/24,
203.0.113.0/24, 240.0.0.0/4 (with 255.255.255.255). Also 224.0.0.0/4,
multicast (IANA IPv4 Multicast Address Space Registry,
https://www.iana.org/assignments/multicast-addresses/).

IPv6: every address outside 2000::/3, the global unicast space of the IANA
IPv6 Address Space registry
(https://www.iana.org/assignments/ipv6-address-space/). That covers ::/128,
::1/128, the IPv4-compatible and IPv4-mapped forms (::ffff:0:0/96 is read as
its IPv4 address by `addr?`), 64:ff9b:1::/48, 100::/64, 100:0:0:1::/64,
5f00::/16, fc00::/7, fe80::/10, fec0::/10 and ff00::/8. Inside 2000::/3,
the blocks of the IANA IPv6 Special-Purpose Address Registry
(https://www.iana.org/assignments/iana-ipv6-special-registry/): 2001::/23,
2001:db8::/32, 2620:4f:8000::/48, 3fff::/20. Two translation prefixes are
judged by the IPv4 address they carry: 64:ff9b::/96 (RFC 6052, NAT64) and
2002::/16 (RFC 3056, 6to4).
-/
import L4Factoidal.Net.Addr

namespace L4Factoidal.Net

/-! ## Special-purpose addresses -/

/-- An IPv4 address (four octets) in a special-purpose block. Any other
number of octets is special: it is no address this module can check. -/
def specialV4 : List Nat → Bool
  | [a, b, c, _] =>
      a == 0 || a == 10 || (a == 100 && 64 ≤ b && b ≤ 127) || a == 127 ||
      (a == 169 && b == 254) || (a == 172 && 16 ≤ b && b ≤ 31) ||
      (a == 192 && b == 0 && c == 0) || (a == 192 && b == 0 && c == 2) ||
      (a == 192 && b == 31 && c == 196) || (a == 192 && b == 52 && c == 193) ||
      (a == 192 && b == 88 && c == 99) || (a == 192 && b == 168) ||
      (a == 192 && b == 175 && c == 48) || (a == 198 && (b == 18 || b == 19)) ||
      (a == 198 && b == 51 && c == 100) || (a == 203 && b == 0 && c == 113) ||
      224 ≤ a
  | _ => true

/-- The IPv4 address carried by a 16-bit group pair. -/
def v4OfGroups (hi lo : Nat) : List Nat := [hi / 256, hi % 256, lo / 256, lo % 256]

/-- The IPv4 address embedded in an IPv6 address of a translation prefix:
64:ff9b::/96 (RFC 6052 §2.1, the last 32 bits) and 2002::/16 (RFC 3056 §2,
bits 16 to 47). -/
def embeddedV4? : List Nat → Option (List Nat)
  | [0x64, 0xff9b, 0, 0, 0, 0, hi, lo] => some (v4OfGroups hi lo)
  | 0x2002 :: hi :: lo :: _ => some (v4OfGroups hi lo)
  | _ => none

/-- An IPv6 address (eight groups) in a special-purpose block; a
translation prefix is judged by its embedded IPv4 address. -/
def specialV6 (gs : List Nat) : Bool :=
  if gs.length != 8 then true else
  match embeddedV4? gs with
  | some v4 => specialV4 v4
  | none =>
      let g0 := gs.headD 0
      let g1 := (gs.drop 1).headD 0
      let g2 := (gs.drop 2).headD 0
      -- outside 2000::/3, the global unicast space
      g0 / 0x2000 != 1 ||
      (g0 == 0x2001 && g1 < 0x200) ||                -- 2001::/23
      (g0 == 0x2001 && g1 == 0xdb8) ||               -- 2001:db8::/32
      (g0 == 0x2620 && g1 == 0x4f && g2 == 0x8000) ||  -- 2620:4f:8000::/48
      (g0 == 0x3fff && g1 < 0x1000)                  -- 3fff::/20

/-- **Special-purpose address**: one this server does not connect to for a
URL a remote party chose, unless the operator opts in. -/
def specialPurpose : Addr → Bool
  | .v4 os => specialV4 os
  | .v6 gs => specialV6 gs

/-! ## The decision -/

/-- The egress policy of one server. `allowPrivate` is the operator's
opt-in (`--allow-private-fetch`); off by default. -/
structure EgressPolicy where
  allowPrivate : Bool := false
  deriving Repr, Inhabited, BEq, DecidableEq

/-- May the server connect to these addresses? -/
def addressesAllowed (p : EgressPolicy) (as : List Addr) : Bool :=
  p.allowPrivate || !(as.any specialPurpose)

/-- **The decision** for the addresses `texts` of `host`: the address to
connect to, or the refusal. -/
def choose (p : EgressPolicy) (host : String) (texts : List String) : Except String String :=
  let parsed := texts.filterMap addr?
  if localhostName host && !p.allowPrivate then
    .error s!"{host} is a localhost name; connecting to it is refused (--allow-private-fetch)"
  else if parsed.isEmpty then .error s!"{host} did not resolve to an address"
  else if !addressesAllowed p parsed then
    .error s!"{host} resolves to a special-purpose address (loopback, private, link-local, shared, multicast, reserved or documentation); connecting to it is refused (--allow-private-fetch)"
  else match texts.find? (fun t => (addr? t).isSome) with
    | some a => .ok a
    | none => .error s!"{host} did not resolve to an address"

/-- The address texts that stand for `host`: the host itself when it is an
IP literal (without brackets), otherwise the texts the host resolved. -/
def candidates (host : String) (resolved : List String) : List String :=
  match addr? host with
  | some _ => [if host.startsWith "[" then ((host.drop 1).dropEnd 1).toString else host]
  | none => resolved

/-- The decision for a URL: its host, and `choose` over its candidates.
`resolved` is what the host's resolver gave for the name now; it is not
read for an IP literal. -/
def target (p : EgressPolicy) (url : String) (resolved : List String) :
    Except String (String × String) :=
  match authority? url with
  | none => .error s!"{url} is not an http or https URL with a host"
  | some (host, _) =>
      match choose p host (candidates host resolved) with
      | .ok a => .ok (host, a)
      | .error w => .error w

/-- The name the host must resolve before `target` can decide: the host of
the URL when it is not an IP literal. -/
def toResolve? (url : String) : Option String :=
  match authority? url with
  | some (h, _) => if (addr? h).isSome then none else some h
  | none => none

/-! ## Theorems -/

/-- **The guard (I5).** Without `allowPrivate`, a host with a
special-purpose address among its addresses is never connected to. -/
theorem egress_refuses_special {p : EgressPolicy} {host : String} {texts : List String}
    {a : Addr} (hp : p.allowPrivate = false) (ha : a ∈ texts.filterMap addr?)
    (hs : specialPurpose a = true) (x : String) : choose p host texts ≠ .ok x := by
  unfold choose
  have hany : (texts.filterMap addr?).any specialPurpose = true :=
    List.any_eq_true.mpr ⟨a, ha, hs⟩
  simp only [hp]
  split
  · simp
  · split
    · simp
    · simp [addressesAllowed, hp, hany]

/-- Without `allowPrivate`, a localhost name is never connected to. -/
theorem egress_refuses_localhost {p : EgressPolicy} {host : String} {texts : List String}
    (hp : p.allowPrivate = false) (hl : localhostName host = true) (x : String) :
    choose p host texts ≠ .ok x := by
  unfold choose
  simp [hp, hl]

/-- **The chosen address is one of the addresses given**, and it reads as an
IP literal: the host connects to an address the decision saw. -/
theorem choose_mem {p : EgressPolicy} {host : String} {texts : List String} {x : String}
    (h : choose p host texts = .ok x) : x ∈ texts ∧ (addr? x).isSome := by
  have hf : texts.find? (fun t => (addr? t).isSome) = some x := by
    unfold choose at h
    cases hf : texts.find? (fun t => (addr? t).isSome) with
    | none =>
        simp only [hf] at h
        split at h <;> (try split at h) <;> (try split at h) <;> simp at h
    | some a =>
        simp only [hf] at h
        split at h <;> (try split at h) <;> (try split at h) <;> simp_all
  exact ⟨List.mem_of_find?_eq_some hf, by simpa using List.find?_some hf⟩

/-- `target` is `choose` on the URL's host: the address it names is what
`choose` gave for that host and those candidates. -/
theorem target_choose {p : EgressPolicy} {url : String} {resolved : List String}
    {host a : String} (h : target p url resolved = .ok (host, a)) :
    ∃ port, authority? url = some (host, port) ∧
      choose p host (candidates host resolved) = .ok a := by
  unfold target at h
  split at h
  · simp at h
  · rename_i h0 port hauth
    split at h
    · rename_i a' hc
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨port, hauth, hc⟩
    · simp at h

/-- Without `allowPrivate`, `target` never names an address when a
candidate address of the URL's host is special-purpose. -/
theorem target_refuses_special {p : EgressPolicy} {url : String} {resolved : List String}
    {host : String} {port : Nat} {a : Addr} (hp : p.allowPrivate = false)
    (hu : authority? url = some (host, port))
    (ha : a ∈ (candidates host resolved).filterMap addr?) (hs : specialPurpose a = true)
    (x : String × String) : target p url resolved ≠ .ok x := by
  intro h
  obtain ⟨host', a'⟩ := x
  obtain ⟨port', hu', hc⟩ := target_choose h
  rw [hu] at hu'
  simp only [Option.some.injEq, Prod.mk.injEq] at hu'
  obtain ⟨rfl, -⟩ := hu'
  exact egress_refuses_special hp ha hs a' hc

/-! ## Checks -/

#guard specialPurpose (.v4 [100, 64, 0, 1]) && specialPurpose (.v4 [100, 127, 255, 255])
#guard !specialPurpose (.v4 [100, 63, 0, 1]) && !specialPurpose (.v4 [100, 128, 0, 1])
#guard specialPurpose (.v4 [198, 18, 0, 1]) && specialPurpose (.v4 [198, 19, 255, 1])
#guard !specialPurpose (.v4 [198, 20, 0, 1])
#guard specialPurpose (.v4 [192, 0, 0, 8]) && specialPurpose (.v4 [224, 0, 0, 1])
#guard specialPurpose (.v4 [240, 0, 0, 1]) && specialPurpose (.v4 [255, 255, 255, 255])
#guard specialPurpose (.v4 [10, 0, 0, 1]) && specialPurpose (.v4 [172, 31, 0, 1])
#guard !specialPurpose (.v4 [172, 32, 0, 1]) && specialPurpose (.v4 [192, 168, 1, 1])
#guard specialPurpose (.v4 [127, 0, 0, 2]) && specialPurpose (.v4 [0, 0, 0, 0])
#guard specialPurpose (.v4 [169, 254, 169, 254]) && specialPurpose (.v4 [203, 0, 113, 7])
#guard !specialPurpose (.v4 [8, 8, 8, 8]) && !specialPurpose (.v4 [93, 184, 215, 14])
#guard specialPurpose (.v4 [1, 2, 3])
-- IPv6, through `addr?` so the text forms are covered.
private def sp (t : String) : Bool := ((addr? t).map specialPurpose).getD false
#guard sp "::1" && sp "::" && sp "fc00::1" && sp "fdff::1" && sp "fe80::1" && sp "febf::1"
#guard sp "fec0::1" && sp "feff::1" && sp "ff02::1" && sp "100::1" && sp "5f00::1"
#guard sp "2001:db8::1" && sp "2001::1" && sp "2001:1ff::1" && sp "3fff::1"
#guard sp "2620:4f:8000::1" && sp "64:ff9b:1::a00:1"
#guard !sp "2001:200::1" && !sp "2606:4700::1" && !sp "2a00:1450::1"
-- IPv4-mapped is read as IPv4.
#guard sp "::ffff:10.0.0.1" && !sp "::ffff:8.8.8.8"
-- NAT64 and 6to4 are judged by the IPv4 address they carry.
#guard sp "64:ff9b::10.0.0.1" && sp "64:ff9b::7f00:1" && !sp "64:ff9b::8.8.8.8"
#guard sp "2002:a00:1::1" && sp "2002:c0a8:101::1" && !sp "2002:808:808::1"

#guard (choose {} "h.example" ["93.184.215.14"]).toOption == some "93.184.215.14"
#guard (choose {} "h.example" ["93.184.215.14", "100.64.0.1"]).toOption == none
#guard (choose {} "100.64.0.1" ["100.64.0.1"]).toOption == none
#guard (choose { allowPrivate := true } "100.64.0.1" ["100.64.0.1"]).toOption == some "100.64.0.1"
#guard (choose {} "localhost" ["93.184.215.14"]).toOption == none
#guard (choose {} "h.example" []).toOption == none
#guard target {} "http://10.0.0.1/" [] |>.toOption |>.isNone
#guard target {} "http://[::1]:9/in" [] |>.toOption |>.isNone
#guard (target {} "https://h.example/in" ["93.184.215.14"]).toOption == some ("h.example", "93.184.215.14")
-- A literal's own address is used; what a resolver says is not read.
#guard (target {} "http://8.8.8.8/in" ["10.0.0.1"]).toOption == some ("8.8.8.8", "8.8.8.8")
#guard (target { allowPrivate := true } "http://127.0.0.1:9/in" []).toOption == some ("127.0.0.1", "127.0.0.1")
#guard toResolve? "https://h.example:8443/x" == some "h.example"
#guard toResolve? "http://10.0.0.1/" == none && toResolve? "http://[::1]/" == none

end L4Factoidal.Net
