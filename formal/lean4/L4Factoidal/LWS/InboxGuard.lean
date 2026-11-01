/-
L4Factoidal.LWS.InboxGuard — refuse a webhook inbox that names this server,
decided in Lean. https://github.com/danbri/factoidal/issues/915

Source: LWS 1.0 Notification Suite: Webhooks
(https://w3c.github.io/lws-protocol/lws10-notifications-webhook/,
w3c/lws-protocol 9a08ff65, 2026-10-19), "Security Considerations":
"Subscription Abuse: Rate limiting and endpoint verification are suggested
to prevent abuse of the subscription mechanism." The draft defines no
procedure for either; what follows is this server's choice.

## What is refused, and why

A delivery is a POST that this server makes to the inbox. When the inbox is
this server, the POST is a request to this server: to a container it
creates a resource, whose Create is delivered again (to a data resource it
answers 405, to a missing path 404, and creates nothing). `Notifications`
refused an inbox that is a container IRI below `baseIri`; with this module
it refuses the same container under every other name of this server:
another host name, an IP address, or `localhost` (`readSubRequest`). The
decision whether an inbox names this server (`loops`) compares the inbox
authority with:

* the authority of `baseIri` (host and port, the port by the scheme when it
  is absent);
* the address the host bound (`Config.listenAddress`, `listenPort`); when
  it is every interface (`0.0.0.0` or `::`), every address of the machine
  the host read (`Config.localAddresses`) and every loopback address.

The inbox host is an IP literal (IPv4 dotted decimal, or IPv6 in brackets,
IPv4-mapped IPv6 read as IPv4), or a name. For a name the HOST resolves it
(`resolve` in the wasm ABI: the engine names the host, the host passes the
addresses back in the request member `resolved`) and this module compares
the addresses; the host only passes data. `localhost` and the names below
`.localhost` are loopback names whatever the resolution gives (RFC 6761
§6.3: "Users are free to use localhost names as they would any other domain
names. [...] Name resolution APIs and libraries SHOULD recognize localhost
names as special and SHOULD always return the IP loopback address").

Every loopback address (127.0.0.0/8, `::1`) and the unspecified address
(`0.0.0.0`, `::`, which a connection reaches as this machine) is one
address here, so a server bound to `127.0.0.1` also refuses `127.0.0.2`
and `[::1]` at its port. A port is compared exactly: another server on the
same machine is a valid inbox.

## Limits, each a server choice

* The check runs when a subscription is made. Requests to private and other
  special-purpose addresses are a separate decision, made again just before
  each delivery with the addresses resolved then (`L4Factoidal.Net.Egress`,
  `Notifications.egressOf`, https://github.com/danbri/factoidal/issues/1126).
* A name that leads to this server only through a proxy, or through an
  address the host did not report, is not detected. Under authorization a
  delivery is an anonymous POST, which the access policy refuses unless it
  grants Append to the public.
-/
import L4Factoidal.LWS.Operations
import L4Factoidal.Net.Addr

namespace L4Factoidal.LWS.InboxGuard

open L4Factoidal.LWS

/-! ## IP literals and authorities

Moved to `L4Factoidal.Net.Addr` (issue 1126), so that `L4Factoidal.Net.Egress`
and every fetching surface read addresses the same way. The names stay
reachable here. -/

export L4Factoidal.Net (octet? ipv4? hexGroup? groups? ipv6? Addr addr? authority? localhostName)

/-- A loopback address (127.0.0.0/8, `::1`) or the unspecified address
(`0.0.0.0`, `::`): this machine. -/
def thisMachine : Addr → Bool
  | .v4 (127 :: _) => true
  | .v4 [0, 0, 0, 0] => true
  | .v6 gs => gs == [0, 0, 0, 0, 0, 0, 0, 1] || gs == [0, 0, 0, 0, 0, 0, 0, 0]
  | _ => false

/-- The unspecified address: a socket bound to every interface. -/
def unspecified : Addr → Bool
  | .v4 [0, 0, 0, 0] => true
  | .v6 gs => gs == [0, 0, 0, 0, 0, 0, 0, 0]
  | _ => false

/-- Is the inbox address `x` the bound address `b` (with the machine's
addresses `locals` for a socket bound to every interface)? -/
def sameAddr (locals : List Addr) (b x : Addr) : Bool :=
  b == x || (thisMachine b && thisMachine x) || (unspecified b && (thisMachine x || locals.contains x))

/-- The addresses an inbox host stands for: itself when it is an IP literal;
otherwise what the host resolved for it, and the loopback addresses for a
localhost name. -/
def addressesOf (cfg : Config) (h : String) : List Addr :=
  match addr? h with
  | some a => [a]
  | none =>
      ((cfg.resolved.lookup h).getD []).filterMap addr? ++
      (if localhostName h then [.v4 [127, 0, 0, 1], .v6 [0, 0, 0, 0, 0, 0, 0, 1]] else [])

/-- The endpoints of this server: (address, port) pairs, from `baseIri` when
its host is an IP literal or a localhost name, and from the bound address. -/
def selfEndpoints (cfg : Config) : List (Addr × Nat) :=
  let fromBase := match authority? cfg.baseIri with
    | some (h, p) =>
        (match addr? h with
         | some a => [a]
         | none => if localhostName h then [.v4 [127, 0, 0, 1]] else []).map (·, p)
    | none => []
  let fromListen := match cfg.listenAddress.bind addr?, cfg.listenPort with
    | some a, some p => [(a, p)]
    | _, _ => []
  fromBase ++ fromListen

/-- **Does the inbox name this server?** Its authority is `baseIri`'s, or one
of its addresses at its port is an endpoint of this server. -/
def loops (cfg : Config) (inbox : String) : Bool :=
  match authority? inbox with
  | none => false
  | some (h, p) =>
      (authority? cfg.baseIri == some (h, p)) ||
      let locals := cfg.localAddresses.filterMap addr?
      (addressesOf cfg h).any (fun x =>
        (selfEndpoints cfg).any (fun (b, bp) => bp == p && sameAddr locals b x))

/-- The inbox host the engine needs resolved before it can decide `loops`:
a name, not `baseIri`'s host, that the request did not resolve. -/
def toResolve? (cfg : Config) (inbox : String) : Option String :=
  match authority? inbox with
  | none => none
  | some (h, p) =>
      if (addr? h).isSome || authority? cfg.baseIri == some (h, p) ||
        (cfg.resolved.lookup h).isSome then none
      else some h

/-! ## Checks -/

#guard ipv4? "127.0.0.1" == some [127, 0, 0, 1]
#guard ipv4? "127.0.0.01" == none && ipv4? "256.0.0.1" == none && ipv4? "1.2.3" == none
#guard ipv6? "::1" == some [0, 0, 0, 0, 0, 0, 0, 1]
#guard ipv6? "fe80::1%eth0" == some [0xfe80, 0, 0, 0, 0, 0, 0, 1]
#guard ipv6? "1:2:3:4:5:6:7:8" == some [1, 2, 3, 4, 5, 6, 7, 8]
#guard ipv6? "1:2:3:4:5:6:7:8:9" == none && ipv6? "1::2::3" == none && ipv6? "g::" == none
#guard addr? "[::ffff:127.0.0.1]" == some (.v4 [127, 0, 0, 1])
#guard addr? "::" == some (.v6 [0, 0, 0, 0, 0, 0, 0, 0])
#guard addr? "example.org" == none
#guard authority? "http://LocalHost.:8080/x" == some ("localhost", 8080)
#guard authority? "https://[::1]/hook" == some ("::1", 443)
#guard authority? "http://user@127.0.0.1:9/" == some ("127.0.0.1", 9)
#guard authority? "ftp://h/" == none

private def c0 : Config :=
  { baseIri := "http://127.0.0.1:3000/", listenAddress := some "127.0.0.1", listenPort := some 3000 }

-- Positive: this server by its base authority, another loopback address,
-- `localhost`, IPv6 loopback, an IPv4-mapped address, a resolved name.
#guard loops c0 "http://127.0.0.1:3000/hook"
#guard loops c0 "http://127.0.0.2:3000/hook"
#guard loops c0 "http://localhost:3000/hook"
#guard loops c0 "http://sub.localhost:3000/hook"
#guard loops c0 "http://[::1]:3000/hook"
#guard loops c0 "http://[::ffff:127.0.0.1]:3000/hook"
#guard loops { c0 with resolved := [("pod.test", ["127.0.0.1"])] } "http://pod.test:3000/hook"
#guard loops { baseIri := "https://pod.example/" } "https://POD.example:443/inbox/"
-- A server bound to every interface: each interface address at its port.
#guard loops { baseIri := "https://pod.example/", listenAddress := some "0.0.0.0", listenPort := some 8443,
               localAddresses := ["10.1.2.3", "fe80::1"] } "http://10.1.2.3:8443/h"
#guard loops { baseIri := "https://pod.example/", listenAddress := some "::", listenPort := some 8443,
               localAddresses := [] } "http://[::1]:8443/h"
-- Negative: another port of this machine, another host, a resolved name
-- elsewhere, an unresolved name, an interface address when bound to loopback.
#guard !loops c0 "http://127.0.0.1:3001/hook"
#guard !loops c0 "http://localhost:3001/hook"
#guard !loops c0 "https://hook.example/in"
#guard !loops { c0 with resolved := [("hook.example", ["192.0.2.7"])] } "http://hook.example:3000/in"
#guard !loops c0 "http://hook.example:3000/in"
#guard !loops { c0 with localAddresses := ["10.1.2.3"] } "http://10.1.2.3:3000/h"
#guard !loops c0 "mailto:x@example.org"
-- What the engine asks the host to resolve: names only, once.
#guard toResolve? c0 "http://hook.example:3000/in" == some "hook.example"
#guard toResolve? c0 "http://localhost:3000/in" == some "localhost"
#guard toResolve? c0 "http://127.0.0.1:9/in" == none
#guard toResolve? { c0 with resolved := [("hook.example", [])] } "http://hook.example/in" == none
#guard toResolve? { baseIri := "https://pod.example/" } "https://pod.example/in" == none

end L4Factoidal.LWS.InboxGuard
