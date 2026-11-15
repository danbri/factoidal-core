module

public import Veil

/-!
# HTTP connections: reuse, pipelining limits, multiplexed streams

What exists today: the engine decides each request (`formal/lean4/L4Factoidal/Net/PageFetch.lean`:
origin, CORS, redirects, the address of a name), and the desktop host moves the bytes
(`labs/demos/foafnaut/native_net.ts`): one `NetWire {id, …}` in, one `NetAnswer {id, …}` out, a
new client per request, connected to the address the engine pinned (no second DNS answer can
move a request). There is no connection pool and no HTTP/2 in our code today; Deno's client
speaks the protocol.

This model is the contract a pool must keep when one is added (in the host, or in Lean), and the
one the `id` pairing of the wire already keeps:

- A connection is opened for one pool key: origin, network partition (the top-level site the
  request is made for) and the address the engine pinned. It carries only requests with the
  same key, so a connection is never reused across origins, partitions or addresses.
- A connection carries at most `maxStreams` requests at a time (HTTP/1.1 without pipelining:
  1; HTTP/2: the peer's SETTINGS_MAX_CONCURRENT_STREAMS), and a request is on one connection.
- A response is delivered only to the request that owns it: the request that was sent on that
  connection with that stream.
- Closing a connection fails the requests still on it; none of them is delivered later.
- Flow control (HTTP/2): DATA received on a connection never exceeds the window the client
  granted (`window`), and the window is replenished only by the client.

Invariants proved by `#check_invariants` with SMT proof reconstruction (`veil.smt.trust false`);
`#model_check` on a small instance is test evidence only.
-/

set_option veil.smt.trust false

veil module HttpConnections

type conn
type req
type origin
type partition
type address

immutable individual maxStreams : Nat
/- The initial flow-control window of a connection, in units (one unit: one DATA frame's worth). -/
immutable individual initWindow : Nat
immutable function reqOrigin : req → origin
immutable function reqPartition : req → partition
immutable function reqAddress : req → address

relation opened : conn → Bool
relation closed : conn → Bool
function connOrigin : conn → origin
function connPartition : conn → partition
function connAddress : conn → address
/- `onConn r c`: request `r` was sent on connection `c` and has no answer yet. -/
relation onConn : req → conn → Bool
function streams : conn → Nat
/- `responseFor c r`: a response arrived on `c` on the stream of request `r`. -/
relation responseFor : conn → req → Bool
relation sent : req → Bool
relation delivered : req → Bool
relation failed : req → Bool
/- HTTP/2 flow control: bytes the client still allows the server to send on `c`. -/
function window : conn → Nat
/- Bytes received on `c` minus window updates the client sent, for the ghost check. -/
function received : conn → Nat
function granted : conn → Nat

#gen_state

assumption [some_stream] maxStreams ≥ 1

after_init {
  opened C := false
  closed C := false
  onConn R C := false
  streams C := 0
  responseFor C R := false
  sent R := false
  delivered R := false
  failed R := false
  window C := 0
  received C := 0
  granted C := 0
}

/- Open a fresh connection for the pool key of request `r`, with the initial window. -/
action openFor (c : conn) (r : req) {
  require ¬ opened c
  opened c := true
  connOrigin c := reqOrigin r
  connPartition c := reqPartition r
  connAddress c := reqAddress r
  window c := initWindow
  granted c := initWindow
}

/- Send a request on an open connection of its own pool key with a free stream. -/
action send (r : req) (c : conn) {
  require opened c ∧ ¬ closed c
  require ¬ sent r
  require connOrigin c = reqOrigin r ∧ connPartition c = reqPartition r
  require connAddress c = reqAddress r
  require streams c < maxStreams
  sent r := true
  onConn r c := true
  streams c := streams c + 1
}

/- The server sends one unit of DATA on `c` for request `r`'s stream, within the window. -/
action data (c : conn) (r : req) {
  require onConn r c
  require window c > 0
  window c := window c - 1
  received c := received c + 1
}

/- The client grants one more unit on `c` (WINDOW_UPDATE). -/
action windowUpdate (c : conn) {
  require opened c ∧ ¬ closed c
  window c := window c + 1
  granted c := granted c + 1
}

/- The response headers and end of stream for request `r` arrive on `c`. -/
action respond (c : conn) (r : req) {
  require onConn r c
  responseFor c r := true
}

/- The engine is given the response that arrived on `c` for `r`; the stream is free again. -/
action deliver (c : conn) (r : req) {
  require responseFor c r
  require onConn r c
  delivered r := true
  responseFor c r := false
  onConn r c := false
  streams c := streams c - 1
}

/- A connection closes (by either side, or an error): its unanswered requests fail. -/
action close (c : conn) {
  require opened c ∧ ¬ closed c
  closed c := true
  failed R := failed R ∨ onConn R c
  onConn R c := false
  responseFor c R := false
  streams c := 0
}

-- A response reaches only the request that owns it.
safety [owner_only] responseFor C R → onConn R C
safety [deliver_once] delivered R → ¬ onConn R C
-- No reuse across origins, partitions or pinned addresses.
safety [same_key]
  onConn R C → connOrigin C = reqOrigin R ∧ connPartition C = reqPartition R ∧
    connAddress C = reqAddress R
-- A request is on one connection; only open connections carry requests.
safety [one_conn] onConn R C ∧ onConn R D → C = D
invariant [on_open] onConn R C → opened C ∧ ¬ closed C ∧ sent R
-- A failed request is never delivered later.
safety [failed_final] failed R → ¬ onConn R C
-- Bounded streams per connection.
safety [streams_bounded] streams C ≤ maxStreams
-- Flow control: never more DATA than the client granted.
safety [flow_control] received C + window C = granted C
invariant [delivered_sent] delivered R → sent R
invariant [failed_sent] failed R → sent R
invariant [unopened_empty] ¬ opened C → received C = 0 ∧ window C = 0 ∧ granted C = 0
invariant [closed_opened] closed C → opened C

-- Model checking only: a small instance with bounded byte counts.
state_constraint [small] granted C ≤ 2

#gen_spec

#check_invariants

#gen_theorems

#model_check { conn := Fin 2, req := Fin 2, origin := Fin 2, partition := Fin 1, address := Fin 1 }
  { maxStreams := 1, initWindow := 1, reqOrigin := fun r => r, reqPartition := fun _ => 0, reqAddress := fun _ => 0 }

end HttpConnections
