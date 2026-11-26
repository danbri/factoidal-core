/-
L4Factoidal.Net.Socks5 — the decisions of the SOCKS5 server that sits in front
of the Tor streams of the Foafnaut Tor worker (RFC 1928, with username/password
authentication by RFC 1929).

EXPERIMENTAL UNDER-REVIEWED CODE - USE WITH CARE - DO NOT CREATE PUBLIC SERVICES
USING THIS WITHOUT CAREFUL INDEPENDENT EXPERT REVIEW.

Source of the rules: `labs/demos/foafnaut/tor-wasm/deno/socks5.ts` (function
`serveOne`), section 18 of
`docs/designissues/2026-11-25-foafnaut-tor-onion-routing.md`. This module makes
the same decisions; a later change makes the TypeScript call it and keep only
byte I/O.

The decision is one pure function over the whole handshake prefix that the
server has received, `handshake (s : Session) (input : List UInt8) : Outcome`.
The host calls it after each read and acts on the result:

* `Outcome.sent`: every byte the server writes for this prefix, from the start
  of the connection. The host writes the part that it has not written yet.
* `Outcome.verdict`:
  - `needMore`: read more bytes;
  - `refuse why`: write `sent`, record `why`, close;
  - `proxyCheck host port`: write `sent`, record the target, close (the user
    name was `foafnaut-proxy-check`; no stream is opened);
  - `connect partition host port consumed`: open a Tor stream for
    `partition`, then write `replyBytes rep` with the result of the open; the
    bytes after the first `consumed` input bytes are early client data.

Rules (the same as `serveOne`, in its order):

1. Greeting `VER NMETHODS METHODS`: `VER` other than 5 is refused with no
   reply. A method list without 2 (username/password) gets `[5, 0xff]`.
   Otherwise the server writes `[5, 2]`.
2. RFC 1929 `VER ULEN UNAME PLEN PASSWD`. Admitted only when `VER` is 1, the
   password equals the session secret (`secretEq`), and the user name is not
   empty and has bytes 0x21 to 0x7e only. A refusal writes `[1, 1]`; an
   admission writes `[1, 0]`.
3. Request `VER CMD RSV ATYP DST.ADDR DST.PORT`: `VER` other than 5 is refused
   with no reply. `ATYP` other than 1, 3, 4 gets reply 8 (address type not
   supported). Then a command other than 1 (CONNECT) gets reply 7 (command not
   supported). Then the user `foafnaut-proxy-check` gets reply 2 and the
   outcome `proxyCheck`. Then an empty domain name or port 0 gets reply 2.
   Otherwise `connect`.

Known difference from `socks5.ts`: the TypeScript decodes the user name and the
domain name with `TextDecoder`, which drops a leading UTF-8 byte order mark.
So TypeScript admits a user name `EF BB BF 61` as "a"; this module refuses it
(byte 0xEF is not in 0x21 to 0x7e). TypeScript refuses a domain name of
exactly `EF BB BF` as empty; this module passes those three bytes on. This
module is the rule from now on.

Theorems: `L4Factoidal.Net.Socks5Theorems`.

No `sorry`, no `axiom`, no `partial`, no `native_decide`. Imports Lean core
only.
-/

namespace L4Factoidal.Net.Socks5

/-! ## Reply codes and bytes -/

/-- RFC 1928 §6 reply codes. -/
def repOk : UInt8 := 0
def repGeneral : UInt8 := 1
def repNotAllowed : UInt8 := 2
def repHostUnreachable : UInt8 := 4
def repRefused : UInt8 := 5
def repTtlExpired : UInt8 := 6
def repCommandNotSupported : UInt8 := 7
def repAddressNotSupported : UInt8 := 8

/-- The reply to a request: `VER REP RSV ATYP BND.ADDR BND.PORT`, with bound
address 0.0.0.0 and port 0, as `socks5.ts` writes it. -/
def replyBytes (rep : UInt8) : List UInt8 := [5, rep, 0, 1, 0, 0, 0, 0, 0, 0]

/-- The bytes of the user name of the start-up check, `foafnaut-proxy-check`
(`PROXY_CHECK_USER` in `socks5.ts`). -/
def proxyCheckUser : List UInt8 := "foafnaut-proxy-check".toUTF8.toList

/-! ## The session and the secret comparison -/

/-- One SOCKS5 session: the secret password that the worker made at start. -/
structure Session where
  secret : List UInt8

/-- The accumulated difference of two byte lists: OR of the XOR of each pair of
bytes, the shorter list padded with zero bytes. Every byte of both lists is
read; the recursion never stops at the first difference. -/
def diffFold : List UInt8 → List UInt8 → UInt8 → UInt8
  | [], [], acc => acc
  | a :: as, [], acc => diffFold as [] (acc ||| (a ^^^ 0))
  | [], b :: bs, acc => diffFold [] bs (acc ||| ((0 : UInt8) ^^^ b))
  | a :: as, b :: bs, acc => diffFold as bs (acc ||| (a ^^^ b))

/-- The pairs that `diffFold` reads: both lists, the shorter padded with zero
bytes. -/
def padZip : List UInt8 → List UInt8 → List (UInt8 × UInt8)
  | [], [] => []
  | a :: as, [] => (a, 0) :: padZip as []
  | [], b :: bs => (0, b) :: padZip [] bs
  | a :: as, b :: bs => (a, b) :: padZip as bs

/-- Password comparison (`sameBytes` in `socks5.ts`): the lengths are equal and
the accumulated difference is zero. Both parts are computed before they are
combined. -/
def secretEq (a b : List UInt8) : Bool :=
  let d := diffFold a b 0
  let sameLength := a.length == b.length
  sameLength && d == 0

/-! ## A small parser over the received prefix -/

/-- The result of one parse stage: more bytes are needed, the stage refuses
with error `e`, or it gives `a` and the bytes after it. -/
inductive Res (ε α : Type) where
  | needMore
  | stop (e : ε)
  | ok (a : α) (rest : List UInt8)

/-- A parse stage. -/
def P (ε α : Type) := List UInt8 → Res ε α

def P.pure (a : α) : P ε α := fun l => .ok a l

def P.fail (e : ε) : P ε α := fun _ => .stop e

def P.bind (p : P ε α) (f : α → P ε β) : P ε β := fun l =>
  match p l with
  | .needMore => .needMore
  | .stop e => .stop e
  | .ok a rest => f a rest

/-- One byte. -/
def P.byte : P ε UInt8 := fun l =>
  match l with
  | [] => .needMore
  | b :: rest => .ok b rest

/-- Exactly `n` bytes. -/
def P.bytes (n : Nat) : P ε (List UInt8) := fun l =>
  if n ≤ l.length then .ok (l.take n) (l.drop n) else .needMore

/-! ## The three messages -/

/-- Refusals of the greeting. -/
inductive GreetErr where
  /-- The first byte is not 5. No reply. -/
  | notSocks5
  /-- The method list has no 2 (username/password). Reply `[5, 0xff]`. -/
  | noUserPassMethod
deriving DecidableEq, Repr

def GreetErr.reply : GreetErr → List UInt8
  | .notSocks5 => []
  | .noUserPassMethod => [5, 0xff]

/-- Greeting `VER NMETHODS METHODS` (RFC 1928 §3). -/
def greeting : P GreetErr Unit :=
  P.bind P.byte fun ver =>
  P.bind P.byte fun nmethods =>
  if ver ≠ 5 then P.fail .notSocks5 else
  P.bind (P.bytes nmethods.toNat) fun methods =>
  if methods.contains 2 then P.pure () else P.fail .noUserPassMethod

/-- The fields of the RFC 1929 message. -/
structure Creds where
  aver : UInt8
  user : List UInt8
  pass : List UInt8
deriving DecidableEq, Repr

/-- RFC 1929 §2 `VER ULEN UNAME PLEN PASSWD`. This stage never refuses. -/
def authMsg : P Empty Creds :=
  P.bind P.byte fun aver =>
  P.bind P.byte fun ulen =>
  P.bind (P.bytes ulen.toNat) fun user =>
  P.bind P.byte fun plen =>
  P.bind (P.bytes plen.toNat) fun pass =>
  P.pure ⟨aver, user, pass⟩

/-- A destination address (RFC 1928 §5). A domain name is kept as bytes: it is
passed to Tor and resolved by the exit, never here. -/
inductive Host where
  | ipv4 (bytes : List UInt8)
  | domain (name : List UInt8)
  | ipv6 (bytes : List UInt8)
deriving DecidableEq, Repr

def Host.isEmpty : Host → Bool
  | .domain n => n.isEmpty
  | _ => false

/-- Refusals of the request. -/
inductive ReqErr where
  /-- The request's first byte is not 5. No reply. -/
  | badRequestVersion
  /-- `ATYP` is not 1, 3 or 4. Reply 8. -/
  | addressType
deriving DecidableEq, Repr

def ReqErr.reply : ReqErr → List UInt8
  | .badRequestVersion => []
  | .addressType => replyBytes repAddressNotSupported

/-- The fields of a request. -/
structure Req where
  cmd : UInt8
  host : Host
  port : Nat
deriving DecidableEq, Repr

/-- `DST.ADDR` for address type `atyp`. -/
def address (atyp : UInt8) : P ReqErr Host :=
  if atyp = 1 then P.bind (P.bytes 4) fun b => P.pure (.ipv4 b)
  else if atyp = 3 then P.bind P.byte fun n => P.bind (P.bytes n.toNat) fun b => P.pure (.domain b)
  else if atyp = 4 then P.bind (P.bytes 16) fun b => P.pure (.ipv6 b)
  else P.fail .addressType

/-- Request `VER CMD RSV ATYP DST.ADDR DST.PORT` (RFC 1928 §4). The command is
read here and judged in `run`, after the address, as `socks5.ts` does. -/
def request : P ReqErr Req :=
  P.bind P.byte fun ver =>
  P.bind P.byte fun cmd =>
  P.bind P.byte fun _rsv =>
  P.bind P.byte fun atyp =>
  if ver ≠ 5 then P.fail .badRequestVersion else
  P.bind (address atyp) fun host =>
  P.bind P.byte fun hi =>
  P.bind P.byte fun lo =>
  P.pure ⟨cmd, host, hi.toNat * 256 + lo.toNat⟩

/-! ## The decision -/

/-- The circuit partition of a stream: the user name, nothing else. -/
structure Partition where
  user : List UInt8
deriving DecidableEq, Repr

/-- Why a connection was refused (the `why` of the `refused` event). -/
inductive Reason where
  | notSocks5
  | noUserPassMethod
  | authFailed
  | badRequestVersion
  | addressType
  | onlyConnect
  | emptyHostOrPort0
deriving DecidableEq, Repr

def GreetErr.reason : GreetErr → Reason
  | .notSocks5 => .notSocks5
  | .noUserPassMethod => .noUserPassMethod

def ReqErr.reason : ReqErr → Reason
  | .badRequestVersion => .badRequestVersion
  | .addressType => .addressType

inductive Verdict where
  | needMore
  | refuse (why : Reason)
  | proxyCheck (host : Host) (port : Nat)
  | connect (partition : Partition) (host : Host) (port : Nat) (consumed : Nat)
deriving DecidableEq, Repr

structure Outcome where
  /-- All bytes the server writes for this input prefix, from the start. -/
  sent : List UInt8
  verdict : Verdict
deriving DecidableEq, Repr

/-- A user name of RFC 1929 that this server admits: not empty, bytes 0x21 to
0x7e only (`/^[\x21-\x7e]+$/` in `socks5.ts`). -/
def userOk (u : List UInt8) : Bool :=
  !u.isEmpty && u.all (fun b => 0x21 ≤ b && b ≤ 0x7e)

/-- The admission test of the RFC 1929 message, with the password check given
as `passOk`. -/
def admit (passOk : List UInt8 → Bool) (c : Creds) : Bool :=
  c.aver == 1 && passOk c.pass && userOk c.user

/-- The bytes the server has written once the greeting is accepted. -/
def sentGreet : List UInt8 := [5, 2]
/-- ... once the RFC 1929 message is admitted. -/
def sentAuthOk : List UInt8 := [5, 2, 1, 0]
/-- ... once the RFC 1929 message is refused. -/
def sentAuthFail : List UInt8 := [5, 2, 1, 1]

/-- The decision, with the password check as a parameter. `handshake` is
`run` with `secretEq · s.secret`; the theorems use the parameter to show that
the secret acts only through it. -/
def run (passOk : List UInt8 → Bool) (input : List UInt8) : Outcome :=
  match greeting input with
  | .needMore => ⟨[], .needMore⟩
  | .stop e => ⟨e.reply, .refuse e.reason⟩
  | .ok () r1 =>
    match authMsg r1 with
    | .needMore => ⟨sentGreet, .needMore⟩
    | .stop e => nomatch e
    | .ok c r2 =>
      if admit passOk c then
        match request r2 with
        | .needMore => ⟨sentAuthOk, .needMore⟩
        | .stop e => ⟨sentAuthOk ++ e.reply, .refuse e.reason⟩
        | .ok q r3 =>
          if q.cmd ≠ 1 then ⟨sentAuthOk ++ replyBytes repCommandNotSupported, .refuse .onlyConnect⟩
          else if c.user = proxyCheckUser then
            ⟨sentAuthOk ++ replyBytes repNotAllowed, .proxyCheck q.host q.port⟩
          else if q.host.isEmpty || q.port == 0 then
            ⟨sentAuthOk ++ replyBytes repNotAllowed, .refuse .emptyHostOrPort0⟩
          else ⟨sentAuthOk, .connect ⟨c.user⟩ q.host q.port (input.length - r3.length)⟩
      else ⟨sentAuthFail, .refuse .authFailed⟩

/-- The decision of the server for session `s` on the bytes `input` received so
far on one connection. -/
def handshake (s : Session) (input : List UInt8) : Outcome :=
  run (fun p => secretEq p s.secret) input

/-! ## Fields of the input, independent of any session -/

/-- The RFC 1929 message of `input`, when the greeting was accepted and the
message is complete. -/
def credsField? (input : List UInt8) : Option Creds :=
  match greeting input with
  | .ok () r1 =>
    match authMsg r1 with
    | .ok c _ => some c
    | _ => none
  | _ => none

/-- The RFC 1929 password field of `input`. -/
def passwordField? (input : List UInt8) : Option (List UInt8) := (credsField? input).map (·.pass)

/-- The RFC 1929 user name field of `input`. -/
def userField? (input : List UInt8) : Option (List UInt8) := (credsField? input).map (·.user)

/-- The request of `input`, when the greeting and the RFC 1929 message are
complete and the request parses (whatever the password). -/
def requestField? (input : List UInt8) : Option Req :=
  match greeting input with
  | .ok () r1 =>
    match authMsg r1 with
    | .ok _ r2 =>
      match request r2 with
      | .ok q _ => some q
      | _ => none
    | _ => none
  | _ => none

/-- The one bit of the secret that the decision uses: whether the password
field equals it. `false` when there is no complete password field. -/
def authBit (s : Session) (input : List UInt8) : Bool :=
  match passwordField? input with
  | some p => secretEq p s.secret
  | none => false

/-- Text of a host for logs and for Tor: dotted decimal, IPv6 groups in lower
hexadecimal without zero compression (as `ipv6Text` in `socks5.ts`), or the
domain bytes unchanged. -/
def Host.textBytes : Host → List UInt8
  | .ipv4 b => ".".intercalate (b.map (fun x => toString x.toNat)) |>.toUTF8.toList
  | .ipv6 b =>
    let rec groups : List UInt8 → List String
      | x :: y :: rest => String.ofList (Nat.toDigits 16 (x.toNat * 256 + y.toNat)) :: groups rest
      | _ => []
    ":".intercalate (groups b) |>.toUTF8.toList
  | .domain n => n

/-! ## Listen address -/

/-- An IPv4 address. -/
structure IPv4 where
  a : UInt8
  b : UInt8
  c : UInt8
  d : UInt8
deriving DecidableEq, Repr

/-- The 127.0.0.0/8 loopback block (RFC 1122 §3.2.1.3 (g)). -/
def IPv4.isLoopback (x : IPv4) : Bool := x.a == 127

/-- The address the server listens on (`Deno.listen({ hostname: "127.0.0.1" })`). -/
def listenAddress : IPv4 := ⟨127, 0, 0, 1⟩

/-! ## The host messages of the worker

A model of `tor-worker.ts`: a thread creates the worker (`start t`); op
`socks` starts the SOCKS5 server once and answers with its port and password;
other ops answer without them. A worker answers with `postMessage`, which goes
to the thread that created it, whichever thread is named as the sender. -/

abbrev ThreadId := Nat

inductive HostState where
  | idle
  | started (owner : ThreadId)
  | socksUp (owner : ThreadId)
deriving DecidableEq, Repr

inductive HostIn where
  | start (t : ThreadId)
  | socksOp (sender : ThreadId)
  | otherOp (sender : ThreadId)
deriving DecidableEq, Repr

/-- One answer: the receiving thread, and whether it carries the port and
password of the SOCKS5 server. -/
structure HostOut where
  to : ThreadId
  carriesSecret : Bool
deriving DecidableEq, Repr

def hostStep : HostState → HostIn → HostState × List HostOut
  | .idle, .start t => (.started t, [])
  | .idle, _ => (.idle, [])
  | .started o, .start _ => (.started o, [])
  | .started o, .socksOp _ => (.socksUp o, [⟨o, true⟩])
  | .started o, .otherOp _ => (.started o, [⟨o, false⟩])
  | .socksUp o, .start _ => (.socksUp o, [])
  | .socksUp o, .socksOp _ => (.socksUp o, [⟨o, true⟩])
  | .socksUp o, .otherOp _ => (.socksUp o, [⟨o, false⟩])

/-- Run a list of host messages; the answers in order. -/
def hostRun : HostState → List HostIn → HostState × List HostOut
  | st, [] => (st, [])
  | st, m :: ms =>
    let (st1, out1) := hostStep st m
    let (st2, out2) := hostRun st1 ms
    (st2, out1 ++ out2)

/-- The thread of the first `start` in a list of messages. -/
def firstStart : List HostIn → Option ThreadId
  | [] => none
  | .start t :: _ => some t
  | _ :: ms => firstStart ms

end L4Factoidal.Net.Socks5
