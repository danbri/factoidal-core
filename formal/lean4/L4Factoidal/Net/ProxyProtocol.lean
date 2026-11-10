/-
L4Factoidal.Net.ProxyProtocol — the PROXY protocol version 2 header that a
TCP proxy writes before the bytes of the connection it relays (HAProxy,
"The PROXY protocol, Versions 1 & 2",
https://www.haproxy.org/download/2.9/doc/proxy-protocol.txt, section 2.2).

Why: on Fly every XMPP port is raw TCP and TLS ends on the machine, so the
socket's peer is Fly's proxy. With `handlers = ["proxy_proto"]` and
`proxy_proto_options = { version = "v2" }` the proxy sends this header first,
and it names the client. `xmpp-serve --proxy-protocol` reads it, before TLS,
and the failed-login limit counts against the client's address
(`Net.LoginLimit.addressTag`), not against the proxy's.

Every accept and refuse decision is `parse`. The host buffers the bytes of a
new connection, calls `parse` on what it has, and:

* `more`: waits for more bytes. `parse_more_bounded`: this happens only while
  the host holds fewer than `headerFixed + maxPayload` bytes, so the buffer is
  bounded. The spec (section 2.2) says a receiver rejects a partial header;
  this receiver waits instead, within that bound and the host's time limit,
  because a TCP segment can split the header, and a test does that.
* `refuse r`: closes the connection. No XMPP byte and no TLS byte is read.
* `local_ n`: drops `n` bytes; the connection is the proxy's own (a health
  check). Section 2.2: "the receiver must accept this connection as valid and
  must use the real connection endpoints". The address of the connection is
  then the socket's address, which is the proxy's.
* `proxy n address port`: drops `n` bytes; `address` (dotted IPv4, or eight
  hexadecimal IPv6 groups) is the client's. What follows the `n` bytes (a TLS
  ClientHello, an XMPP stream header) belongs to the connection.

Decisions, with the spec's words where it has them:

* The 12-byte signature, then version 2 only ("the receiver must only accept
  this value"). A version 1 header ("PROXY TCP4 ...") starts with `P`, not
  `\r`, so it is refused at its first byte: Fly sends v2 when asked to, and a
  second, text parser would only add a way in.
* Command LOCAL (0) or PROXY (1); anything else is refused ("Receivers must
  drop connections presenting unexpected values here").
* PROXY over TCP: family and transport `0x11` (IPv4, 12 address bytes) or
  `0x21` (IPv6, 36 address bytes). Every other family is refused for PROXY:
  UNSPEC names no client (the spec lets a receiver refuse it), UNIX has no
  address for a limit, DGRAM is not this service. LOCAL ignores the family.
* The length field counts every byte after the 16 fixed ones: the addresses
  and the TLVs. TLVs are skipped, unread. A length above `maxPayload` is
  refused, and so is a PROXY length shorter than its address block.
* An IPv4-mapped IPv6 source (`::ffff:a.b.c.d`) is given as the IPv4 address,
  so that it does not share the /64 key `0:0:0:0::/64` with every other one.

No `sorry`, no `axiom`, no `partial`.
-/

namespace L4Factoidal.Net.ProxyProtocol

/-- The 12 bytes that start a version 2 header (section 2.2). -/
def signature : List UInt8 :=
  [0x0D, 0x0A, 0x0D, 0x0A, 0x00, 0x0D, 0x0A, 0x51, 0x55, 0x49, 0x54, 0x0A]

/-- The signature, the version and command byte, the family byte and the
two length bytes. -/
def headerFixed : Nat := 16

/-- The largest length field this receiver accepts: an IPv6 address block
(36 bytes) and TLVs. The spec names no maximum; it asks that a header fit
the 536-byte minimum TCP segment. -/
def maxPayload : Nat := 1024

/-- Why a header was refused. -/
inductive Refusal where
  | signature | version | command | family | length
  deriving DecidableEq, Repr, Inhabited

def Refusal.name : Refusal → String
  | .signature => "signature"
  | .version => "version"
  | .command => "command"
  | .family => "family"
  | .length => "length"

/-- The decision on the bytes a connection has sent so far. -/
inductive Result where
  /-- Every byte so far can start a valid header; wait for more. -/
  | more
  | refuse (r : Refusal)
  /-- A LOCAL header of `consumed` bytes. -/
  | local_ (consumed : Nat)
  /-- A PROXY header of `consumed` bytes, with the client's address and port. -/
  | proxy (consumed : Nat) (address : String) (port : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- A byte differs from the signature (in the bytes there are). -/
def sigMismatch (bs : List UInt8) : Bool :=
  (bs.zip signature).any (fun p => p.1 != p.2)

def be16 (hi lo : UInt8) : Nat := hi.toNat * 256 + lo.toNat

/-- The address block of a PROXY header over TCP: IPv4 or IPv6. -/
def addrLen? (familyTransport : UInt8) : Option Nat :=
  if familyTransport == 0x11 then some 12
  else if familyTransport == 0x21 then some 36
  else none

/-- The loop of `groups16`: a tail call, so it uses no stack per group. -/
def groups16Go (acc : List Nat) : List UInt8 → List Nat
  | a :: b :: rest => groups16Go (be16 a b :: acc) rest
  | _ => acc.reverse

/-- 16-bit groups of an IPv6 address, big-endian. -/
def groups16 (bs : List UInt8) : List Nat := groups16Go [] bs

#guard groups16 [0x20, 0x01, 0x0d, 0xb8, 0xff] == [0x2001, 0x0db8]

/-- The text of a source address: dotted IPv4; the IPv4 address of an
IPv4-mapped IPv6 address; else eight lower-case hexadecimal groups. -/
def addressText (familyTransport : UInt8) (block : List UInt8) : String :=
  let dotted (bs : List UInt8) : String := ".".intercalate (bs.map (fun b => toString b.toNat))
  if familyTransport == 0x11 then dotted (block.take 4)
  else
    let src := block.take 16
    if src.take 10 == List.replicate 10 0 && (src.drop 10).take 2 == [0xff, 0xff] then dotted (src.drop 12)
    else ":".intercalate ((groups16 src).map (fun g => String.ofList (Nat.toDigits 16 g)))

/-- The source port: after the two addresses. -/
def sourcePort (familyTransport : UInt8) (block : List UInt8) : Nat :=
  let at_ := if familyTransport == 0x11 then 8 else 32
  match block.drop at_ with
  | hi :: lo :: _ => be16 hi lo
  | _ => 0

/-- The decision on the bytes `bs` a new connection has sent so far. -/
def parse (bs : List UInt8) : Result :=
  if sigMismatch bs then .refuse .signature
  else match bs.drop 12 with
  | vc :: ft :: hi :: lo :: rest =>
    if vc >>> 4 != 2 then .refuse .version
    else if be16 hi lo > maxPayload then .refuse .length
    else if vc &&& 0x0F == 0 then
      if rest.length < be16 hi lo then .more else .local_ (headerFixed + be16 hi lo)
    else if vc &&& 0x0F == 1 then
      match addrLen? ft with
      | none => .refuse .family
      | some n =>
        if be16 hi lo < n then .refuse .length
        else if rest.length < be16 hi lo then .more
        else .proxy (headerFixed + be16 hi lo) (addressText ft rest) (sourcePort ft rest)
    else .refuse .command
  | _ => .more

/-- `parse` over a byte array: only the first `headerFixed + maxPayload` bytes
can decide, so a large first read costs no more. -/
def parseBytes (b : ByteArray) : Result :=
  parse (b.extract 0 (headerFixed + maxPayload)).toList

/-! ## Theorems -/

/-- A byte that differs from the signature refuses the connection, whatever
follows: a client that does not start with a header is never read further. -/
theorem parse_signature (bs : List UInt8) (h : sigMismatch bs = true) :
    parse bs = .refuse .signature := by
  simp [parse, h]

/-- An accepted header starts with the signature. -/
theorem parse_local_sig (bs : List UInt8) (c : Nat) (h : parse bs = .local_ c) :
    sigMismatch bs = false := by
  cases hs : sigMismatch bs
  · rfl
  · rw [parse_signature bs hs] at h; cases h

theorem parse_proxy_sig (bs : List UInt8) (c : Nat) (a : String) (p : Nat)
    (h : parse bs = .proxy c a p) : sigMismatch bs = false := by
  cases hs : sigMismatch bs
  · rfl
  · rw [parse_signature bs hs] at h; cases h

/-- The host waits only while it holds fewer than `headerFixed + maxPayload`
bytes: the buffer of a connection that never completes a header is bounded. -/
theorem parse_more_bounded (bs : List UInt8) (h : parse bs = .more) :
    bs.length < headerFixed + maxPayload := by
  unfold parse at h
  split at h
  · cases h
  · rename_i hd
    have hl : (bs.drop 12).length = bs.length - 12 := List.length_drop
    split at h
    · rename_i vc ft hi lo rest heq
      rw [heq] at hl
      simp only [List.length_cons] at hl
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i hmax
          split at h
          · split at h
            · rename_i hr; simp [headerFixed, maxPayload] at *; omega
            · cases h
          · split at h
            · split at h
              · cases h
              · split at h
                · cases h
                · split at h
                  · rename_i hr; simp [headerFixed, maxPayload] at *; omega
                  · cases h
            · cases h
    · rename_i hno
      have : bs.drop 12 = [] ∨ (∃ a, bs.drop 12 = [a]) ∨ (∃ a b, bs.drop 12 = [a, b]) ∨
          (∃ a b c, bs.drop 12 = [a, b, c]) := by
        match hm : bs.drop 12 with
        | [] => exact Or.inl rfl
        | [a] => exact Or.inr (Or.inl ⟨a, rfl⟩)
        | [a, b] => exact Or.inr (Or.inr (Or.inl ⟨a, b, rfl⟩))
        | [a, b, c] => exact Or.inr (Or.inr (Or.inr ⟨a, b, c, rfl⟩))
        | a :: b :: c :: d :: rest => exact absurd hm (hno a b c d rest)
      rcases this with e | ⟨_, e⟩ | ⟨_, _, e⟩ | ⟨_, _, _, e⟩ <;>
        (rw [e] at hl; simp at hl; simp [headerFixed, maxPayload]; omega)

/-- A LOCAL header is never longer than the bytes there are. -/
theorem parse_local_le (bs : List UInt8) (c : Nat) (h : parse bs = .local_ c) :
    c ≤ bs.length := by
  unfold parse at h
  split at h
  · cases h
  · have hl : (bs.drop 12).length = bs.length - 12 := List.length_drop
    split at h
    · rename_i vc ft hi lo rest heq
      rw [heq] at hl
      simp only [List.length_cons] at hl
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · split at h
            · cases h
            · rename_i hr
              injection h with h
              simp [headerFixed] at *; omega
          · split at h
            · split at h
              · cases h
              · split at h
                · cases h
                · split at h <;> cases h
            · cases h
    · cases h

/-- A PROXY header is never longer than the bytes there are, so the bytes
after it are the connection's own. -/
theorem parse_proxy_le (bs : List UInt8) (c : Nat) (a : String) (p : Nat)
    (h : parse bs = .proxy c a p) : c ≤ bs.length := by
  unfold parse at h
  split at h
  · cases h
  · have hl : (bs.drop 12).length = bs.length - 12 := List.length_drop
    split at h
    · rename_i vc ft hi lo rest heq
      rw [heq] at hl
      simp only [List.length_cons] at hl
      split at h
      · cases h
      · split at h
        · cases h
        · split at h
          · split at h <;> cases h
          · split at h
            · split at h
              · cases h
              · split at h
                · cases h
                · split at h
                  · cases h
                  · rename_i hr
                    injection h with h
                    simp [headerFixed] at *; omega
            · cases h
    · cases h

/-! ## Checks -/

/-- A test header: signature, version/command, family, length, block. -/
def mk (vc ft : UInt8) (block : List UInt8) : List UInt8 :=
  signature ++ [vc, ft, UInt8.ofNat (block.length / 256), UInt8.ofNat (block.length % 256)] ++ block

def v4Block : List UInt8 := [203, 0, 113, 7, 10, 0, 0, 1, 0xC3, 0x50, 0x14, 0x66]
def v6Block : List UInt8 :=
  [0x20, 0x01, 0x0d, 0xb8, 0, 1, 0, 2, 0, 3, 0, 4, 0, 5, 0, 6] ++ List.replicate 16 0 ++ [0x12, 0x34, 0x14, 0x66]

-- IPv4 PROXY: 28 bytes, the source address and port.
#guard parse (mk 0x21 0x11 v4Block) == .proxy 28 "203.0.113.7" 50000
-- What follows the header is not read: a TLS ClientHello byte after it.
#guard parse (mk 0x21 0x11 v4Block ++ [0x16, 0x03, 0x01]) == .proxy 28 "203.0.113.7" 50000
-- IPv6 PROXY: 52 bytes; eight groups, which `LoginLimit.clientPrefix` reads.
#guard parse (mk 0x21 0x21 v6Block) == .proxy 52 "2001:db8:1:2:3:4:5:6" 0x1234
-- An IPv4-mapped IPv6 source is its IPv4 address.
#guard parse (mk 0x21 0x21 (List.replicate 10 0 ++ [0xff, 0xff, 198, 51, 100, 9] ++ List.replicate 16 0 ++ [0, 80, 0, 80]))
  == .proxy 52 "198.51.100.9" 80
-- TLVs after the addresses are skipped.
#guard parse (mk 0x21 0x11 (v4Block ++ [0x04, 0x00, 0x01, 0x00])) == .proxy 32 "203.0.113.7" 50000
-- LOCAL, length 0, any family.
#guard parse (mk 0x20 0x00 []) == .local_ 16
#guard parse (mk 0x20 0x11 v4Block) == .local_ 28
-- Each split point of a header waits; the whole header decides.
#guard (List.range 28).all (fun n => parse ((mk 0x21 0x11 v4Block).take n) == .more)
-- A wrong first byte: an XMPP stream header, a TLS ClientHello, a v1 header.
#guard parse "<?xml version='1.0'?>".toUTF8.toList == .refuse .signature
#guard parse [0x16, 0x03, 0x01] == .refuse .signature
#guard parse "PROXY TCP4 203.0.113.7 10.0.0.1 50000 5222\r\n".toUTF8.toList == .refuse .signature
-- A wrong byte inside the signature, before the rest arrived.
#guard parse (signature.take 5 ++ [0x0E]) == .refuse .signature
-- Version 1 in the binary form, command 2, families UNSPEC, UNIX, DGRAM.
#guard parse (mk 0x11 0x11 v4Block) == .refuse .version
#guard parse (mk 0x22 0x11 v4Block) == .refuse .command
#guard parse (mk 0x21 0x00 []) == .refuse .family
#guard parse (mk 0x21 0x31 (List.replicate 216 0)) == .refuse .family
#guard parse (mk 0x21 0x12 v4Block) == .refuse .family
-- A PROXY length shorter than its addresses; a length above the bound.
#guard parse (mk 0x21 0x11 (v4Block.take 8)) == .refuse .length
#guard parse (signature ++ [0x21, 0x11, 0x04, 0x01]) == .refuse .length
#guard parse (signature ++ [0x20, 0x00, 0x04, 0x00]) == .more
-- `parseBytes` reads only the bound.
#guard parseBytes (ByteArray.mk (mk 0x21 0x11 v4Block ++ List.replicate 5000 0x41).toArray) == .proxy 28 "203.0.113.7" 50000

end L4Factoidal.Net.ProxyProtocol
