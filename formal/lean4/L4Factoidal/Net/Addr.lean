/-
L4Factoidal.Net.Addr — IP literals and the authority of an `http` or `https`
URL, read the same way by every surface that makes or checks an outbound
request (https://github.com/danbri/factoidal/issues/1126). Moved from
`L4Factoidal.LWS.InboxGuard`, which re-exports the names.

Sources: RFC 3986 §3.2.2 (host: IP-literal, IPv4address, reg-name);
RFC 4291 §2.2 (text form of IPv6 addresses); RFC 6874 (zone identifiers,
removed here); RFC 6761 §6.3 (localhost names).
-/

namespace L4Factoidal.Net

/-! ## IP literals -/

/-- A decimal octet: one to three digits, at most 255, no leading zero
(WHATWG and `inet_pton` read leading zeros differently, so they are not
IP literals here; such a host is a name, which the host resolves). -/
def octet? (s : String) : Option Nat :=
  if s.isEmpty || s.length > 3 || !s.all Char.isDigit then none
  else if s.length > 1 && s.front == '0' then none
  else match s.toNat? with
    | some n => if n ≤ 255 then some n else none
    | none => none

/-- An IPv4 address in dotted decimal, as its four octets. -/
def ipv4? (s : String) : Option (List Nat) :=
  match s.splitOn "." with
  | [a, b, c, d] => [a, b, c, d].mapM octet?
  | _ => none

/-- One IPv6 group: one to four hexadecimal digits. -/
def hexGroup? (s : String) : Option Nat :=
  if s.isEmpty || s.length > 4 then none
  else s.foldl (fun acc c => acc.bind (fun n =>
    if c.isDigit then some (n * 16 + (c.toNat - '0'.toNat))
    else if 'a' ≤ c && c ≤ 'f' then some (n * 16 + (c.toNat - 'a'.toNat + 10))
    else if 'A' ≤ c && c ≤ 'F' then some (n * 16 + (c.toNat - 'A'.toNat + 10))
    else none)) (some 0)

/-- The 16-bit groups of one side of `::`, with an IPv4 tail allowed
when `tail` (two groups). -/
def groups? (s : String) (tail : Bool) : Option (List Nat) :=
  if s.isEmpty then some [] else
  let parts := s.splitOn ":"
  match parts.getLast? with
  | none => some []
  | some last =>
      let front := parts.dropLast
      match (if tail then ipv4? last else none) with
      | some [a, b, c, d] =>
          (front.mapM hexGroup?).map (· ++ [a * 256 + b, c * 256 + d])
      | _ => parts.mapM hexGroup?

/-- An IPv6 address (without brackets, an RFC 6874 zone removed), as its
eight 16-bit groups. -/
def ipv6? (s0 : String) : Option (List Nat) :=
  let s := (s0.splitOn "%").head!
  match s.splitOn "::" with
  | [whole] =>
      match groups? whole true with
      | some gs => if gs.length == 8 then some gs else none
      | none => none
  | [l, r] =>
      match groups? l false, groups? r true with
      | some a, some b =>
          if a.length + b.length ≤ 7 then
            some (a ++ List.replicate (8 - a.length - b.length) 0 ++ b)
          else none
      | _, _ => none
  | _ => none

/-- An address, normalized: IPv4 as four octets; IPv6 as eight groups,
except an IPv4-mapped IPv6 address (`::ffff:a.b.c.d`), which is its IPv4
address. -/
inductive Addr where
  | v4 (octets : List Nat)
  | v6 (groups : List Nat)
deriving Repr, DecidableEq, BEq

/-- Read an IP literal: dotted decimal, or IPv6 with or without brackets. -/
def addr? (s : String) : Option Addr :=
  match ipv4? s with
  | some o => some (.v4 o)
  | none =>
      let inner := if s.startsWith "[" && s.endsWith "]" then ((s.drop 1).dropEnd 1).toString else s
      match ipv6? inner with
      | some [0, 0, 0, 0, 0, 0xffff, hi, lo] => some (.v4 [hi / 256, hi % 256, lo / 256, lo % 256])
      | some gs => some (.v6 gs)
      | none => none

/-! ## Authorities -/

/-- The host (lower case, without brackets for IPv6, one trailing dot
removed) and the port (by the scheme when absent) of an `http` or `https`
URL; `none` for another URL. -/
def authority? (u : String) : Option (String × Nat) :=
  match u.splitOn "://" with
  | [scheme, rest] =>
      let sch := scheme.toLower
      let dflt : Option Nat := if sch == "http" then some 80 else if sch == "https" then some 443 else none
      match dflt with
      | none => none
      | some d =>
          let auth := (String.ofList (rest.toList.takeWhile (fun c => c != '/' && c != '?' && c != '#'))).toLower
          let auth := match auth.splitOn "@" with
            | [a] => a
            | parts => parts.getLast!
          let (host, portText) :=
            if auth.startsWith "[" then
              match auth.splitOn "]" with
              | [h, p] => (h.drop 1 |>.toString, if p.startsWith ":" then (p.drop 1).toString else p)
              | _ => (auth, "")
            else match auth.splitOn ":" with
              | [h] => (h, "")
              | [h, p] => (h, p)
              | _ => (auth, "")
          let host := if host.endsWith "." then (host.dropEnd 1).toString else host
          if host.isEmpty then none else
          if portText.isEmpty then some (host, d)
          else (portText.toNat?).map (host, ·)
  | _ => none

/-- Is the name a localhost name (RFC 6761 §6.3)? -/
def localhostName (h : String) : Bool := h == "localhost" || h.endsWith ".localhost"

end L4Factoidal.Net
