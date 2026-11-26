/-
L4Factoidal.Net.Socks5Theorems — theorems about the SOCKS5 decisions of
`L4Factoidal.Net.Socks5` (the server of the Foafnaut Tor worker).

Owner, 2026-11-26, verbatim: "make sure this is splattered with theorems of
great impressiveness and robustness". Plan: section 18 of
`docs/designissues/2026-11-25-foafnaut-tor-onion-routing.md`. Reading rules:
`docs/designissues/2026-11-10-theorems-as-contributions.md`.

(a) No stream without the secret: `connect_only_with_secret`,
    `proxyCheck_only_with_secret`, `wrong_password_refused`,
    `wrong_password_length_refused`, `no_userpass_method_refused`,
    `not_socks5_refused`, `connect_command_is_connect`,
    `non_connect_command_refused`, `truncated_needMore`, `handshake_final`.
(b) Partition: `connect_partition`, `partition_function_of_user`,
    `partition_injective`, `connect_partition_ok`, `Partition.key_injective`.
(c) Non-interference: `handshake_factor`, `handshake_secret_free`,
    `handshake_eq_unless_password_is_secret`, `handshake_noninterference`,
    `same_reason_same_outcome`, `run_sent_shape`.
(d) The comparison reads every byte: `diffFold_eq_foldl`, `padZip_length`,
    `padZip_getElem?`, `secretEq_iff`. This is not a statement of constant
    CPU time.
(e) `listenAddress_loopback`.
(f) Host model: `hostRun_answers_to_starter`, `secret_only_to_starter`.

Test vectors: the `#guard`s below, the cases of `socks5.test.ts`.

Not proved here: that `socks5.ts` or `tor-worker.ts` behave as this model
(the TypeScript does not call this module yet; a differential test is planned
in section 18 of the design record); anything about timing.

No `sorry`, no `axiom`, no `partial`, no `native_decide`.
-/
import L4Factoidal.Net.Socks5

namespace L4Factoidal.Net.Socks5

/-! ## Test vectors (the cases of `socks5.test.ts`) -/

private def ascii (s : String) : List UInt8 := s.toUTF8.toList
private def sess : Session := ⟨ascii "0123abcd"⟩
private def authBytes (u p : String) : List UInt8 :=
  [1, (ascii u).length.toUInt8] ++ ascii u ++ [(ascii p).length.toUInt8] ++ ascii p
private def connectDomain (cmd : UInt8) (h : String) (port : Nat) : List UInt8 :=
  [5, cmd, 0, 3, (ascii h).length.toUInt8] ++ ascii h ++ [(port / 256).toUInt8, (port % 256).toUInt8]
private def good : List UInt8 :=
  [5, 1, 2] ++ authBytes "siteA.example" "0123abcd" ++ connectDomain 1 "example.onion" 80

-- A good CONNECT with a domain name.
#guard handshake sess good ==
  ⟨[5, 2, 1, 0], .connect ⟨ascii "siteA.example"⟩ (.domain (ascii "example.onion")) 80 good.length⟩
-- Early client data after the request does not change the decision.
#guard handshake sess (good ++ ascii "GET / HTTP/1.1\r\n") == handshake sess good
-- Every strict prefix of a good handshake needs more bytes.
#guard (List.range good.length).all fun j => (handshake sess (good.take j)).verdict == .needMore
-- A wrong password.
#guard handshake sess ([5, 1, 2] ++ authBytes "siteA" "not-the-password") ==
  ⟨[5, 2, 1, 1], .refuse .authFailed⟩
-- A password of the right length with one byte changed.
#guard handshake sess ([5, 1, 2] ++ authBytes "siteA" "0123abce") == ⟨[5, 2, 1, 1], .refuse .authFailed⟩
-- No username/password method offered.
#guard handshake sess [5, 1, 0] == ⟨[5, 0xff], .refuse .noUserPassMethod⟩
-- Not SOCKS5.
#guard handshake sess [4, 1, 0] == ⟨[], .refuse .notSocks5⟩
-- BIND and UDP ASSOCIATE: reply 7.
#guard handshake sess ([5, 1, 2] ++ authBytes "siteA" "0123abcd" ++ connectDomain 2 "example.org" 80) ==
  ⟨[5, 2, 1, 0] ++ replyBytes 7, .refuse .onlyConnect⟩
#guard handshake sess ([5, 1, 2] ++ authBytes "siteA" "0123abcd" ++ connectDomain 3 "example.org" 80) ==
  ⟨[5, 2, 1, 0] ++ replyBytes 7, .refuse .onlyConnect⟩
-- The start-up check user: recorded and refused with reply 2.
#guard handshake sess ([5, 1, 2] ++ authBytes "foafnaut-proxy-check" "0123abcd" ++ [5, 1, 0, 1, 127, 0, 0, 1, 0, 80]) ==
  ⟨[5, 2, 1, 0] ++ replyBytes 2, .proxyCheck (.ipv4 [127, 0, 0, 1]) 80⟩
-- The start-up check user with a wrong password is refused at the password.
#guard handshake sess ([5, 1, 2] ++ authBytes "foafnaut-proxy-check" "x") == ⟨[5, 2, 1, 1], .refuse .authFailed⟩
-- Empty user name; a user name with a space.
#guard handshake sess ([5, 1, 2] ++ authBytes "" "0123abcd") == ⟨[5, 2, 1, 1], .refuse .authFailed⟩
#guard handshake sess ([5, 1, 2] ++ authBytes "a b" "0123abcd") == ⟨[5, 2, 1, 1], .refuse .authFailed⟩
-- Address type 5: reply 8 (before the command is judged).
#guard handshake sess ([5, 1, 2] ++ authBytes "siteA" "0123abcd" ++ [5, 2, 0, 5]) ==
  ⟨[5, 2, 1, 0] ++ replyBytes 8, .refuse .addressType⟩
-- Port 0 and an empty domain name: reply 2.
#guard handshake sess ([5, 1, 2] ++ authBytes "siteA" "0123abcd" ++ connectDomain 1 "example.org" 0) ==
  ⟨[5, 2, 1, 0] ++ replyBytes 2, .refuse .emptyHostOrPort0⟩
#guard handshake sess ([5, 1, 2] ++ authBytes "siteA" "0123abcd" ++ connectDomain 1 "" 443) ==
  ⟨[5, 2, 1, 0] ++ replyBytes 2, .refuse .emptyHostOrPort0⟩
-- Request version other than 5: no reply.
#guard handshake sess ([5, 1, 2] ++ authBytes "siteA" "0123abcd" ++ [4, 1, 0, 1]) ==
  ⟨[5, 2, 1, 0], .refuse .badRequestVersion⟩
-- IPv6 text.
#guard String.fromUTF8! ⟨(Host.ipv6 [0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1]).textBytes.toArray⟩ == "0:0:0:0:0:0:0:1"
#guard String.fromUTF8! ⟨(Host.ipv4 [10, 255, 255, 1]).textBytes.toArray⟩ == "10.255.255.1"
-- The user name of the start-up check is admissible as a user name.
#guard userOk proxyCheckUser
-- Host model: the secret goes to the starting thread, not to the sender.
#guard (hostRun .idle [.start 1, .start 2, .socksOp 3, .otherOp 1]).2 == [⟨1, true⟩, ⟨1, false⟩]

/-! ## Stability of the parse stages under more input -/

/-- `extend e r`: the result after `e` is appended to the input. -/
def Res.extend (e : List UInt8) : Res ε α → Res ε α
  | .ok a r => .ok a (r ++ e)
  | x => x

/-- A stage whose decisions do not change when bytes arrive later. -/
def P.Stable (p : P ε α) : Prop :=
  ∀ l e, p l ≠ .needMore → p (l ++ e) = (p l).extend e

/-- Invariant (parser combinator). Says: `P.pure` is stable under more input. Does not
say: anything about other stages. -/
theorem P.stable_pure (a : α) : (P.pure a : P ε α).Stable := by
  intro l e _; rfl

/-- Invariant (parser combinator). Says: `P.fail` is stable under more input. Does not
say: anything about other stages. -/
theorem P.stable_fail (x : ε) : (P.fail x : P ε α).Stable := by
  intro l e _; rfl

/-- Invariant (parser combinator). Says: reading one byte is stable under more input. Does
not say: that the byte is valid. -/
theorem P.stable_byte : (P.byte : P ε UInt8).Stable := by
  intro l e h
  cases l with
  | nil => exact absurd rfl h
  | cons b r => rfl

/-- Invariant (parser combinator). Says: reading `n` bytes is stable under more input.
Does not say: that `n` is bounded. -/
theorem P.stable_bytes (n : Nat) : (P.bytes n : P ε (List UInt8)).Stable := by
  intro l e h
  unfold P.bytes at *
  by_cases hn : n ≤ l.length
  · have hn' : n ≤ l.length + e.length := by omega
    simp [hn, hn', Res.extend, List.take_append_of_le_length hn, List.drop_append_of_le_length hn]
  · simp [hn] at h

/-- Invariant (parser combinator). Says: sequencing two stable stages gives a stable
stage. Does not say: that either stage ends. -/
theorem P.stable_bind {p : P ε α} {f : α → P ε β} (hp : p.Stable) (hf : ∀ a, (f a).Stable) :
    (P.bind p f).Stable := by
  intro l e h
  unfold P.bind at *
  cases hpl : p l with
  | needMore => simp [hpl] at h
  | stop x =>
    have := hp l e (by simp [hpl])
    simp [hpl, Res.extend] at this
    simp [this, Res.extend]
  | ok a r =>
    have := hp l e (by simp [hpl])
    simp [hpl, Res.extend] at this
    simp only [hpl] at h
    simp [this, hf a r e h]

/-- Invariant (parser combinator). Says: a choice between two stable stages is stable.
Does not say: which branch is taken. -/
theorem P.stable_ite {c : Prop} [Decidable c] {p q : P ε α} (hp : p.Stable) (hq : q.Stable) :
    (if c then p else q).Stable := by
  split <;> assumption

/-- Invariant. Says: the greeting stage is stable under more input. Does not say: that the
greeting is accepted. -/
theorem greeting_stable : greeting.Stable := by
  unfold greeting
  refine P.stable_bind P.stable_byte fun _ => P.stable_bind P.stable_byte fun _ => ?_
  refine P.stable_ite (P.stable_fail _) (P.stable_bind (P.stable_bytes _) fun _ => ?_)
  split
  · exact P.stable_pure _
  · exact P.stable_fail _

/-- Invariant. Says: the RFC 1929 stage is stable under more input. Does not say: that the
message is admitted. -/
theorem authMsg_stable : authMsg.Stable := by
  unfold authMsg
  exact P.stable_bind P.stable_byte fun _ => P.stable_bind P.stable_byte fun _ =>
    P.stable_bind (P.stable_bytes _) fun _ => P.stable_bind P.stable_byte fun _ =>
    P.stable_bind (P.stable_bytes _) fun _ => P.stable_pure _

/-- Invariant. Says: the address stage is stable under more input, for every address type.
Does not say: that the address is reachable. -/
theorem address_stable (atyp : UInt8) : (address atyp).Stable := by
  unfold address
  refine P.stable_ite (P.stable_bind (P.stable_bytes _) fun _ => P.stable_pure _) ?_
  refine P.stable_ite (P.stable_bind P.stable_byte fun _ =>
    P.stable_bind (P.stable_bytes _) fun _ => P.stable_pure _) ?_
  exact P.stable_ite (P.stable_bind (P.stable_bytes _) fun _ => P.stable_pure _) (P.stable_fail _)

/-- Invariant. Says: the request stage is stable under more input. Does not say: that the
request is admitted. -/
theorem request_stable : request.Stable := by
  unfold request
  refine P.stable_bind P.stable_byte fun _ => P.stable_bind P.stable_byte fun _ =>
    P.stable_bind P.stable_byte fun _ => P.stable_bind P.stable_byte fun _ => ?_
  exact P.stable_ite (P.stable_fail _) (P.stable_bind (address_stable _) fun _ =>
    P.stable_bind P.stable_byte fun _ => P.stable_bind P.stable_byte fun _ => P.stable_pure _)

/-- Invariant. Says: once `run` has decided (anything but `needMore`) on a
prefix, more input bytes give the same outcome, `consumed` included.
Does not say: what the host does with the bytes after `consumed` (they are
early client data that the host passes to the stream). -/
theorem run_final (passOk : List UInt8 → Bool) (i e : List UInt8)
    (h : (run passOk i).verdict ≠ .needMore) : run passOk (i ++ e) = run passOk i := by
  unfold run at *
  cases hg : greeting i with
  | needMore => simp [hg] at h
  | stop x =>
    have := greeting_stable i e (by simp [hg]); simp [hg, Res.extend] at this; simp [this]
  | ok u r1 =>
    have hg' := greeting_stable i e (by simp [hg]); simp [hg, Res.extend] at hg'
    simp only [hg] at h; simp only [hg']
    cases ha : authMsg r1 with
    | needMore => simp [ha] at h
    | stop x => exact nomatch x
    | ok c r2 =>
      have ha' := authMsg_stable r1 e (by simp [ha]); simp [ha, Res.extend] at ha'
      simp only [ha] at h; simp only [ha']
      by_cases hadm : admit passOk c = true
      · simp only [hadm, if_true] at h ⊢
        cases hr : request r2 with
        | needMore => simp [hr] at h
        | stop x =>
          have := request_stable r2 e (by simp [hr]); simp [hr, Res.extend] at this; simp [this]
        | ok q r3 =>
          have hr' := request_stable r2 e (by simp [hr]); simp [hr, Res.extend] at hr'
          simp only [hr']
          simp only [List.length_append]
          have : i.length + e.length - (r3.length + e.length) = i.length - r3.length := by omega
          simp only [this]
      · simp [hadm]

/-- Invariant. Says: `consumed` of a `connect` is at most the length of the
input. Does not say: that the input had no bytes after the request. -/
theorem run_consumed_le (passOk : List UInt8 → Bool) (i : List UInt8) {p h port c}
    (hc : (run passOk i).verdict = .connect p h port c) : c ≤ i.length := by
  unfold run at hc
  split at hc
  · simp at hc
  · simp at hc
  · split at hc
    · simp at hc
    · rename_i x _; exact nomatch x
    · split at hc
      · split at hc
        · simp at hc
        · simp at hc
        · split at hc
          · simp at hc
          · split at hc
            · simp at hc
            · split at hc
              · simp at hc
              · simp at hc; omega
      · simp at hc

/-! ## (d) The secret comparison -/

/-- Refinement. Says: `diffFold` is a left fold over `padZip a b`, the list of
byte pairs of both inputs with the shorter one padded by zero bytes.
Does not say: anything about CPU time. -/
theorem diffFold_eq_foldl (a b : List UInt8) (acc : UInt8) :
    diffFold a b acc = (padZip a b).foldl (fun acc p => acc ||| (p.1 ^^^ p.2)) acc := by
  induction a generalizing b acc with
  | nil =>
    induction b generalizing acc with
    | nil => simp [diffFold, padZip]
    | cons y ys ih => simp only [diffFold, padZip, List.foldl_cons]; exact ih _
  | cons x xs ih =>
    cases b with
    | nil => simp only [diffFold, padZip, List.foldl_cons]; exact ih [] _
    | cons y ys => simp only [diffFold, padZip, List.foldl_cons]; exact ih ys _

/-- Cost model. Says: the fold of `diffFold` has one step for each position up
to the length of the longer input: the comparison reads every byte of both
inputs, whether or not they differ.
Does not say: that the comparison takes constant CPU time. The compiled code,
the allocator and the cache can still depend on the data; this is a statement
about the Lean definition, not about the machine. -/
theorem padZip_length (a b : List UInt8) : (padZip a b).length = max a.length b.length := by
  induction a generalizing b with
  | nil =>
    induction b with
    | nil => simp [padZip]
    | cons y ys ih => simp only [padZip, List.length_cons, ih, List.length_nil]; omega
  | cons x xs ih =>
    cases b with
    | nil => simp only [padZip, List.length_cons, ih, List.length_nil]; omega
    | cons y ys => simp only [padZip, List.length_cons, ih]; omega

/-- Cost model. Says: position `k` of the fold of `diffFold` reads byte `k` of
each input (zero past its end), for every `k` below the longer length; no byte
of either input is skipped.
Does not say: that the comparison takes constant CPU time. -/
theorem padZip_getElem? (a b : List UInt8) (k : Nat) (hk : k < max a.length b.length) :
    (padZip a b)[k]? = some (a.getD k 0, b.getD k 0) := by
  induction a generalizing b k with
  | nil =>
    induction b generalizing k with
    | nil => simp at hk
    | cons y ys ih =>
      cases k with
      | zero => simp [padZip]
      | succ k =>
        simp only [padZip, List.getElem?_cons_succ]
        have := ih k (by simp at hk ⊢; omega)
        simpa using this
  | cons x xs ih =>
    cases b with
    | nil =>
      cases k with
      | zero => simp [padZip]
      | succ k =>
        simp only [padZip, List.getElem?_cons_succ]
        have := ih [] k (by simp at hk ⊢; omega)
        simpa using this
    | cons y ys =>
      cases k with
      | zero => simp [padZip]
      | succ k =>
        simp only [padZip, List.getElem?_cons_succ]
        have := ih ys k (by simp at hk ⊢; omega)
        simpa using this

/-- Invariant. Says: for lists of equal length, the accumulated difference is zero exactly
when the start value is zero and the lists are equal. Does not say: anything for lists of
different length (`secretEq` checks the length apart). -/
theorem diffFold_eq_zero_iff (a b : List UInt8) (acc : UInt8) (hl : a.length = b.length) :
    diffFold a b acc = 0 ↔ acc = 0 ∧ a = b := by
  induction a generalizing b acc with
  | nil =>
    cases b with
    | nil => simp [diffFold]
    | cons y ys => simp at hl
  | cons x xs ih =>
    cases b with
    | nil => simp at hl
    | cons y ys =>
      simp only [diffFold]
      rw [ih ys _ (by simpa using hl), UInt8.or_eq_zero_iff, UInt8.xor_eq_zero_iff]
      simp only [List.cons.injEq]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨h1, h2, h3⟩
      · rintro ⟨h1, h2, h3⟩; exact ⟨⟨h1, h2⟩, h3⟩

/-- Conformance (of the comparison with list equality). Says: `secretEq a b`
is true exactly when `a` and `b` are the same bytes.
Does not say: that it takes the same time for all inputs. -/
theorem secretEq_iff (a b : List UInt8) : secretEq a b = true ↔ a = b := by
  unfold secretEq
  by_cases hl : a.length = b.length
  · simp only [Bool.and_eq_true, beq_iff_eq, hl, true_and]
    rw [diffFold_eq_zero_iff a b 0 hl]; simp
  · simp only [Bool.and_eq_true, beq_iff_eq, hl, false_and, false_iff]
    intro h; exact hl (h ▸ rfl)

/-! ## The fields under a decision -/

/-- Invariant. Says: when `run` answers `connect`, the input has a complete RFC 1929
message that `admit` accepted and a complete request with command 1, a user name other
than the start-up check user, a non-empty host and a port other than 0; the partition is
the user name and the target is the request's. Does not say: that Tor can open the stream.
-/
theorem run_connect_facts {passOk : List UInt8 → Bool} {i : List UInt8} {p h port c}
    (hc : (run passOk i).verdict = .connect p h port c) :
    ∃ cr q, credsField? i = some cr ∧ requestField? i = some q ∧ admit passOk cr = true ∧
      q.cmd = 1 ∧ cr.user ≠ proxyCheckUser ∧ q.host.isEmpty = false ∧ q.port ≠ 0 ∧
      p = ⟨cr.user⟩ ∧ h = q.host ∧ port = q.port := by
  unfold run at hc
  unfold credsField? requestField?
  cases hg : greeting i with
  | needMore => simp [hg] at hc
  | stop x => simp [hg] at hc
  | ok u r1 =>
    simp only [hg] at hc ⊢
    cases ha : authMsg r1 with
    | needMore => simp [ha] at hc
    | stop x => exact nomatch x
    | ok cr r2 =>
      simp only [ha] at hc ⊢
      by_cases hadm : admit passOk cr = true
      · simp only [hadm, if_true] at hc
        cases hr : request r2 with
        | needMore => simp [hr] at hc
        | stop x => simp [hr] at hc
        | ok q r3 =>
          simp only [hr] at hc ⊢
          by_cases h1 : q.cmd = 1
          · by_cases h2 : cr.user = proxyCheckUser
            · simp [h1, h2] at hc
            · by_cases h3 : (q.host.isEmpty || q.port == 0) = true
              · simp [h1, h2, h3] at hc
              · simp only [Bool.or_eq_true, beq_iff_eq, not_or, Bool.not_eq_true] at h3
                simp [h1, h2, h3] at hc
                obtain ⟨rfl, rfl, rfl, _⟩ := hc
                exact ⟨cr, q, rfl, rfl, hadm, h1, h2, h3.1, h3.2, rfl, rfl, rfl⟩
          · simp [h1] at hc
      · simp [hadm] at hc

/-- Invariant. Says: when `run` answers `proxyCheck`, the RFC 1929 message was admitted,
the command is 1 and the user name is the start-up check user. Does not say: that the
target is a loopback name. -/
theorem run_proxyCheck_facts {passOk : List UInt8 → Bool} {i : List UInt8} {h port}
    (hc : (run passOk i).verdict = .proxyCheck h port) :
    ∃ cr q, credsField? i = some cr ∧ requestField? i = some q ∧ admit passOk cr = true ∧
      q.cmd = 1 ∧ cr.user = proxyCheckUser ∧ h = q.host ∧ port = q.port := by
  unfold run at hc
  unfold credsField? requestField?
  cases hg : greeting i with
  | needMore => simp [hg] at hc
  | stop x => simp [hg] at hc
  | ok u r1 =>
    simp only [hg] at hc ⊢
    cases ha : authMsg r1 with
    | needMore => simp [ha] at hc
    | stop x => exact nomatch x
    | ok cr r2 =>
      simp only [ha] at hc ⊢
      by_cases hadm : admit passOk cr = true
      · simp only [hadm, if_true] at hc
        cases hr : request r2 with
        | needMore => simp [hr] at hc
        | stop x => simp [hr] at hc
        | ok q r3 =>
          simp only [hr] at hc ⊢
          by_cases h1 : q.cmd = 1
          · by_cases h2 : cr.user = proxyCheckUser
            · simp [h1, h2] at hc
              obtain ⟨rfl, rfl⟩ := hc
              exact ⟨cr, q, rfl, rfl, hadm, h1, h2, rfl, rfl⟩
            · by_cases h3 : (q.host.isEmpty || q.port == 0) = true
              · simp [h1, h2, h3] at hc
              · simp [h1, h2, h3] at hc
          · simp [h1] at hc
      · simp [hadm] at hc

/-- Invariant. Says: `admit` with the session's check accepts only version 1, the exact
secret and an admissible user name. Does not say: that a message with these fields is
always admitted by `run` (the greeting must come first). -/
theorem admit_secret {s : Session} {cr : Creds}
    (h : admit (fun p => secretEq p s.secret) cr = true) :
    cr.aver = 1 ∧ cr.pass = s.secret ∧ userOk cr.user = true := by
  unfold admit at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact ⟨h.1.1, (secretEq_iff _ _).mp h.1.2, h.2⟩

/-! ## (a) No stream without the secret -/

/-- Conformance (RFC 1929 §2, with the rule of `socks5.ts`). Says: for every
session and every byte string, when the server answers `connect`, the input
holds a complete RFC 1929 message whose version is 1, whose password field is
exactly the session secret, and whose user name is admissible.
Does not say: that the client knew the secret in any other sense, or anything
about who else can read the secret on the machine. -/
theorem connect_only_with_secret (s : Session) (i : List UInt8) {p h port c}
    (hc : (handshake s i).verdict = .connect p h port c) :
    passwordField? i = some s.secret ∧
      ∃ cr, credsField? i = some cr ∧ cr.aver = 1 ∧ userOk cr.user = true := by
  obtain ⟨cr, _, hcr, _, hadm, _⟩ := run_connect_facts hc
  obtain ⟨h1, h2, h3⟩ := admit_secret hadm
  exact ⟨by simp [passwordField?, hcr, h2], cr, hcr, h1, h3⟩

/-- Conformance. Says: the start-up check answer (`proxyCheck`, which records
the target) also needs the exact secret.
Does not say: that the start-up check finds every proxy bypass. -/
theorem proxyCheck_only_with_secret (s : Session) (i : List UInt8) {h port}
    (hc : (handshake s i).verdict = .proxyCheck h port) : passwordField? i = some s.secret := by
  obtain ⟨cr, _, hcr, _, hadm, _⟩ := run_proxyCheck_facts hc
  exact by simp [passwordField?, hcr, (admit_secret hadm).2.1]

/-- Conformance. Says: a complete RFC 1929 message whose password is not the
session secret gets `[1, 1]` after `[5, 2]` and the reason `authFailed`, for
every byte string that follows it.
Does not say: that the connection is closed (the host closes it). -/
theorem wrong_password_refused (s : Session) (i pw : List UInt8)
    (hp : passwordField? i = some pw) (hne : pw ≠ s.secret) :
    handshake s i = ⟨sentAuthFail, .refuse .authFailed⟩ := by
  unfold passwordField? credsField? at hp
  unfold handshake run
  cases hg : greeting i with
  | needMore => simp [hg] at hp
  | stop x => simp [hg] at hp
  | ok u r1 =>
    simp only [hg] at hp ⊢
    cases ha : authMsg r1 with
    | needMore => simp [ha] at hp
    | stop x => exact nomatch x
    | ok cr r2 =>
      simp only [ha, Option.map_some, Option.some.injEq] at hp ⊢
      have : admit (fun p => secretEq p s.secret) cr = false := by
        cases hh : admit (fun p => secretEq p s.secret) cr
        · rfl
        · exact absurd (hp ▸ (admit_secret hh).2.1) hne
      simp [this]

/-- Conformance. Says: a password of another length than the secret is
refused. Does not say: that the length of the secret is hidden. -/
theorem wrong_password_length_refused (s : Session) (i pw : List UInt8)
    (hp : passwordField? i = some pw) (hl : pw.length ≠ s.secret.length) :
    handshake s i = ⟨sentAuthFail, .refuse .authFailed⟩ :=
  wrong_password_refused s i pw hp (fun h => hl (h ▸ rfl))

/-- Conformance (RFC 1928 §3). Says: a greeting whose method list has no 2
(username/password), the "no authentication" method included, gets
`[5, 0xff]`, whatever bytes follow it.
Does not say: that a client which offers method 2 is admitted. -/
theorem no_userpass_method_refused (s : Session) (n : UInt8) (ms rest : List UInt8)
    (hl : ms.length = n.toNat) (h2 : ms.contains 2 = false) :
    handshake s (5 :: n :: (ms ++ rest)) = ⟨[5, 0xff], .refuse .noUserPassMethod⟩ := by
  have hle : n.toNat ≤ ms.length + rest.length := by omega
  have h2' : (2 : UInt8) ∉ ms := by simpa using h2
  simp [handshake, run, greeting, P.bind, P.byte, P.bytes, P.fail, hle,
    List.take_left' hl, List.drop_left' hl, h2', GreetErr.reply, GreetErr.reason]

/-- Conformance. Says: a first byte other than 5 is refused with no reply,
whatever follows. Does not say: anything about SOCKS4 clients beyond that. -/
theorem not_socks5_refused (s : Session) (v n : UInt8) (rest : List UInt8) (hv : v ≠ 5) :
    handshake s (v :: n :: rest) = ⟨[], .refuse .notSocks5⟩ := by
  simp [handshake, run, greeting, P.bind, P.byte, P.fail, hv, GreetErr.reply, GreetErr.reason]

/-- Conformance. Says: `connect` only follows a request whose command is 1
(CONNECT). Does not say: what Tor does with the stream. -/
theorem connect_command_is_connect (s : Session) (i : List UInt8) {p h port c}
    (hc : (handshake s i).verdict = .connect p h port c) :
    ∃ q, requestField? i = some q ∧ q.cmd = 1 := by
  obtain ⟨_, q, _, hq, _, h1, _⟩ := run_connect_facts hc
  exact ⟨q, hq, h1⟩

/-- Conformance (RFC 1928 §4, `socks5.ts`). Says: a complete request whose
command is not 1 (BIND is 2, UDP ASSOCIATE is 3) is refused, with reason
`onlyConnect` (reply 7) or, when the password check failed, `authFailed`.
Does not say: that BIND or UDP ASSOCIATE are wrong; this server does not
offer them. -/
theorem non_connect_command_refused (s : Session) (i : List UInt8) (q : Req)
    (hq : requestField? i = some q) (h1 : q.cmd ≠ 1) :
    handshake s i = ⟨sentAuthOk ++ replyBytes repCommandNotSupported, .refuse .onlyConnect⟩ ∨
      handshake s i = ⟨sentAuthFail, .refuse .authFailed⟩ := by
  unfold requestField? at hq
  unfold handshake run
  cases hg : greeting i with
  | needMore => simp [hg] at hq
  | stop x => simp [hg] at hq
  | ok u r1 =>
    simp only [hg] at hq ⊢
    cases ha : authMsg r1 with
    | needMore => simp [ha] at hq
    | stop x => exact nomatch x
    | ok cr r2 =>
      simp only [ha] at hq ⊢
      cases hr : request r2 with
      | needMore => simp [hr] at hq
      | stop x => simp [hr] at hq
      | ok q' r3 =>
        simp only [hr, Option.some.injEq] at hq
        subst hq
        by_cases hadm : admit (fun p => secretEq p s.secret) cr = true
        · left; simp [hadm, h1]
        · right; simp [hadm]

/-- Invariant. Says: a strict prefix of the bytes that a `connect` consumed
gets `needMore`: a truncated handshake is never admitted, and never refused
either. Does not say: how long the host waits for more bytes. -/
theorem truncated_needMore (s : Session) (i : List UInt8) {p h port c}
    (hc : (handshake s i).verdict = .connect p h port c) (j : Nat) (hj : j < c) :
    (handshake s (i.take j)).verdict = .needMore := by
  apply Classical.byContradiction
  intro hne
  have hfin := run_final (fun p => secretEq p s.secret) (i.take j) (i.drop j) hne
  rw [List.take_append_drop] at hfin
  unfold handshake at hc
  rw [hfin] at hc
  have := run_consumed_le _ _ hc
  simp at this
  omega

/-- Invariant. Says: once the decision is not `needMore`, bytes that arrive
later do not change it. Does not say: that the host reads them. -/
theorem handshake_final (s : Session) (i e : List UInt8)
    (h : (handshake s i).verdict ≠ .needMore) : handshake s (i ++ e) = handshake s i :=
  run_final _ i e h

/-! ## (c) The secret acts through one bit -/

/-- Invariant (non-interference). Says: the outcome of `handshake s i` is
`run` with a password check that ignores its argument and gives the one bit
`authBit s i`. The secret enters the outcome through that bit and no other
way. Does not say: that the bit is hidden (a client sees `[1, 1]` or `[1, 0]`). -/
theorem handshake_factor (s : Session) (i : List UInt8) :
    handshake s i = run (fun _ => authBit s i) i := by
  unfold handshake run authBit passwordField? credsField?
  split
  · rfl
  · rfl
  · rename_i hg
    simp only [hg]
    split
    · rfl
    · rename_i x _; exact nomatch x
    · rename_i ha
      simp [ha, admit]

/-- Invariant (non-interference). Says: two sessions with any two secrets give
the same outcome (bytes written, verdict, reason, target, partition) on every
input on which their password bits agree. So no field of an `Outcome` holds the
secret or anything computed from it other than that bit.
Does not say: anything about timing. -/
theorem handshake_secret_free (s1 s2 : Session) (i : List UInt8)
    (h : authBit s1 i = authBit s2 i) : handshake s1 i = handshake s2 i := by
  rw [handshake_factor s1, handshake_factor s2, h]

/-- Invariant (non-interference). Says: an input whose password field is
neither secret (or which has no complete password field) gets the same outcome
under both sessions. Does not say: anything about an input that holds one of
the two secrets. -/
theorem handshake_eq_unless_password_is_secret (s1 s2 : Session) (i : List UInt8)
    (h1 : passwordField? i ≠ some s1.secret) (h2 : passwordField? i ≠ some s2.secret) :
    handshake s1 i = handshake s2 i := by
  apply handshake_secret_free
  unfold authBit
  cases hp : passwordField? i with
  | none => rfl
  | some pw =>
    rw [hp] at h1 h2
    have e1 : secretEq pw s1.secret = false := by
      cases hh : secretEq pw s1.secret
      · rfl
      · exact absurd (by rw [(secretEq_iff _ _).mp hh]) h1
    have e2 : secretEq pw s2.secret = false := by
      cases hh : secretEq pw s2.secret
      · rfl
      · exact absurd (by rw [(secretEq_iff _ _).mp hh]) h2
    simp [e1, e2]

/-- Invariant. Says: every outcome with reason `authFailed` is `[5, 2, 1, 1]` with that
reason, for every password check and input. Does not say: why the check failed (version,
password or user name). -/
theorem run_authFailed (passOk : List UInt8 → Bool) (i : List UInt8)
    (h : (run passOk i).verdict = .refuse .authFailed) :
    run passOk i = ⟨sentAuthFail, .refuse .authFailed⟩ := by
  unfold run at *
  cases hg : greeting i with
  | needMore => simp [hg] at h
  | stop x => simp only [hg] at h; cases x <;> simp [GreetErr.reason] at h
  | ok u r1 =>
    simp only [hg] at h ⊢
    cases ha : authMsg r1 with
    | needMore => simp [ha] at h
    | stop x => exact nomatch x
    | ok cr r2 =>
      simp only [ha] at h ⊢
      by_cases hadm : admit passOk cr = true
      · exfalso
        simp only [hadm, if_true] at h
        cases hr : request r2 with
        | needMore => simp [hr] at h
        | stop x => simp only [hr] at h; cases x <;> simp [ReqErr.reason] at h
        | ok q r3 =>
          simp only [hr] at h
          split at h
          · simp at h
          · split at h
            · simp at h
            · split at h <;> simp at h
      · simp [hadm]

/-- Invariant (non-interference). Says: for two password checks `ok1` and
`ok2`, if either both outcomes are `authFailed` or neither is, the two outcomes
are equal in every field. With `handshake`, two sessions that differ in the
secret only differ on an input where exactly one of them refuses at the
password: every other log value, reply byte and target is the same.
Does not say: that the two outcomes are equal when one session admits and the
other refuses. -/
theorem run_noninterference (ok1 ok2 : List UInt8 → Bool) (i : List UInt8)
    (h : (run ok1 i).verdict = .refuse .authFailed ↔ (run ok2 i).verdict = .refuse .authFailed) :
    run ok1 i = run ok2 i := by
  by_cases hf : (run ok1 i).verdict = .refuse .authFailed
  · rw [run_authFailed _ _ hf, run_authFailed _ _ (h.mp hf)]
  · have hf2 : ¬ (run ok2 i).verdict = .refuse .authFailed := fun x => hf (h.mpr x)
    unfold run at *
    cases hg : greeting i with
    | needMore => rfl
    | stop x => rfl
    | ok u r1 =>
      simp only [hg] at hf hf2 ⊢
      cases ha : authMsg r1 with
      | needMore => rfl
      | stop x => exact nomatch x
      | ok cr r2 =>
        simp only [ha] at hf hf2 ⊢
        by_cases h1 : admit ok1 cr = true
        · by_cases h2 : admit ok2 cr = true
          · simp only [h1, h2]
          · simp [h2] at hf2
        · simp [h1] at hf

/-- Invariant (non-interference), for sessions. Says: the outcomes of two
sessions on one input are equal in every field unless exactly one of them is
`authFailed`. Does not say: anything about timing. -/
theorem handshake_noninterference (s1 s2 : Session) (i : List UInt8)
    (h : (handshake s1 i).verdict = .refuse .authFailed ↔
      (handshake s2 i).verdict = .refuse .authFailed) :
    handshake s1 i = handshake s2 i :=
  run_noninterference _ _ i h

/-- Invariant. Says: two outcomes with the same refusal reason are equal in
every field, for any two sessions: a log of the reason tells nothing about the
secret that the reason does not already tell.
Does not say: that the reason is hidden from the client. -/
theorem same_reason_same_outcome (s1 s2 : Session) (i : List UInt8) (r : Reason)
    (h1 : (handshake s1 i).verdict = .refuse r) (h2 : (handshake s2 i).verdict = .refuse r) :
    handshake s1 i = handshake s2 i := by
  apply handshake_noninterference
  rw [h1, h2]

/-- The finite set of byte strings that the server writes during a handshake. -/
def sentShapes : List (List UInt8) :=
  [[], [5, 0xff], sentGreet, sentAuthFail, sentAuthOk,
   sentAuthOk ++ replyBytes repNotAllowed, sentAuthOk ++ replyBytes repCommandNotSupported,
   sentAuthOk ++ replyBytes repAddressNotSupported]

/-- Invariant. Says: for every password check and every input, the bytes that
the server writes during the handshake are one of eight fixed strings; none
holds input bytes or the secret. Does not say: anything about the bytes copied
after `connect`. -/
theorem run_sent_shape (passOk : List UInt8 → Bool) (i : List UInt8) :
    (run passOk i).sent ∈ sentShapes := by
  unfold run
  split
  · simp [sentShapes]
  · rename_i x _; cases x <;> simp [GreetErr.reply, sentShapes]
  · split
    · simp [sentShapes]
    · rename_i x _; exact nomatch x
    · split
      · split
        · simp [sentShapes]
        · rename_i x _; cases x <;> simp [ReqErr.reply, sentShapes]
        · split
          · simp [sentShapes]
          · split
            · simp [sentShapes]
            · split <;> simp [sentShapes]
      · simp [sentShapes]

/-! ## (b) The partition -/

/-- Invariant. Says: the partition of a `connect` is the user name field of the
input. Does not say: that the user name names a real site. -/
theorem connect_partition (s : Session) (i : List UInt8) {p h port c}
    (hc : (handshake s i).verdict = .connect p h port c) : userField? i = some p.user := by
  obtain ⟨cr, _, hcr, _, _, _, _, _, _, rfl, _⟩ := run_connect_facts hc
  simp [userField?, hcr]

/-- Invariant. Says: the partition depends on the user name alone: two admitted
connections (any sessions, any inputs, any hosts and ports) with equal user
names get equal partitions. Does not say: that equal partitions share a
circuit at every moment (Tor may rotate circuits). -/
theorem partition_function_of_user (s1 s2 : Session) (i1 i2 : List UInt8)
    {p1 h1 port1 c1 p2 h2 port2 c2}
    (hc1 : (handshake s1 i1).verdict = .connect p1 h1 port1 c1)
    (hc2 : (handshake s2 i2).verdict = .connect p2 h2 port2 c2)
    (hu : userField? i1 = userField? i2) : p1 = p2 := by
  rw [connect_partition s1 i1 hc1, connect_partition s2 i2 hc2] at hu
  cases p1; cases p2; simp_all

/-- Invariant. Says: different user names give different partitions. Does not
say: that different partitions use different exit relays. -/
theorem partition_injective (s1 s2 : Session) (i1 i2 : List UInt8)
    {p1 h1 port1 c1 p2 h2 port2 c2}
    (hc1 : (handshake s1 i1).verdict = .connect p1 h1 port1 c1)
    (hc2 : (handshake s2 i2).verdict = .connect p2 h2 port2 c2)
    (hp : p1 = p2) : userField? i1 = userField? i2 := by
  rw [connect_partition s1 i1 hc1, connect_partition s2 i2 hc2, hp]

/-- Invariant. Says: the partition of a `connect` is an admissible user name:
not empty, bytes 0x21 to 0x7e, and not the start-up check user.
Does not say: that it is a host name. -/
theorem connect_partition_ok (s : Session) (i : List UInt8) {p h port c}
    (hc : (handshake s i).verdict = .connect p h port c) :
    userOk p.user = true ∧ p.user ≠ proxyCheckUser := by
  obtain ⟨cr, _, _, _, hadm, _, hpc, _, _, rfl, _⟩ := run_connect_facts hc
  exact ⟨(admit_secret hadm).2.2, hpc⟩

/-- The partition key as text, one character for each byte. For an admitted
user name (bytes 0x21 to 0x7e) it is the same string as the UTF-8 decoding
that `socks5.ts` uses. -/
def Partition.key (p : Partition) : String := String.ofList (p.user.map fun b => Char.ofNat b.toNat)

/-- Invariant. Says: `Partition.key` is injective on all byte strings, so two
partitions with the same key are the same partition. Does not say: that the
key equals the UTF-8 decoding for bytes 0x80 and above (such user names are
refused before a partition is made). -/
theorem Partition.key_injective (p1 p2 : Partition) (h : p1.key = p2.key) : p1 = p2 := by
  unfold Partition.key at h
  have h' := String.ofList_inj.mp h
  have hc : ∀ b : UInt8, (Char.ofNat b.toNat).toNat = b.toNat := fun b => by
    have := b.toNat_lt
    rw [Char.ofNat, dif_pos (by unfold Nat.isValidChar; omega)]; rfl
  have hinj : Function.Injective (fun b : UInt8 => Char.ofNat b.toNat) := by
    intro a b hab
    have := congrArg Char.toNat hab
    simp only [hc] at this
    exact UInt8.toNat_inj.mp this
  cases p1; cases p2
  simp only [Partition.mk.injEq]
  exact (List.map_inj_right fun x y hxy => hinj hxy).mp h'

/-! ## (e) The listen address -/

/-- Conformance (RFC 1122 §3.2.1.3 (g), the 127.0.0.0/8 block). Says: the server
listens on a loopback address, 127.0.0.1. Does not say: that other local
processes cannot connect (they can; the secret is what stops them). -/
theorem listenAddress_loopback : listenAddress.isLoopback = true ∧ listenAddress = ⟨127, 0, 0, 1⟩ := by
  decide

/-! ## (f) The host messages: the secret goes to the starting thread -/

def HostState.owner? : HostState → Option ThreadId
  | .idle => none
  | .started t => some t
  | .socksUp t => some t

/-- Invariant (of the host model). Says: one step keeps the owner and answers only the
owner. Does not say: that the step answers at all. -/
theorem hostStep_owner (st : HostState) (m : HostIn) (t : ThreadId) (h : st.owner? = some t) :
    (hostStep st m).1.owner? = some t ∧ ∀ o ∈ (hostStep st m).2, o.to = t := by
  cases st <;> cases m <;> simp_all [HostState.owner?, hostStep]

/-- Invariant (of the host model). Says: from a state with owner `t`, every answer of any
run goes to `t`. Does not say: that a run gives any answer. -/
theorem hostRun_owner (ms : List HostIn) (st : HostState) (t : ThreadId) (h : st.owner? = some t) :
    ∀ o ∈ (hostRun st ms).2, o.to = t := by
  induction ms generalizing st with
  | nil => simp [hostRun]
  | cons m ms ih =>
    intro o ho
    obtain ⟨h1, h2⟩ := hostStep_owner st m t h
    simp only [hostRun, List.mem_append] at ho
    rcases ho with ho | ho
    · exact h2 o ho
    · exact ih _ h1 o ho

/-- Invariant (of the model of `tor-worker.ts`). Says: in every run from a
worker that was not started, each answer, and so each answer that carries the
SOCKS5 port and password, goes to the thread of the first `start`; a later
`start` or a request from another thread does not change the receiver.
Does not say: that `tor-worker.ts` follows the model; a test of the host
against the model is still to be written. -/
theorem hostRun_answers_to_starter (ms : List HostIn) :
    ∀ o ∈ (hostRun .idle ms).2, firstStart ms = some o.to := by
  induction ms with
  | nil => simp [hostRun]
  | cons m ms ih =>
    intro o ho
    cases m with
    | start t =>
      simp only [hostRun, hostStep, List.nil_append] at ho
      simp only [firstStart]
      exact congrArg some (hostRun_owner ms (.started t) t rfl o ho).symm
    | socksOp x =>
      simp only [hostRun, hostStep, List.nil_append] at ho
      simpa [firstStart] using ih o ho
    | otherOp x =>
      simp only [hostRun, hostStep, List.nil_append] at ho
      simpa [firstStart] using ih o ho

/-- Corollary. Says: an answer that carries the secret goes to the thread that
started the worker. Does not say: what that thread does with it. -/
theorem secret_only_to_starter (ms : List HostIn) (o : HostOut)
    (ho : o ∈ (hostRun .idle ms).2) (_hs : o.carriesSecret = true) : firstStart ms = some o.to :=
  hostRun_answers_to_starter ms o ho

-- Non-vacuity examples for the hypotheses above.
example : ∃ o ∈ (hostRun .idle [.start 1, .socksOp 2]).2, o.carriesSecret = true ∧ o.to = 1 :=
  ⟨⟨1, true⟩, by decide, rfl, rfl⟩

/-! ## Axiom report (`lake build` prints it) -/

#print axioms connect_only_with_secret
#print axioms proxyCheck_only_with_secret
#print axioms wrong_password_refused
#print axioms wrong_password_length_refused
#print axioms no_userpass_method_refused
#print axioms not_socks5_refused
#print axioms connect_command_is_connect
#print axioms non_connect_command_refused
#print axioms truncated_needMore
#print axioms handshake_final
#print axioms connect_partition
#print axioms partition_function_of_user
#print axioms partition_injective
#print axioms connect_partition_ok
#print axioms Partition.key_injective
#print axioms handshake_factor
#print axioms handshake_secret_free
#print axioms handshake_eq_unless_password_is_secret
#print axioms run_noninterference
#print axioms handshake_noninterference
#print axioms same_reason_same_outcome
#print axioms run_sent_shape
#print axioms diffFold_eq_foldl
#print axioms padZip_length
#print axioms padZip_getElem?
#print axioms secretEq_iff
#print axioms listenAddress_loopback
#print axioms hostRun_answers_to_starter
#print axioms secret_only_to_starter

end L4Factoidal.Net.Socks5
