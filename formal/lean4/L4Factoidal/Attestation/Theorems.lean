/- Observable execution and commitment properties for issue #745. -/
import L4Factoidal.Attestation.Ask

namespace L4Factoidal.Attestation

open RDF SPARQL

/-- Digest provenance theorem.
Says: a successful length check returns exactly the supplied hash's bytes.
Does not say: that hash is collision resistant or its FFI implementation
agrees with a cryptographic specification. -/
theorem hash32_bytes {hash : ByteArray → ByteArray} {message : ByteArray}
    {digest : Digest32} (h : hash32 hash message = .ok digest) :
    digest.bytes = hash message := by
  dsimp only [hash32] at h
  split at h
  · cases h
    rfl
  · cases h

/-- Exact commitment theorem.
Says: a successful journal binds the original supplied byte sequence and
salt, the actual admitted source policy and the supplied context through
the named versioned message encodings, and carries the computed Boolean.
Does not say: distinct messages cannot collide, the policy is authorised,
the salt has entropy, or the input graph records authentic facts. -/
theorem makeJournal_bindings (hash : ByteArray → ByteArray) (e : Evaluation)
    (salt originalBytes context : ByteArray) (j : Journal)
    (h : makeJournal hash e salt originalBytes context = .ok j) :
    j.graphCommitment.bytes = hash (graphMessage salt originalBytes) ∧
    j.policyHash.bytes = hash (policyMessage e.policy.source.encode) ∧
    j.contextHash.bytes = hash (contextMessage context) ∧
    j.satisfied = e.satisfied := by
  unfold makeJournal at h
  cases hg : hash32 hash (graphMessage salt originalBytes) with
  | error err => simp [hg, bind, Except.bind] at h
  | ok g =>
    cases hp : hash32 hash (policyMessage e.policy.source.encode) with
    | error err => simp [hg,hp,bind,Except.bind] at h
    | ok p =>
      cases hc : hash32 hash (contextMessage context) with
      | error err => simp [hg,hp,hc,bind,Except.bind] at h
      | ok c =>
        simp [hg,hp,hc,bind,Except.bind,pure,Except.pure] at h
        subst j
        exact ⟨hash32_bytes hg,hash32_bytes hp,hash32_bytes hc,rfl⟩

/-- Successful execution theorem.
Says: every successful attestation has a 32-byte salt, a bounded context,
and an actual successful evaluation of the exact supplied policy and
original bytes. Its public Boolean equals the existing ASK evaluator on
that completed evaluation's checked graph and admitted query.
Does not say: all standards queries are admitted, RDFS and rules form a
combined closure, or a native journal is a cryptographic execution proof. -/
theorem attest_success (hash : ByteArray → ByteArray) (p : Policy)
    (salt originalBytes context : ByteArray) (j : Journal)
    (h : attest hash p salt originalBytes context = .ok j) :
    salt.size = 32 ∧ context.size ≤ p.limits.maxContextBytes ∧
    ∃ e, evaluate p originalBytes = .ok e ∧
      makeJournal hash e salt originalBytes context = .ok j ∧
      j.satisfied = evalAsk {} ⟨e.graph,[]⟩ e.policy.query := by
  by_cases hs : salt.size = 32
  · by_cases hc : context.size ≤ p.limits.maxContextBytes
    · simp only [attest,hs, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte,
        Nat.not_lt_of_ge hc] at h
      cases he : evaluate p originalBytes with
      | error err => simp [he,bind,Except.bind] at h
      | ok e =>
          simp only [he,bind,Except.bind] at h
          exact ⟨hs, hc, e, rfl, h,
            (makeJournal_satisfied hash e salt originalBytes context j h).trans e.answer⟩
    · simp [attest,hs,Nat.lt_of_not_ge hc,bind,Except.bind,
        throw,throwThe,MonadExceptOf.throw] at h
  · simp [attest,hs,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at h

/-- Input-length refusal theorem.
Says: any salt with the wrong length causes a defined invalid-input error
before evaluation or hashing, so it cannot produce a false verdict.
Does not say: any correctly sized salt has sufficient entropy. -/
theorem attest_wrong_salt (hash : ByteArray → ByteArray) (p : Policy)
    (salt originalBytes context : ByteArray) (h : salt.size ≠ 32) :
    attest hash p salt originalBytes context = .error (.invalidInput "salt must have 32 bytes") := by
  simp [attest,h,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

/-- Context-bound refusal theorem.
Says: a correctly salted request with an oversized context causes a
defined resource-limit error before evaluation or hashing.
Does not say: the context format prevents replay; the verifier must
authorise its contents and consume its nonce. -/
theorem attest_context_limit (hash : ByteArray → ByteArray) (p : Policy)
    (salt originalBytes context : ByteArray) (hs : salt.size = 32)
    (hc : p.limits.maxContextBytes < context.size) :
    attest hash p salt originalBytes context = .error (.resourceLimit "context bytes") := by
  simp [attest,hs,hc,bind,Except.bind,throw,throwThe,MonadExceptOf.throw]

#print axioms hash32_bytes
#print axioms makeJournal_bindings
#print axioms attest_success
#print axioms attest_wrong_salt
#print axioms attest_context_limit

end L4Factoidal.Attestation
