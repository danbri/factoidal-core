/- RSA-OAEP with a digest provider that can refuse. XML uses HACL* at run
time. The refinement proofs take agreement of the provider's successful
digest values with the pure specification as a hypothesis. Agreement of the
native or Wasm extern with that specification remains an external trust
assumption. RSA key validity, randomness and compiled timing are separate
properties. -/
import L4Factoidal.Crypto.RsaOaep
import L4Factoidal.NatBounds

namespace L4Factoidal.Crypto.RsaOaep

structure DigestProvider where
  size : Nat
  run : ByteArray → Option ByteArray

def DigestProvider.checked (d : DigestProvider) (msg : ByteArray) : Option ByteArray :=
  (d.run msg).bind fun out => if 0 < d.size ∧ out.size = d.size then some out else none

/-- Only successful answers need agree. A provider can refuse any input. -/
def DigestProvider.Agrees (d : DigestProvider) (spec : ByteArray → ByteArray) : Prop :=
  ∀ msg out, d.run msg = some out → out = spec msg

/-- Kind: refinement.
Says: under provider agreement, a digest that passes the size check equals the specified digest.
Does not say: that this provider satisfies the agreement hypothesis. -/
private theorem checked_agrees {d : DigestProvider} {spec : ByteArray → ByteArray}
    (agree : d.Agrees spec) {msg out} (h : d.checked msg = some out) : out = spec msg := by
  obtain ⟨v, hv, hs⟩ := Option.bind_eq_some_iff.mp h
  split at hs
  · exact (Option.some.inj hs).symm.trans (agree msg v hv)
  · cases hs

/-- Kind: invariant.
Says: the checked call refuses if its provider returns no digest of the declared size.
Does not say: that a digest of the declared size has the correct value. -/
theorem checked_none_of_no_sized_digest {d : DigestProvider} {msg : ByteArray}
    (h : ∀ v, d.run msg = some v → v.size ≠ d.size) : d.checked msg = none := by
  cases hv : d.run msg with
  | none => simp [DigestProvider.checked, hv]
  | some v => simp [DigestProvider.checked, hv, h v hv]

private def mgfBlock (d : DigestProvider) (seed : List UInt8) (counter : Nat) :=
  (d.checked (toBA (seed ++ i2osp4 counter))).map ofBA

/-- RFC 8017 Appendix B.2.1. Each digest must succeed at its specified size.
The length check also prevents a short mask from reaching the XOR operation. -/
def mgf1Checked (d : DigestProvider) (seed : List UInt8) (n : Nat) : Option (List UInt8) :=
  if d.size = 0 ∨ n > L4Factoidal.two32 * d.size then none else
    let counters := List.range ((n + d.size - 1) / d.size)
    (counters.mapM (mgfBlock d seed)).bind fun blocks =>
      let mask := blocks.flatten.take n
      if mask.length = n then some mask else none

/-- Kind: invariant.
Says: a successful mask contains exactly the requested number of octets.
Does not say: that these octets are the specified MGF1 mask. -/
theorem mgf1Checked_length {d seed n out} (h : mgf1Checked d seed n = some out) :
    out.length = n := by
  unfold mgf1Checked at h
  split at h
  · cases h
  · obtain ⟨_, _, hs⟩ := Option.bind_eq_some_iff.mp h
    dsimp only at hs
    split at hs
    · rename_i hlen
      exact (congrArg List.length (Option.some.inj hs)).symm.trans hlen
    · cases hs

/-- Kind: invariant.
Says: one member on which the function refuses makes the option-valued traversal refuse.
Does not say: which member the implementation evaluates first. -/
private theorem mapM_none_of_mem {f : α → Option β} {x : α} {xs : List α}
    (hx : x ∈ xs) (hf : f x = none) : xs.mapM f = none := by
  induction xs with
  | nil => simp at hx
  | cons a xs ih =>
    rcases List.mem_cons.mp hx with hx | hx
    · subst a
      simp [hf]
    · cases ha : f a <;> simp [ha, ih hx]

/-- Kind: invariant.
Says: a checked digest refusal at any required counter makes the whole mask request refuse.
Does not say: that every provider failure has the same runtime cost. -/
theorem mgf1Checked_none_of_block {d : DigestProvider} {seed : List UInt8} {n c : Nat}
    (hc : c ∈ List.range ((n + d.size - 1) / d.size))
    (bad : d.checked (toBA (seed ++ i2osp4 c)) = none) : mgf1Checked d seed n = none := by
  have hb : mgfBlock d seed c = none := by simp [mgfBlock, bad]
  unfold mgf1Checked
  split
  · rfl
  · simp only [mapM_none_of_mem hc hb, Option.bind_none]

/-- Kind: refinement.
Says: if each successful call agrees with the reference function, a successful traversal returns its mapped list.
Does not say: that the traversal succeeds on every list. -/
private theorem mapM_agrees {f : α → Option β} {spec : α → β}
    (agree : ∀ a b, f a = some b → b = spec a) {xs : List α} {ys : List β}
    (h : xs.mapM f = some ys) : ys = xs.map spec := by
  induction xs generalizing ys with
  | nil => simpa using h.symm
  | cons a xs ih =>
    cases ha : f a with
    | none => simp [ha] at h
    | some b =>
      cases ht : xs.mapM f with
      | none => simp [ha, ht] at h
      | some bs =>
        have hbs : bs = xs.map spec := by
          apply ih
          exact ht
        have hb := agree a b ha
        simp [ha, ht] at h
        subst ys
        simp [hb, hbs]

/-- Kind: refinement.
Says: under digest agreement and matching digest widths, a successful mask equals the pure MGF1 mask.
Does not say: that HACL* and the pure digest agree on all inputs. -/
theorem mgf1Checked_agrees {d : DigestProvider} {H : OaepHash}
    (size : d.size = H.mgfLen) (agree : d.Agrees H.mgfHash)
    {seed n mask} (h : mgf1Checked d seed n = some mask) : mask = mgf1 H seed n := by
  have blockAgree : ∀ c b, mgfBlock d seed c = some b →
      b = ofBA (H.mgfHash (toBA (seed ++ i2osp4 c))) := by
    intro c b hb
    obtain ⟨v, hv, rfl⟩ := Option.map_eq_some_iff.mp hb
    rw [checked_agrees agree hv]
  unfold mgf1Checked at h
  split at h
  · cases h
  · obtain ⟨blocks, hb, hs⟩ := Option.bind_eq_some_iff.mp h
    have hblocks := mapM_agrees blockAgree hb
    dsimp only at hs
    split at hs
    · simpa only [mgf1, List.flatMap_def, hblocks, size] using (Option.some.inj hs).symm
    · cases hs

/-- Kind: refinement.
Says: successful application of both masks and the continuation has the reference result if mask values agree.
Does not say: that the mask provider can answer every request. -/
private theorem withMasks_agrees {mask : MaskProvider} {spec : List UInt8 → Nat → List UInt8}
    (agree : ∀ s n v, mask s n = some v → v = spec s n)
    {a b na nb finish} {out : α} (h : withMasks mask a b na nb finish = some out) :
    withMasks (fun s n => some (spec s n)) a b na nb finish = some out := by
  obtain ⟨ma, ha, h⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨mb, hb, h⟩ := Option.bind_eq_some_iff.mp h
  have hma := agree _ _ _ ha
  subst ma
  have hmb := agree _ _ _ hb
  subst mb
  exact h

def emeEncodeChecked (digest mgf : DigestProvider) (k : Nat) (label msg seed : List UInt8) :=
  (digest.checked (toBA label)).bind fun h =>
    emeEncodeWith digest.size k (ofBA h) msg seed (mgf1Checked mgf)

def emeDecodeChecked (digest mgf : DigestProvider) (k : Nat) (label em : List UInt8) :=
  (digest.checked (toBA label)).bind fun h =>
    emeDecodeWith digest.size k (ofBA h) em (mgf1Checked mgf)

/-- Kind: refinement.
Says: given agreement and matching widths for both digests, each successful encoding equals the pure EME encoding.
Does not say: that the caller chose a random seed or a valid RSA key. -/
theorem emeEncodeChecked_agrees {digest mgf : DigestProvider} {H : OaepHash}
    (hd : digest.size = H.hLen) (hm : mgf.size = H.mgfLen)
    (ad : digest.Agrees H.hash) (am : mgf.Agrees H.mgfHash)
    {k label msg seed em} (h : emeEncodeChecked digest mgf k label msg seed = some em) :
    emeEncode H k label msg seed = some em := by
  obtain ⟨lh, hl, hs⟩ := Option.bind_eq_some_iff.mp h
  rw [checked_agrees ad hl, hd] at hs
  unfold emeEncode emeEncodeWith
  unfold emeEncodeWith at hs
  split at hs
  · rename_i valid
    rw [if_pos valid]
    exact withMasks_agrees (fun _ _ _ hv => mgf1Checked_agrees hm am hv) hs
  · cases hs

/-- Kind: refinement.
Says: given agreement and matching widths for both digests, the pure EME decoder returns the same plaintext on success.
Does not say: that decoding has constant time or that RSA's private operation is correct. -/
theorem emeDecodeChecked_agrees {digest mgf : DigestProvider} {H : OaepHash}
    (hd : digest.size = H.hLen) (hm : mgf.size = H.mgfLen)
    (ad : digest.Agrees H.hash) (am : mgf.Agrees H.mgfHash)
    {k label em msg} (h : emeDecodeChecked digest mgf k label em = some msg) :
    emeDecode H k label em = some msg := by
  obtain ⟨lh, hl, hs⟩ := Option.bind_eq_some_iff.mp h
  rw [checked_agrees ad hl, hd] at hs
  unfold emeDecode emeDecodeWith
  unfold emeDecodeWith at hs
  split at hs
  · rename_i valid
    rw [if_pos valid]
    exact withMasks_agrees (fun _ _ _ hv => mgf1Checked_agrees hm am hv) hs
  · cases hs

def oaepEncryptChecked (digest mgf : DigestProvider) (pubOp : RsaOp) (n e msg label seed : ByteArray) :
    Option ByteArray := do
  let em ← emeEncodeChecked digest mgf n.size (ofBA label) (ofBA msg) (ofBA seed)
  pubOp n e (toBA em)

def oaepDecryptChecked (digest mgf : DigestProvider) (privOp : RsaOp) (n d c label : ByteArray) :
    Option ByteArray := do
  if c.size ≠ n.size then none else
    let em ← privOp n d c
    (emeDecodeChecked digest mgf n.size (ofBA label) (ofBA em)).map toBA

end L4Factoidal.Crypto.RsaOaep

#print axioms L4Factoidal.Crypto.RsaOaep.checked_none_of_no_sized_digest
#print axioms L4Factoidal.Crypto.RsaOaep.mgf1Checked_length
#print axioms L4Factoidal.Crypto.RsaOaep.mgf1Checked_none_of_block
#print axioms L4Factoidal.Crypto.RsaOaep.mgf1Checked_agrees
#print axioms L4Factoidal.Crypto.RsaOaep.emeEncodeChecked_agrees
#print axioms L4Factoidal.Crypto.RsaOaep.emeDecodeChecked_agrees
