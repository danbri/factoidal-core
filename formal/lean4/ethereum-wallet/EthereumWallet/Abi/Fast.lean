import EthereumWallet.Abi.Proofs

/-!
# A byte-array encoder, proved equal to the list specification

`AbiType.enc` builds lists, which is the right shape for proofs and a slow one
for large data: every level of nesting copies its bytes cell by cell.
`AbiType.encBA` has the same structure but joins the parts of a sequence in
byte arrays. `encBA_eq` proves it produces the same bytes on every input, so
it can stand in for the specification anywhere: the strict decoder uses it
for the canonical-form comparison, and callers that want bytes use
`encodeArgsBytes`.

Leaves (one word, or one `bytes` value) still go through the list form.
-/

namespace EthereumWallet.Abi

theorem ofBytes_toBytes (l : List UInt8) : ofBytes (toBytes l) = l := by
  simp [ofBytes, toBytes]

theorem ofBytes_append (a b : ByteArray) : ofBytes (a ++ b) = ofBytes a ++ ofBytes b := by
  simp [ofBytes]

theorem ofBytes_length (a : ByteArray) : (ofBytes a).length = a.size := by
  cases a
  simp [ofBytes, ByteArray.size]

theorem ofBytes_empty : ofBytes ByteArray.empty = [] := by
  simp [ofBytes]

theorem rd_eq_getElem (e : ByteArray) (i : Nat) (h : i < (ofBytes e).length) :
    rd e i = (ofBytes e)[i] := by
  have hs : i < e.size := by rw [← ofBytes_length]; exact h
  simp only [rd, hs, dite_true]
  rfl

/-- Compare the last `k` of the first `k` bytes of `e` with `d` from `p`, back to front. -/
def eqFrom (d : ByteArray) (p : Nat) (e : ByteArray) : Nat → Bool
  | 0 => true
  | k + 1 => rd d (p + k) == rd e k && eqFrom d p e k

theorem eqFrom_iff (d : ByteArray) (p : Nat) (e : ByteArray) (k : Nat) :
    eqFrom d p e k = true ↔ ∀ i, i < k → rd d (p + i) = rd e i := by
  induction k with
  | zero => simp [eqFrom]
  | succ k ih =>
    simp only [eqFrom, Bool.and_eq_true, beq_iff_eq, ih]
    constructor
    · intro h i hi
      by_cases hik : i = k
      · rw [hik]; exact h.1
      · exact h.2 i (by omega)
    · intro h
      exact ⟨h k (by omega), fun i hi => h i (by omega)⟩

/-- The bytes of `d` from `p` are exactly the array `e`. -/
def windowBA (d : ByteArray) (p : Nat) (e : ByteArray) : Bool :=
  decide (p + e.size ≤ d.size) && eqFrom d p e e.size

/-- Kind: decision procedure. Says: `windowBA` is true exactly when `d` holds the bytes of `e`
    at `p`.
    Does not say: anything about cost. -/
theorem windowBA_iff (d : ByteArray) (p : Nat) (e : ByteArray) :
    windowBA d p e = true ↔ Window d p (ofBytes e) := by
  simp only [windowBA, Bool.and_eq_true, decide_eq_true_eq, Window, ofBytes_length, eqFrom_iff]
  constructor
  · intro h
    exact ⟨h.1, fun i hi =>
      (h.2 i hi).trans (rd_eq_getElem e i (by rw [ofBytes_length]; exact hi))⟩
  · intro h
    exact ⟨h.1, fun i hi =>
      (h.2 i hi).trans (rd_eq_getElem e i (by rw [ofBytes_length]; exact hi)).symm⟩

/-! ## Sequences -/

def headTotalBA (fs : List (Bool × ByteArray)) : Nat :=
  fs.foldl (fun a f => a + (if f.1 then 32 else f.2.size)) 0

/-- One field: heads so far, tails so far, offset of the next tail. -/
def stepBA (st : ByteArray × ByteArray × Nat) (f : Bool × ByteArray) : ByteArray × ByteArray × Nat :=
  if f.1 then (st.1 ++ toBytes (word st.2.2), st.2.1 ++ f.2, st.2.2 + f.2.size)
  else (st.1 ++ f.2, st.2.1, st.2.2)

def encSeqBA (fs : List (Bool × ByteArray)) : ByteArray :=
  let r := fs.foldl stepBA (ByteArray.empty, ByteArray.empty, headTotalBA fs)
  r.1 ++ r.2.1

def asLists (fs : List (Bool × ByteArray)) : List (Bool × List UInt8) :=
  fs.map fun f => (f.1, ofBytes f.2)

theorem asLists_cons (f : Bool × ByteArray) (fs : List (Bool × ByteArray)) :
    asLists (f :: fs) = (f.1, ofBytes f.2) :: asLists fs := rfl

theorem headTotalBA_fold (fs : List (Bool × ByteArray)) (a : Nat) :
    fs.foldl (fun a f => a + (if f.1 then 32 else f.2.size)) a
      = (asLists fs).foldl (fun a f => a + (if f.1 then 32 else f.2.length)) a := by
  induction fs generalizing a with
  | nil => rfl
  | cons f fs ih =>
    rw [asLists_cons]
    simp only [List.foldl_cons, ofBytes_length]
    exact ih _

theorem headTotalBA_eq (fs : List (Bool × ByteArray)) : headTotalBA fs = headTotal (asLists fs) :=
  headTotalBA_fold fs 0

theorem fold_stepBA (fs : List (Bool × ByteArray)) :
    ∀ (H T : ByteArray) (cur : Nat),
      ofBytes (fs.foldl stepBA (H, T, cur)).1 = ofBytes H ++ heads (asLists fs) cur
        ∧ ofBytes (fs.foldl stepBA (H, T, cur)).2.1 = ofBytes T ++ tails (asLists fs) := by
  induction fs with
  | nil =>
    intro H T cur
    simp [asLists, heads_nil, tails_nil]
  | cons f fs ih =>
    intro H T cur
    obtain ⟨dyn, e⟩ := f
    rw [asLists_cons]
    cases dyn with
    | true =>
      have h := ih (H ++ toBytes (word cur)) (T ++ e) (cur + e.size)
      simp only [List.foldl_cons, stepBA, if_true]
      rw [heads_cons_dyn, tails_cons_dyn, ofBytes_length]
      refine ⟨?_, ?_⟩
      · rw [h.1, ofBytes_append, ofBytes_toBytes, List.append_assoc]
      · rw [h.2, ofBytes_append, List.append_assoc]
    | false =>
      have h := ih (H ++ e) T cur
      simp only [List.foldl_cons, stepBA, Bool.false_eq_true, if_false]
      rw [heads_cons_static, tails_cons_static]
      refine ⟨?_, h.2⟩
      rw [h.1, ofBytes_append, List.append_assoc]

/-- Kind: implementation equals specification. Says: joining a sequence in byte arrays gives
    the bytes of the list specification `encSeq`.
    Does not say: anything about speed. -/
theorem encSeqBA_eq (fs : List (Bool × ByteArray)) : ofBytes (encSeqBA fs) = encSeq (asLists fs) := by
  have h := fold_stepBA fs ByteArray.empty ByteArray.empty (headTotalBA fs)
  simp only [encSeqBA, encSeq]
  rw [ofBytes_append, h.1, h.2, headTotalBA_eq]
  simp [ofBytes_empty]

/-! ## The encoder -/

mutual
def AbiType.encBA : AbiType → AbiValue → ByteArray
  | .uint b, v => toBytes ((AbiType.uint b).enc v)
  | .int b, v => toBytes ((AbiType.int b).enc v)
  | .address, v => toBytes (AbiType.address.enc v)
  | .bool, v => toBytes (AbiType.bool.enc v)
  | .fixedBytes k, v => toBytes ((AbiType.fixedBytes k).enc v)
  | .bytes, v => toBytes (AbiType.bytes.enc v)
  | .string, v => toBytes (AbiType.string.enc v)
  | .array t, v =>
    match v with
    | .seq vs => toBytes (word vs.length) ++ encSeqBA (vs.map fun x => (t.isDynamic, t.encBA x))
    | _ => ByteArray.empty
  | .fixedArray t _, v =>
    match v with
    | .seq vs => encSeqBA (vs.map fun x => (t.isDynamic, t.encBA x))
    | _ => ByteArray.empty
  | .tuple ts, v =>
    match v with
    | .seq vs => encSeqBA (encLBA ts vs)
    | _ => ByteArray.empty
def encLBA : List AbiType → List AbiValue → List (Bool × ByteArray)
  | [], _ => []
  | t :: ts, vs =>
    match vs with
    | v :: vs' => (t.isDynamic, t.encBA v) :: encLBA ts vs'
    | [] => []
end

theorem asLists_map (t : AbiType) (ih : ∀ v, ofBytes (t.encBA v) = t.enc v) (vs : List AbiValue) :
    asLists (vs.map fun x => (t.isDynamic, t.encBA x)) = vs.map fun x => (t.isDynamic, t.enc x) := by
  induction vs with
  | nil => rfl
  | cons v vs ihv =>
    rw [List.map_cons, asLists_cons, List.map_cons, ihv, ih v]

mutual
/-- Kind: implementation equals specification. Says: on every type and every value, well typed
    or not, the byte-array encoder gives exactly the bytes of the list specification.
    Does not say: anything about speed. -/
theorem encBA_eq : ∀ (t : AbiType) (v : AbiValue), ofBytes (t.encBA v) = t.enc v
  | .uint _, _ => by simp only [AbiType.encBA, ofBytes_toBytes]
  | .int _, _ => by simp only [AbiType.encBA, ofBytes_toBytes]
  | .address, _ => by simp only [AbiType.encBA, ofBytes_toBytes]
  | .bool, _ => by simp only [AbiType.encBA, ofBytes_toBytes]
  | .fixedBytes _, _ => by simp only [AbiType.encBA, ofBytes_toBytes]
  | .bytes, _ => by simp only [AbiType.encBA, ofBytes_toBytes]
  | .string, _ => by simp only [AbiType.encBA, ofBytes_toBytes]
  | .array t, v => by
    cases v with
    | seq vs =>
      simp only [AbiType.encBA, AbiType.enc]
      rw [ofBytes_append, ofBytes_toBytes, encSeqBA_eq, asLists_map t (fun x => encBA_eq t x) vs]
    | _ => simp [AbiType.encBA, AbiType.enc, ofBytes_empty]
  | .fixedArray t _, v => by
    cases v with
    | seq vs =>
      simp only [AbiType.encBA, AbiType.enc]
      rw [encSeqBA_eq, asLists_map t (fun x => encBA_eq t x) vs]
    | _ => simp [AbiType.encBA, AbiType.enc, ofBytes_empty]
  | .tuple ts, v => by
    cases v with
    | seq vs =>
      simp only [AbiType.encBA, AbiType.enc]
      rw [encSeqBA_eq, encLBA_eq ts vs]
    | _ => simp [AbiType.encBA, AbiType.enc, ofBytes_empty]
theorem encLBA_eq : ∀ (ts : List AbiType) (vs : List AbiValue), asLists (encLBA ts vs) = encL ts vs
  | [], _ => by simp [encLBA, encL, asLists]
  | t :: ts, vs => by
    cases vs with
    | nil => simp [encLBA, encL, asLists]
    | cons v vs =>
      simp only [encLBA, encL]
      rw [asLists_cons, encBA_eq t v, encLBA_eq ts vs]
end

/-- The encoding of an argument list, as a byte array. -/
def encodeArgsBytes (ts : List AbiType) (vs : List AbiValue) : ByteArray :=
  encSeqBA (encLBA ts vs)

/-- Kind: implementation equals specification. Says: `encodeArgsBytes` gives the bytes of
    `encodeArgs`.
    Does not say: anything about speed. -/
theorem encodeArgsBytes_eq (ts : List AbiType) (vs : List AbiValue) :
    ofBytes (encodeArgsBytes ts vs) = encodeArgs ts vs := by
  simp only [encodeArgsBytes, encodeArgs]
  rw [encSeqBA_eq, encLBA_eq]

end EthereumWallet.Abi
