import L4Factoidal.JS.Interp

/-!
# Theorems about the JavaScript engine

- `toInt32_range`, `toUint32_lt`: ToInt32 and ToUint32 (§7.1.6, §7.1.7) give
  values in their ranges, for every double.
- `arrayIndex?_lt`: an array index is below 2^32 - 1 (§6.1.7).
- `loopNext_*`: LoopContinues (§14.7.1.2): an unlabelled `break` ends the loop
  normally; `continue` and a normal body go on; `return` leaves.
- `sameValue_*`: SameValue is reflexive on the values that are not numbers, and
  tells `+0` from `-0`.
- `unitAt?_notAscii`: on a string that is not ASCII, `charCodeAt`'s unit is the entry of
  `Str.unitChars` (the array that `cachedChars` keeps), so indexing the cached array gives the
  answer of `Str.unitAt?`.
- `isPrivKey_privKey`, `forAwaitFn_private`, `forAwaitStmt_hasYield`: the helpers of
  `for await` are private-name keys, and its statements always go to the generator machine.
- `tick_spent`, `tick_step`, `charge_spent`, `charge_step`, `maxDenseArray_bounds`, `tick_full`,
  `tickCall_full`, `charge_full`, `heap_check_within_1024`: what a
  step and a charge do to the budget, and the dense-array limit.
- `strKey_not_priv`, `strKey_not_sym`, `keyStr_strKey`, `strKey_injective`,
  `strKey_ne_privKey`: the property key of a String value is never a private name's or a
  Symbol's key, is injective, and is undone by `keyStr`.
- `mixesCoalesce_iff`, `lexVarClash_iff`, `legacyEscapeIn_noBackslash`: the parser's early
  errors for `??` beside `&&`/`||` (§13.13), for a name of a lexical `for` head or catch
  parameter that the body also declares with `var` (§14.7, §14.15), and the strict-mode test for
  legacy escapes, which never flags a string literal without a backslash (§12.9.4.1).
- `typedLenOf_fits`, `typedLenOf_fixed`, `typedLenOf_auto`: TypedArrayLength (§10.4.5.12) never
  reaches past the buffer (every element index below it is inside the bytes), is the fixed
  length of a view in bounds, and for a length-tracking view the whole elements after the offset.
- `holdableIn_obj`, `holdableIn_registered`, `holdableIn_unregistered`, `holdableIn_prim`:
  CanBeHeldWeakly (§9.13) holds of every object and of every Symbol that the registry does not
  hold, and of no registered Symbol and no other primitive.
- `switchRealm_one_realm`, `switchRealm_unknown`, `tagFn_realm0`: with one realm (every page)
  the realm machinery leaves the heap as it was; an unknown realm is never entered.

The evaluator is a Lean function, so it is deterministic by construction: the same
script and heap give the same outcome and heap. Each function of the parser and of
the evaluator is total (structural recursion on its fuel); no partial definitions.
-/

namespace L4Factoidal.JS

theorem toInt32_range (x : Float) : -2147483648 ≤ toInt32 x ∧ toInt32 x < 2147483648 := by
  unfold toInt32
  split
  · omega
  · have h0 := Int.emod_nonneg (truncInt x) (b := 4294967296) (by decide)
    have h1 := Int.emod_lt_of_pos (truncInt x) (b := 4294967296) (by decide)
    dsimp only
    split <;> omega

theorem toUint32_lt (x : Float) : toUint32 x < 4294967296 := by
  unfold toUint32
  split
  · omega
  · have h0 := Int.emod_nonneg (truncInt x) (b := 4294967296) (by decide)
    have h1 := Int.emod_lt_of_pos (truncInt x) (b := 4294967296) (by decide)
    omega

/-! ## A Number as an array index, with no key string (`numIndex`, `typedElemNum`) -/

/-- The first digit of a positive number's decimal text is not `0`. -/
theorem head_toDigits_ne_zero : ∀ (n : Nat), 0 < n → (Nat.toDigits 10 n).head? ≠ some '0' := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hpos
    by_cases h : n < 10
    · rw [Nat.toDigits_of_lt_base h]
      have : n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 := by omega
      rcases this with h | h | h | h | h | h | h | h | h <;> subst h <;> decide
    · have h10 : 10 ≤ n := by omega
      rw [Nat.toDigits_of_base_le (by omega) h10]
      have hne : Nat.toDigits 10 (n / 10) ≠ [] := Nat.toDigits_ne_nil
      have := ih (n / 10) (by omega) (by omega)
      cases hd : Nat.toDigits 10 (n / 10) with
      | nil => exact absurd hd hne
      | cons a as => rw [hd] at this; simpa using this

theorem arrayIndex?_toString (i : Nat) (h : i < 4294967295) : arrayIndex? (toString i) = some i := by
  have hlen : (toString i).length ≤ 10 := by
    rw [Nat.toString_eq_repr, Nat.length_repr_le_iff (by omega)]; omega
  have hne : (toString i).isEmpty = false := by
    rw [String.isEmpty_eq_false_iff, Nat.toString_eq_repr]; exact Nat.repr_ne_empty
  have hall : (toString i).all Char.isDigit = true := by
    rw [String.all_bool_eq, Nat.toString_eq_repr, Nat.toList_repr, List.all_eq_true]
    intro c hc
    exact Nat.isDigit_of_mem_toDigits (by omega) (by omega) hc
  have hfront : ((toString i).length > 1 && (toString i).front == '0') = false := by
    by_cases h1 : (toString i).length > 1
    · have hi : 0 < i := by
        rcases Nat.eq_zero_or_pos i with h0 | h0
        · subst h0; exact absurd h1 (by decide)
        · exact h0
      have := head_toDigits_ne_zero i hi
      rw [String.front_eq, String.front?_eq, Nat.toString_eq_repr, Nat.toList_repr]
      cases hd : (Nat.toDigits 10 i).head? with
      | none => simp
      | some c =>
        rw [hd] at this
        have : c ≠ '0' := fun hc => this (by rw [hc])
        simp [this]
    · simp only [h1, decide_false, Bool.false_and]
  have hfold : (toString i).foldl (fun a c => a * 10 + (c.toNat - 48)) 0 = i := by
    rw [String.foldl_eq_foldl_toList, Nat.toString_eq_repr, Nat.toList_repr]
    have := Nat.ofDigitChars_ten_toDigits (n := i)
    rw [Nat.ofDigitChars_eq_foldl] at this
    have hf : (fun (a : Nat) (c : Char) => a * 10 + (c.toNat - 48)) = (fun sofar c => 10 * sofar + (c.toNat - '0'.toNat)) := by
      funext a c; rw [Nat.mul_comm]; rfl
    rw [hf]; exact this
  unfold arrayIndex?
  have hlen' : ¬ (toString i).length > 10 := by omega
  simp only [hne, hlen', hall, hfront, hfold, h]
  simp

theorem front_toString_isDigit (i : Nat) : (toString i).front.isDigit = true := by
  rw [String.front_eq, String.front?_eq, Nat.toString_eq_repr, Nat.toList_repr]
  cases hd : Nat.toDigits 10 i with
  | nil => exact absurd hd Nat.toDigits_ne_nil
  | cons a as =>
    have : a ∈ Nat.toDigits 10 i := by rw [hd]; simp
    simpa using Nat.isDigit_of_mem_toDigits (by omega) (by omega) this

/-- **Kind: refinement.** When `numIndex x` is an index, the key of `x` is the decimal text of that
index. By the cases of `numToString`; nothing is assumed about floating-point arithmetic. -/
theorem keyOfNum_numIndex (x : Float) (h : numIndex x < noIndex) : keyOfNum x = toString (numIndex x) := by
  by_cases h1 : x.isNaN = true
  · rw [numIndex, if_pos h1] at h; exact absurd h (Nat.lt_irrefl _)
  by_cases h2 : (x == 0) = true
  · rw [numIndex, if_neg h1, if_pos h2, keyOfNum, numToString, if_neg h1, if_pos h2]; rfl
  by_cases h3 : x.isInf = true
  · rw [numIndex, if_neg h1, if_neg h2, if_pos h3] at h; exact absurd h (Nat.lt_irrefl _)
  by_cases h4 : (isIntegral x && decide (x.abs < tenPow21)) = true
  · rw [numIndex, if_neg h1, if_neg h2, if_neg h3, if_pos h4] at h ⊢
    rw [keyOfNum, numToString, if_neg h1, if_neg h2, if_neg h3, if_pos h4]
    cases hti : truncInt x with
    | ofNat i =>
      rw [hti] at h
      by_cases hlt : i < noIndex
      · simp only [hlt, if_true, decide_true, Bool.true_or]; rfl
      · simp only [hlt, if_false] at h; exact absurd h (Nat.lt_irrefl _)
    | negSucc i => rw [hti] at h; exact absurd h (Nat.lt_irrefl _)
  · rw [numIndex, if_neg h1, if_neg h2, if_neg h3, if_neg h4] at h; exact absurd h (Nat.lt_irrefl _)

theorem arrayIndex?_keyOfNum (x : Float) (h : numIndex x < noIndex) :
    arrayIndex? (keyOfNum x) = some (numIndex x) := by
  rw [keyOfNum_numIndex x h]; exact arrayIndex?_toString _ h

theorem front_keyOfNum (x : Float) (h : numIndex x < noIndex) : (keyOfNum x).front.isDigit = true := by
  rw [keyOfNum_numIndex x h]; exact front_toString_isDigit _

/-- The key of an index Number does not start with the private-name mark (a digit is not it). -/
theorem front_keyOfNum_privMark (x : Float) (h : numIndex x < noIndex) :
    ((keyOfNum x).front == privMark) = false := by
  have hd := front_keyOfNum x h
  cases he : ((keyOfNum x).front == privMark) with
  | false => rfl
  | true =>
    have hc : (keyOfNum x).front = privMark := by simpa using he
    rw [hc] at hd; exact absurd hd (by decide)

theorem isPrivKey_keyOfNum (x : Float) (h : numIndex x < noIndex) : isPrivKey (keyOfNum x) = false :=
  front_keyOfNum_privMark x h

/-- **Kind: refinement.** `[[Get]]` of a typed array's element by the key of a Number is the pure
read `typedElemAt` of that index, with the heap unchanged, at every fuel but 0. -/
theorem getV_typedElem {H : Type} (n id : Nat) (x : Float) (h : HeapOf H) (v : Value) (hx : numIndex x < noIndex)
    (hv : typedElemAt h id (numIndex x) = v) (hne : v ≠ .hole) :
    getV (n + 1) (.obj id) (keyOfNum x) h = .ok v h := by
  rw [getV.eq_def]
  unfold typedElemAt at hv
  cases hk : (h.obj id).kind with
  | typed ty b off len =>
    rw [hk] at hv
    simp only [front_keyOfNum_privMark x hx, Bool.false_eq_true, if_false, front_keyOfNum x hx, arrayIndex?_keyOfNum x hx, if_true]
    simp only [getObj, liveLen, bind, EStateM.bind, pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, hk]
    rw [← hv]
  | _ => rw [hk] at hv; exact absurd hv.symm hne

/-- **Kind: refinement.** The form the evaluator and the register machine now write for `o[x]`
with a Number `x` on an object that is not an Array (`typedElemNum` first, `getV` on the key of
`x` when it answers `Value.hole`) runs as `getV` on the key of `x` alone, from every heap, at
every fuel but 0 (at fuel 0 `getV` is out of fuel). Does not say anything about speed. -/
theorem getV_typedElemNum {H : Type} (n id : Nat) (x : Float) (h : HeapOf H) :
    (match typedElemNum h id x with
      | .hole => getV (n + 1) (.obj id) (keyOfNum x)
      | w => pure w : JSM H Value) h = getV (n + 1) (.obj id) (keyOfNum x) h := by
  cases hv : typedElemNum h id x with
  | hole => rfl
  | _ =>
    unfold typedElemNum at hv
    by_cases hx : numIndex x < noIndex
    · simp only [hx, if_true] at hv
      exact (getV_typedElem n id x h _ hx hv (by simp)).symm
    · simp only [hx, if_false] at hv; cases hv

/-- ToPropertyKey of a Number is its key, with any fuel left (the evaluator's `.index` arm and
`vmGetIndex` reach `getV` through it). -/
theorem toKey_num {H : Type} (n : Nat) (x : Float) : toKey (H := H) (n + 1) (.num x) = pure (keyOfNum x) := by
  rw [toKey.eq_def]

#print axioms arrayIndex?_toString
#print axioms arrayIndex?_keyOfNum
#print axioms getV_typedElemNum

/-- **Kind: refinement.** `vmStash`, a value that needs no evaluation, then `vmTake`, is `vmSettle`
with the registers kept: the same heap and the same registers for the continuation, for every
heap. The register machine's read of a typed array's element uses it. -/
theorem vmStash_pure_vmTake {H α : Type} (regs : Array Value) (fregs : FloatArray) (top : Nat) (w : Value)
    (k : Value → Array Value × FloatArray → JSM H α) :
    (do vmStash regs fregs top
        let v ← (pure w : JSM H Value)
        let r ← vmTake
        k v r) = (do vmSettle top; k w (regs, fregs)) := by
  funext h
  rfl

#print axioms vmStash_pure_vmTake

/-! ## ToNumber of a Number (the `toNumQ` form of `JS/Interp.lean`) -/

/-- ToNumber of a Number is that Number, with any fuel left. -/
theorem toNum_num {H : Type} (n : Nat) (x : Float) : toNum (H := H) (n + 1) (.num x) = pure x := by
  rw [toNum.eq_def]

/-- Out of fuel at 0, whatever the value. -/
theorem toNum_zero {H : Type} (v : Value) : toNum (H := H) 0 v = throw (.halt "fuel") := by
  rw [toNum.eq_def]

/-- **Kind: refinement.** The form the evaluator now writes for ToNumber of an operand (`toNumQ`:
a Number is answered with no call) is `toNum` at every fuel but 0, for every value. At fuel 0
`toNum` is out of fuel (`toNum_zero`) and the form answers a Number; the fuel is not a script's
budget, and a run that is out of fuel at one fuel is the same run at a larger one
(`FuelMonoAll.IH_all`). Does not say anything about speed. -/
theorem toNumQ_succ {H : Type} (n : Nat) (v : Value) :
    (match v with | Value.num x => pure x | w => toNum (n + 1) w : JSM H Float) = toNum (n + 1) v := by
  cases v <;> first | rfl | exact (toNum_num n _).symm

/-- **Kind: refinement.** `typedConv` of a Number for a Number element type: the arm that now
answers the Number itself gives what the `toNum` call it replaced gave (with fuel for that call). -/
theorem typedConv_num_arm {H : Type} (n : Nat) (x : Float) :
    (do pure (Value.num (← toNum (n + 1) (.num x))) : JSM H Value) = pure (.num x) := by
  rw [toNum_num]; rfl

theorem typedConv_num {H : Type} (n ty : Nat) (x : Float) (h : typedIsBig ty = false) :
    typedConv (H := H) (n + 1) ty (.num x) = pure (.num x) := by
  rw [typedConv.eq_def]
  first | (simp only [h, Bool.false_eq_true, ↓reduceIte]; done) | (simp only [h]; rfl) | simp [h]

#print axioms toNumQ_succ
#print axioms typedConv_num_arm
#print axioms typedConv_num

/-! ## A typed array's element written by a Number, with no key string (`typedSetNum`) -/

/-- An array with a cell swapped out and put back is the array. -/
theorem swapAt_set_same (objs : Array Obj) (id : Nat) (h : id < objs.size) :
    (objs.swapAt! id default).2.set! id (objs.swapAt! id default).1 = objs := by
  simp only [Array.swapAt!, h, dite_true, Array.swapAt, Array.set!_eq_setIfInBounds]
  apply Array.ext
  · simp
  · intro j hj1 hj2
    by_cases hji : id = j
    · subst hji; rw [Array.getElem_setIfInBounds_self]
    · rw [Array.getElem_setIfInBounds_ne (by simpa using hj2) hji, Array.getElem_set_ne _ _ hji]
#print axioms swapAt_set_same

theorem HeapOf.obj_eq_getElem {H : Type} (h : HeapOf H) (id : Nat) (hid : id < h.objs.size) : h.obj id = h.objs[id] := by
  simp [HeapOf.obj, Array.getD, hid]

/-- A change that leaves the object as it was leaves the heap as it was, when no undo log covers the object. -/
theorem updateObj_keep {H : Type} {α} [Inhabited α] (id : Nat) (f : Obj → α × Obj) (h : HeapOf H) (a : α)
    (hb : h.undoObjs.base ≤ id) (hid : id < h.objs.size) (hf : f (h.obj id) = (a, h.obj id)) :
    updateObj id f h = .ok a h := by
  have hnb : ¬ id < h.undoObjs.base := by omega
  rw [HeapOf.obj_eq_getElem h id hid] at hf
  unfold updateObj
  simp only [modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, HeapOf.noteObj, hnb, if_false, hid, if_true, takeAt]
  have h1 : (h.objs.swapAt! id default).fst = h.objs[id] := by
    simp [Array.swapAt!, hid, Array.swapAt]
  have h2 := swapAt_set_same h.objs id hid
  rw [h1] at h2 ⊢
  rw [hf]
  simp only [h2]
#print axioms updateObj_keep

theorem obj_lt_of_typed {H : Type} (h : HeapOf H) (id ty b off len : Nat) (hk : (h.obj id).kind = .typed ty b off len) :
    id < h.objs.size := by
  apply Classical.byContradiction
  intro hn
  have : h.obj id = default := by simp [HeapOf.obj, Array.getD, hn]
  rw [this] at hk
  cases hk

theorem setElem_typed {H : Type} (h : HeapOf H) (id i ty b off len : Nat) (v : Value)
    (hk : (h.obj id).kind = .typed ty b off len) (hb : h.undoObjs.base ≤ id) :
    setElem id i v h = .ok false h := by
  unfold setElem
  exact updateObj_keep id _ h false hb (obj_lt_of_typed h id ty b off len hk) (by simp only [hk])

theorem setOwnData_typed {H : Type} (h : HeapOf H) (id ty b off len : Nat) (key : String) (v : Value)
    (hk : (h.obj id).kind = .typed ty b off len) (hb : h.undoObjs.base ≤ id) :
    setOwnData id key v h = .ok false h := by
  unfold setOwnData
  exact updateObj_keep id _ h false hb (obj_lt_of_typed h id ty b off len hk) (by simp only [hk, ite_self])
#print axioms setOwnData_typed

theorem bind_pure_unit {H : Type} (m : JSM H Unit) : (EStateM.bind m fun _ => EStateM.pure ()) = m := by
  funext s
  unfold EStateM.bind
  cases m s <;> rfl

/-- **Kind: refinement.** `[[Set]]` of a Number on a typed array of a Number element type, by the
key of an index Number, when no undo log covers the object: the element write `typedWriteV` (or
nothing past the live length), given that `typedConv` answers the Number (`typedConv_num`). -/
theorem putV_typedNum {H : Type} (n id : Nat) (x y : Float) (strict : Bool) (h : HeapOf H) (ty b off len : Nat)
    (hk : (h.obj id).kind = .typed ty b off len) (hb : h.undoObjs.base ≤ id)
    (hx : numIndex x < noIndex)
    (hconv : typedConv (H := H) n ty (.num y) = pure (.num y)) :
    putV (n + 1) (.obj id) (keyOfNum x) (.num y) strict h =
      (if numIndex x < (typedLenOf (isDetached (h.obj b)) off len (elemSize ty) (bufferBytes (h.obj b)).size)
        then typedWriteV ty b off (numIndex x) (.num y) else pure ()) h := by
  rw [putV.eq_def]
  simp only [bind, EStateM.bind, setOwnData_typed h id ty b off len _ _ hk hb, getObj, pure, EStateM.pure, get, getThe,
    MonadStateOf.get, EStateM.get, hk, arrayIndex?_keyOfNum x hx, hconv, liveLen,
    isPrivKey_keyOfNum x hx, Bool.false_eq_true, if_false]
  try simp only [EStateM.bind, EStateM.get, EStateM.pure, Bool.false_eq_true, if_false, hk, hconv, pure]
  try simp only [bind_pure_unit]
#print axioms putV_typedNum

/-- **Kind: refinement.** The form the evaluator and the register machine now write for `o[x] = v`
with a Number `x`, after the Array path has declined (`typedSetNum` first, `putV` on the key of `x`
when it answers `false`) runs as `putV` alone, from every heap and for every value, with fuel 2
or more for `putV` (below that `putV` is out of fuel before it stores). Does not say anything
about speed. -/
theorem typedSetNum_refines {H : Type} (n id : Nat) (x : Float) (v : Value) (strict : Bool) (h : HeapOf H) :
    (do let done ← typedSetNum id x v
        if !done then putV (n + 2) (.obj id) (keyOfNum x) v strict : JSM H Unit) h
    = putV (n + 2) (.obj id) (keyOfNum x) v strict h := by
  unfold typedSetNum
  simp only [bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get, pure, EStateM.pure]
  cases hk : (h.obj id).kind with
  | typed ty b off len =>
    cases v with
    | num y =>
      simp only []
      by_cases hc : (decide (numIndex x < noIndex) && !typedIsBig ty && decide (h.undoObjs.base ≤ id)) = true
      · have hc' := hc
        simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at hc'
        obtain ⟨⟨hx, hbig⟩, hb⟩ := hc'
        simp only [hc, if_true]
        rw [putV_typedNum (n + 1) id x y strict h ty b off len hk hb hx (typedConv_num n ty y hbig)]
        by_cases hl : numIndex x < (typedLenOf (isDetached (h.obj b)) off len (elemSize ty) (bufferBytes (h.obj b)).size)
        · simp only [hl, if_true]
          unfold EStateM.bind
          cases typedWriteV ty b off (numIndex x) (Value.num y) h <;> rfl
        · simp only [hl, if_false]; rfl
      · simp only [hc]; rfl
    | _ => rfl
  | _ => rfl

#print axioms updateObj_keep
#print axioms putV_typedNum
#print axioms typedSetNum_refines

theorem arrayIndex?_lt {s : String} {n : Nat} (h : arrayIndex? s = some n) : n < 4294967295 := by
  unfold arrayIndex? at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · dsimp only at h
        split at h
        · rename_i hlt; cases h; exact hlt
        · simp at h

theorem loopNext_break (ls : List String) : loopNext ls (.brk none) = some .normal := rfl
theorem loopNext_continue (ls : List String) : loopNext ls (.cont none) = none := rfl
theorem loopNext_normal (ls : List String) : loopNext ls .normal = none := rfl
theorem loopNext_return (ls : List String) (v : Value) : loopNext ls (.ret v) = some (.ret v) := rfl
theorem loopNext_label (l : String) (ls : List String) :
    loopNext (l :: ls) (.brk (some l)) = some .normal := by simp [loopNext]

theorem sameValue_str (s : String) : sameValue (.str s) (.str s) = true := by
  simp [sameValue, strictEq]

theorem sameValue_obj (i : Nat) : sameValue (.obj i) (.obj i) = true := by
  simp [sameValue, strictEq]

theorem sameValue_bool (b : Bool) : sameValue (.bool b) (.bool b) = true := by
  simp [sameValue, strictEq]

theorem toBool_obj (i : Nat) : toBool (.obj i) = true := rfl
theorem toBool_undef : toBool .undef = false := rfl

/-- Kind: an equation of definitions (the fast path is the definition's own branch).
Says: for a string that is not ASCII, `Str.unitAt? s i` is entry `i` of `Str.unitChars s` read
as a unit, which is what `charCodeAt` computes from `cachedChars` when the cache holds `s`.
Does not say: that the cache holds `s` (the evaluator compares the strings before it uses it), or
anything about `charAt`, whose answer `#guard`s in `RegressionTests` check. -/
theorem unitAt?_notAscii (s : String) (i : Nat) (h : Str.isAscii s = false) :
    Str.unitAt? s i = (Str.unitChars s)[i]?.map Str.charUnit := by
  simp [Str.unitAt?, h]

/-- Kind: an equation of definitions.
Says: for an ASCII string, and for any string when the heap holds no cached string or a different
one, `strLength` is `Str.jsLength` (the cached path is the only other case).
Does not say: that the cached array's size is `Str.jsLength` of its string (checked by `#guard`s
in `RegressionTests`, not proved). -/
theorem strLength_uncached {H : Type} (h : HeapOf H) (s : String)
    (hc : h.reCache = none ∨ ∃ t cs, h.reCache = some (t, cs) ∧ t ≠ s) :
    h.strLength s = Str.jsLength s := by
  unfold HeapOf.strLength
  split
  · rename_i ha; simp [Str.jsLength, ha]
  · rcases hc with hc | ⟨t, cs, hc, hne⟩
    · simp [hc]
    · simp [hc, hne]

/-! ## `for await` (`forAwaitStmt`, `forAwaitFn`) -/

/-- Kind: a property of the key encoding.
Says: the key of a private name is recognised as one (`isPrivKey`), whatever the name.
Does not say: that no other string is recognised as one. -/
theorem isPrivKey_privKey (name : String) : isPrivKey (privKey name) = true := by
  simp [isPrivKey, privKey, String.front_eq, String.front?_eq, String.toList_append]

/-- Kind: a property of the key encoding.
Says: each name the statements of `for await` call is a private-name key, so the engine's
listings of an object's keys leave it out (they filter `isPrivKey`), and no identifier of
source text spells it (an identifier does not start with U+10FFFE).
Does not say: that a computed property key cannot spell it. -/
theorem forAwaitFn_private (k : Nat) : isPrivKey (forAwaitFn k) = true := isPrivKey_privKey _

/-- Kind: an invariant of the parser's output.
Says: the statements made for a `for await` hold an `await` (a `yield` of the generator
machine) for every head and body, so `genRun` runs them and the plain evaluator, which
refuses a `yield`, never does.
Does not say: that the statements behave as §14.7.5.7 says (the `#guard`s of
`RegressionTests` and Test262's `for-await-of` check that). -/
theorem forAwaitStmt_hasYield (inGen : Bool) (uid : Nat) (kind : Option DeclKind) (pat : Pat)
    (obj : Expr) (body : Stmt) : (forAwaitStmt inGen uid kind pat obj body).hasYield = true := by
  have h : ∀ n, Stmt.hasYieldF (n + 16) (forAwaitStmt inGen uid kind pat obj body) = true := by
    intro n
    cases inGen <;> simp [forAwaitStmt, Stmt.hasYieldF, Stmt.anyYield, Decl.anyYield, Expr.hasYieldF]
  exact h 99984

/-! ## Property keys (`strKey`, `keyStr`, `privKey`, `symKey`)

ToPropertyKey of a String value is `strKey` (`toKey`'s `.str` case, the parser's string
property names, `JSON.parse`'s member names); listings of keys give `keyStr`. -/

/-- Kind: a lemma about strings. Says: a string that starts with a character starts with it. -/
theorem front_singleton_append (c : Char) (s : String) : (String.singleton c ++ s).front = c := by
  simp [String.front_eq, String.front?_eq, String.toList_append]

/-- Kind: a lemma about strings. Says: dropping the first character gives the rest back. -/
theorem drop_one_singleton_append (c : Char) (s : String) :
    ((String.singleton c ++ s).drop 1).toString = s := by
  apply String.ext
  simp [String.toList_append]

/-- Kind: a property of the key encoding.
Says: the key of a String value starts with `strMark` or with a character that is not reserved.
Does not say: which of the two (a string that starts with a reserved character gets the mark). -/
theorem strKey_front (s : String) :
    (strKey s).front = strMark ∨ keyReserved (strKey s).front = false := by
  unfold strKey
  split
  · left; exact front_singleton_append _ _
  · right; rename_i h; simpa using h

/-- Kind: a security property of the key encoding (the defect behind WPT `names.wast`).
Says: no String value has a private name's key: for every string `s`, `strKey s` is not
recognised by `isPrivKey`. So a computed member access, `in`, `Object.defineProperty`,
`JSON.parse` and every other use of ToPropertyKey on a string cannot reach a private member
or the hidden helpers of the global object.
Does not say: that every place that makes a key from a string calls `strKey` (`toKey`, the
parser's string property names and `JSON.parse` do; the `#guard`s of `RegressionTests` check
them), or anything about the embedding host's own property names. -/
theorem strKey_not_priv (s : String) : isPrivKey (strKey s) = false := by
  unfold isPrivKey
  rcases strKey_front s with h | h
  · rw [h]; decide
  · cases hf : (strKey s).front == Char.ofNat 0x10FFFE
    · rfl
    · have h2 : (strKey s).front = Char.ofNat 0x10FFFE := eq_of_beq hf
      rw [h2] at h
      exact absurd h (by decide)

/-- Kind: a security property of the key encoding.
Says: the key that marks an Array whose elements left the fast form (`arrayMarkKey`) is a
private key, so no String value has it: `o["..."]`, `in`, `Object.defineProperty` and
`JSON.parse` can not read, write or forge the mark, and only the engine decides IsArray.
Does not say: more than `strKey_not_priv` does about where `strKey` is called. -/
theorem arrayMarkKey_priv : isPrivKey arrayMarkKey = true := by decide

theorem strKey_ne_arrayMarkKey (s : String) : strKey s ≠ arrayMarkKey := by
  intro h
  have h1 := strKey_not_priv s
  rw [h, arrayMarkKey_priv] at h1
  exact Bool.noConfusion h1

/-- Kind: a security property of the key encoding.
Says: no String value has a Symbol's key: `strKey s` is not recognised by `isSymKey`, so
`o["\u{10FFFF}0"]` is not the property of `Symbol.iterator`.
Does not say: more than `strKey_not_priv` does about where `strKey` is called. -/
theorem strKey_not_sym (s : String) : isSymKey (strKey s) = false := by
  unfold isSymKey
  rcases strKey_front s with h | h
  · rw [h]; decide
  · cases hf : (strKey s).front == symMark
    · rfl
    · have h2 : (strKey s).front = symMark := eq_of_beq hf
      rw [h2] at h
      exact absurd h (by decide)

/-- Kind: a round trip.
Says: `keyStr` gives back the string `strKey` was given, so `Object.keys`, `for`-`in`,
`Reflect.ownKeys` and `JSON.stringify` name a property by the string it was made with.
Does not say: what `keyStr` gives for a key that `strKey` did not make. -/
theorem keyStr_strKey (s : String) : keyStr (strKey s) = s := by
  unfold strKey
  split
  · unfold keyStr
    rw [front_singleton_append, if_pos (by decide)]
    exact drop_one_singleton_append _ _
  · rename_i h
    unfold keyStr
    have hf : (s.front == strMark) = false := by
      cases hf : s.front == strMark
      · rfl
      · have h2 : s.front = strMark := eq_of_beq hf
        rw [h2] at h
        exact absurd h (by decide)
    rw [hf]
    rfl

/-- Kind: injectivity of the key encoding.
Says: different String values have different keys.
Does not say: anything about numbers (`keyOfNum`) or Symbols (`symKey`), whose keys are
kept apart from a string's by `strKey_not_sym` and by their own forms. -/
theorem strKey_injective (s t : String) (h : strKey s = strKey t) : s = t := by
  have := congrArg keyStr h
  simpa [keyStr_strKey] using this

/-- Kind: a corollary. Says: a String value's key is never the key of a private name. -/
theorem strKey_ne_privKey (s name : String) : strKey s ≠ privKey name := by
  intro h
  have h1 := strKey_not_priv s
  rw [h, isPrivKey_privKey] at h1
  cases h1

/-! ## The step budget (`tick`, `charge`)

Every loop iteration, call and job of a script takes a step (`tick`), and a built-in that
loops inside the engine takes steps for the size of its work (`charge`). These four say what
one of them does to the budget. -/

/-- Kind: a refusal. Says: with no steps left, `tick` halts the run and changes nothing.
Does not say: that every loop of the evaluator ticks (its loops are written with `tick`; that
is read from the code, not proved). -/
theorem tick_spent {H : Type} (h : HeapOf H) (h0 : h.steps = 0) :
    (tick : JSM H Unit).run h = .error (.halt "step budget exhausted") h := by
  simp [tick, h0, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- Kind: a cost. Says: with steps left, and the heap within its size, `tick` takes exactly
one step and changes nothing else. -/
theorem tick_step {H : Type} (h : HeapOf H) (h0 : h.steps ≠ 0) (hf : h.full = false) :
    (tick : JSM H Unit).run h = .ok () { h with steps := h.steps - 1 } := by
  simp [tick, h0, hf, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get, EStateM.get,
    set, MonadStateOf.set, EStateM.set]

/-! ## Redefining a property (`Desc.allowedOn`, §10.1.6.3)

`Object.defineProperty` on a property that is not configurable: what may change. Before
2026-11-14 the engine refused every redefinition of a property that was neither configurable
nor writable, also one that changed nothing (`Object.defineProperty(C, 'prototype', {
writable: false })` on a class), and let the enumerability of a writable one be asked for. -/

/-- Kind: a specification. Says: a configurable property accepts every descriptor. -/
theorem allowedOn_configurable (d : Desc) (cur : PropV) (h : cur.configurable = true) : d.allowedOn cur = true := by
  simp [Desc.allowedOn, h]

/-- Kind: a specification. Says: a descriptor with no fields is accepted on every property (it
asks for no change). -/
theorem allowedOn_empty (cur : PropV) : ({} : Desc).allowedOn cur = true := by
  cases cur <;> simp [Desc.allowedOn]

/-- Kind: a refusal (object integrity). Says: a property that is not configurable never
becomes configurable. -/
theorem allowedOn_stays_unconfigurable (d : Desc) (cur : PropV) (hc : cur.configurable = false)
    (h : d.allowedOn cur = true) : d.configurable ≠ some true := by
  intro hd
  simp [Desc.allowedOn, hc, hd] at h

/-- Kind: a refusal (object integrity: frozen data stays). Says: a data property that is
neither configurable nor writable keeps its value: an accepted descriptor that names a value
names the same value (SameValue), and does not make the property writable.
Does not say: that `defineFromDescriptor` asks `allowedOn` for every exotic object (it does for
ordinary objects and arrays; typed arrays and Proxies have their own paths). -/
theorem allowedOn_frozen (d : Desc) (v : Value) (e : Bool) (h : d.allowedOn (.data v false e false) = true) :
    d.writable ≠ some true ∧ ∀ x, d.value = some x → sameValue x v = true := by
  constructor
  · intro hw
    simp [Desc.allowedOn, PropV.configurable, hw] at h
  · intro x hx
    cases hs : sameValue x v with
    | true => rfl
    | false => simp [Desc.allowedOn, PropV.configurable, hx, hs] at h

/-- Kind: a refusal. Says: an accessor that is not configurable keeps its getter and setter
and does not become a data property. -/
theorem allowedOn_accessor (d : Desc) (g s : Value) (e : Bool) (h : d.allowedOn (.acc g s e false) = true) :
    d.value = none ∧ d.writable = none ∧ (∀ x, d.get = some x → sameValue x g = true) ∧
      (∀ x, d.set = some x → sameValue x s = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · cases hv : d.value with
    | none => rfl
    | some x => simp [Desc.allowedOn, PropV.configurable, hv] at h
  · cases hv : d.writable with
    | none => rfl
    | some x => simp [Desc.allowedOn, PropV.configurable, hv] at h
  · intro x hx
    cases hs : sameValue x g with
    | true => rfl
    | false => simp [Desc.allowedOn, PropV.configurable, hx, hs] at h
  · intro x hx
    cases hs : sameValue x s with
    | true => rfl
    | false => simp [Desc.allowedOn, PropV.configurable, hx, hs] at h

/-! ## The prototype of a function made from source (`Realm.closureProto`)

Generator, async generator and async functions inherit from %GeneratorFunction.prototype%,
%AsyncGeneratorFunction.prototype% and %AsyncFunction.prototype% (§27.3.3, §27.4.3, §27.7.3);
before 2026-11-14 every function inherited from Function.prototype, so
`Object.getPrototypeOf(function* () {}).prototype` was undefined. -/

/-- Kind: totality. Says: a function never gets object 0 as its prototype (the slot of a realm
that has not made the intrinsic yet), when Function.prototype is made. -/
theorem orFn_ne_zero (r : Realm) (p : Nat) (h : r.functionProto ≠ 0) : r.orFn p ≠ 0 := by
  unfold Realm.orFn
  split <;> assumption

theorem closureProto_ne_zero (r : Realm) (gen async : Bool) (h : r.functionProto ≠ 0) :
    r.closureProto gen async ≠ 0 :=
  orFn_ne_zero r _ h

/-- Kind: a specification. Says: an ordinary function (neither generator nor async) inherits
from Function.prototype. -/
theorem closureProto_plain (r : Realm) : r.closureProto false false = r.functionProto := by
  simp [Realm.closureProto, Realm.closureProtoRaw, Realm.orFn]

/-- Kind: a specification. Says: once the realm has %GeneratorFunction.prototype%, a generator
function inherits from it, and likewise for the async kinds. -/
theorem closureProto_gen (r : Realm) (h : r.genFnProto ≠ 0) : r.closureProto true false = r.genFnProto := by
  simp [Realm.closureProto, Realm.closureProtoRaw, Realm.orFn, h]

theorem closureProto_asyncGen (r : Realm) (h : r.asyncGenFnProto ≠ 0) :
    r.closureProto true true = r.asyncGenFnProto := by
  simp [Realm.closureProto, Realm.closureProtoRaw, Realm.orFn, h]

theorem closureProto_async (r : Realm) (h : r.asyncFnProto ≠ 0) : r.closureProto false true = r.asyncFnProto := by
  simp [Realm.closureProto, Realm.closureProtoRaw, Realm.orFn, h]

/-! ## Changing a prototype (`protoChangeAllowed`, §10.1.2.1, §10.4.7.2)

Before 2026-11-14 `Object.setPrototypeOf` and `Reflect.setPrototypeOf` set any prototype: on a
frozen object, on Object.prototype, and into a cycle. -/

/-- Kind: a specification. Says: setting the prototype an object already has is accepted. -/
theorem protoChange_same (o : Nat) (cur v : Value) (e i : Bool) (ch : List Nat) (h : sameValue v cur = true) :
    protoChangeAllowed o cur v e i ch = true := by
  simp [protoChangeAllowed, h]

/-- Kind: a refusal (object integrity). Says: an immutable prototype exotic object, or an object
that is not extensible, keeps its prototype: an accepted change is no change. -/
theorem protoChange_fixed (o : Nat) (cur v : Value) (e i : Bool) (ch : List Nat) (hf : i = true ∨ e = false)
    (h : protoChangeAllowed o cur v e i ch = true) : sameValue v cur = true := by
  cases hs : sameValue v cur with
  | true => rfl
  | false =>
    rcases hf with hi | he
    · simp [protoChangeAllowed, hs, hi] at h
    · simp [protoChangeAllowed, hs, he] at h

/-- Kind: a refusal (no cycles). Says: an accepted change to a new prototype never puts the
object on its own prototype chain (as far as the walk sees it). -/
theorem protoChange_no_cycle (o : Nat) (cur v : Value) (e i : Bool) (ch : List Nat)
    (h : protoChangeAllowed o cur v e i ch = true) (hs : sameValue v cur = false) : o ∉ ch := by
  intro hm
  simp_all [protoChangeAllowed]

/-! ## Function declarations in a block (`blockFunsOk`, §14.2.1, B.3.2.4) -/

/-- Kind: a refusal. Says: in strict code the function declarations of a block have distinct names. -/
theorem blockFunsOk_strict (fd : List (String × Bool)) (h : blockFunsOk true fd = true) :
    (fd.map (·.1)).eraseDups.length = (fd.map (·.1)).length := by
  simpa [blockFunsOk] using h
/-- Kind: a specification. Says: function declarations with distinct names are always accepted. -/
theorem blockFunsOk_distinct (s : Bool) (fd : List (String × Bool))
    (h : (fd.map (·.1)).eraseDups.length = (fd.map (·.1)).length) : blockFunsOk s fd = true := by
  simp [blockFunsOk, h]
/-- Kind: a refusal (Annex B.3.2.4 is for plain functions only). Says: when names repeat, a
generator or async function declaration's name is not one of the repeated ones. -/
theorem blockFunsOk_special (s : Bool) (fd : List (String × Bool)) (h : blockFunsOk s fd = true)
    (hd : (fd.map (·.1)).eraseDups.length ≠ (fd.map (·.1)).length) (x : String) (hx : (x, true) ∈ fd) :
    (fd.map (·.1)).count x = 1 := by
  simp [blockFunsOk] at h hd
  rcases h with h | ⟨_, h⟩
  · exact absurd h hd
  · exact h x hx
/-! ## Class elements, `super` and `new.target` early errors (parser, §15.7.1, §15.2.1) -/

/-- Kind: a refusal (§15.7.1). Says: a getter, setter, generator or async method is never named "constructor". -/
theorem classElementOk_special_ctor (k : Bool) : classElementOk false true k (.lit "constructor") = false := by
  cases k <;> rfl
/-- Kind: a refusal. Says: no static member is named "prototype". -/
theorem classElementOk_static_prototype (sp f : Bool) : classElementOk true sp f (.lit "prototype") = false := by
  cases sp <;> cases f <;> rfl
/-- Kind: a refusal. Says: no field is named "constructor". -/
theorem classElementOk_field_ctor (st sp : Bool) : classElementOk st sp true (.lit "constructor") = false := by
  cases st <;> cases sp <;> rfl
/-- Kind: a specification. Says: a computed key has no PropName and is never refused. -/
theorem classElementOk_computed (st sp f : Bool) (e : Expr) : classElementOk st sp f (.computed e) = true := rfl
/-- Kind: a refusal (§15.7.1). Says: `super(...)` is allowed only in a derived class constructor or an arrow function inside a place that allows it. -/
theorem superCallIn_derived (k : FunKind) (o : Bool) (h : superCallIn k o = true) :
    k = .ctor true ∨ (k = .arrow ∧ o = true) := by
  cases k with
  | ctor d => cases d <;> simp_all [superCallIn]
  | arrow => simp_all [superCallIn]
  | normal => simp [superCallIn] at h
  | method => simp [superCallIn] at h
/-- Kind: a refusal (§15.2.1). Says: a plain function body never allows `super.x`. -/
theorem superPropIn_normal (o : Bool) : superPropIn .normal o = false := rfl

/-- Kind: a refusal (§15.4.1). Says: an accepted getter has no parameters and no rest parameter. -/
theorem accessorParamsOk_getter (c : Nat) (r : Bool) (h : accessorParamsOk true c r = true) : c = 0 ∧ r = false := by
  simp [accessorParamsOk] at h; exact ⟨h.2, h.1⟩

/-- Kind: a refusal. Says: an accepted setter has exactly one parameter and no rest parameter. -/
theorem accessorParamsOk_setter (c : Nat) (r : Bool) (h : accessorParamsOk false c r = true) : c = 1 ∧ r = false := by
  simp [accessorParamsOk] at h; exact ⟨h.2, h.1⟩

/-! ## ValidateTypedArray (`typedOob`, §10.4.5.11, §23.2.4.4) -/

/-- Kind: a refusal. Says: a fixed-length view that is in bounds is on a live buffer and its
bytes fit in it; a length-tracking view (`autoLen`) in bounds starts inside it. -/
theorem typedOob_false (d : Bool) (off len e size : Nat) (h : typedOob d off len e size = false) :
    d = false ∧ (if len = autoLen then off ≤ size else off + len * e ≤ size) := by
  unfold typedOob at h
  cases d <;> simp at h
  by_cases ha : len = autoLen
  · simp [ha] at h ⊢; omega
  · have hb : (len == autoLen) = false := by simp [ha]
    simp [hb, ha] at h ⊢; omega

/-- Kind: a refusal. Says: a detached buffer is always out of bounds. -/
theorem typedOob_detached (off len e size : Nat) : typedOob true off len e size = true := by
  simp [typedOob]

/-! ## A Proxy's defineProperty trap against its target (`proxyDefineOk`, §10.5.6) -/

/-- Kind: a refusal (proxy invariant). Says: a trap may not report a new property defined on a
target that is not extensible. -/
theorem proxyDefineOk_nonextensible (d : Desc) : proxyDefineOk false d none = false := by
  simp [proxyDefineOk]

/-- Kind: a refusal. Says: a trap may not report a non-configurable property the target lacks. -/
theorem proxyDefineOk_new_unconfigurable (e : Bool) (d : Desc) (h : d.configurable = some false) :
    proxyDefineOk e d none = false := by
  simp [proxyDefineOk, h]

/-- Kind: a refusal. Says: a trap may not report a property non-configurable while the target's
is configurable. -/
theorem proxyDefineOk_configurable_target (e : Bool) (d : Desc) (p : PropV) (h : d.configurable = some false)
    (hp : p.configurable = true) : proxyDefineOk e d (some p) = false := by
  simp [proxyDefineOk, h, hp]

/-! ## A `switch` in the generator machine (`switchStmts`) -/

/-- Kind: a refusal. Says: a `switch` with an unlabelled `continue` for an enclosing loop is
not rewritten (the `do`-`while` would catch it); the generator machine reports it unsupported. -/
theorem switchStmts_cont (k : Nat) (l : List String) (d : Expr) (cs : List Case)
    (h : Case.anyContOut 100000 cs = true) : switchStmts k l d cs = none := by
  simp [switchStmts, h]

/-! ## Array iteration and holes (`arrayProbes`, §23.1.3) -/

/-- Kind: a specification. Says: forEach, map, filter, some and every skip absent indices; find
and findIndex read every index. -/
theorem arrayProbes_spec : arrayProbes .arrayForEach = true ∧ arrayProbes .arrayMap = true ∧
    arrayProbes .arrayFilter = true ∧ arrayProbes .arraySome = true ∧ arrayProbes .arrayEvery = true ∧
    arrayProbes .arrayFind = false ∧ arrayProbes .arrayFindIndex = false := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## RegExp.escape (`regexpEscapeStr`, §22.2.5.1) -/

/-- Kind: a specification. Says: a leading decimal digit is written as `\\xNN`, so the escaped
text cannot continue a back reference or an escape before it. -/
theorem regexpEscapeStr_digit (c : Char) (cs : List Char) (h : c.isDigit = true) :
    regexpEscapeStr (c :: cs) = "\\x" ++ hexLower c.toNat 2 ++ String.join (cs.map encodeForRegExpEscape) := by
  simp [regexpEscapeStr, h]

/-! ## The size of the heap (`HeapOf.full`, `maxObjs`)

The heap has no collector: an object, once made, stays. A page that makes objects for ever (a
timer that polls through promises, as WPT `fetch/metadata/generated/element-video-poster`
does) grew until the operating system ended the host's process (seven runner processes of the
full run of 19fb349c1 ended with SIGKILL). The engine now stops such a script itself. -/

/-- Kind: a refusal. Says: on a full heap, a step whose number is a multiple of 1024 halts the
run and changes nothing (the heap grows no further through that run).
Does not say: how many objects one step can make (a built-in can make many; those that loop
take their steps with `charge`, which looks at the heap every time), or how many bytes an
object holds (its properties and elements are not counted: see the design record). -/
theorem tick_full {H : Type} (h : HeapOf H) (h0 : h.steps ≠ 0) (hk : h.steps % 1024 = 0)
    (hf : h.full = true) :
    (tick : JSM H Unit).run h = .error (.halt heapFullMsg) h := by
  simp [tick, h0, hk, hf, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- Kind: a refusal. Says: on a full heap no function is entered: the step of a call halts
the run and changes nothing, whatever the step count. A run of a page starts with a call, so
a page whose heap is full runs no further handler or callback. -/
theorem tickCall_full {H : Type} (h : HeapOf H) (h0 : h.steps ≠ 0) (hf : h.full = true) :
    (tickCall : JSM H Unit).run h = .error (.halt heapFullMsg) h := by
  simp [tickCall, h0, hf, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- Kind: a cost. Says: within the heap's size a call's step is `tick`'s: one step. -/
theorem tickCall_step {H : Type} (h : HeapOf H) (h0 : h.steps ≠ 0) (hf : h.full = false) :
    (tickCall : JSM H Unit).run h = .ok () { h with steps := h.steps - 1 } := by
  simp [tickCall, h0, hf, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, set, MonadStateOf.set, EStateM.set]

/-- Kind: a refusal. Says: on a full heap a charge that the budget covers halts the run, with
the heap as it was: the work the charge stands for is not done. -/
theorem charge_full {H : Type} (h : HeapOf H) (k : Nat) (hk : k ≠ 0) (hge : ¬ h.steps < k.toUInt64)
    (hf : h.full = true) :
    (charge k : JSM H Unit).run h = .error (.halt heapFullMsg) h := by
  simp [charge, hk, hge, hf, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, throw, throwThe, MonadExceptOf.throw, EStateM.throw]

/-- Kind: a bound. Says: among any 1024 consecutive step counts one is a multiple of 1024:
counting down from `s`, the count `s - s % 1024` is reached within 1023 steps. With
`tick_full`: a loop on a full heap halts within 1024 of its steps.
Does not say: this for `UInt64` (the step count's type; the statement is about `Nat`). -/
theorem heap_check_within_1024 (s : Nat) : s % 1024 < 1024 ∧ (s - s % 1024) % 1024 = 0 := by
  omega

/-- Kind: a refusal. Says: a heap with more objects than `maxObjs` is full. -/
theorem full_of_objs {H : Type} (h : HeapOf H) (hgt : h.objs.size > h.maxObjs) : h.full = true := by
  simp [HeapOf.full, hgt]

/-- Kind: a refusal. Says: a heap with more environment records than `maxObjs` is full. -/
theorem full_of_envs {H : Type} (h : HeapOf H) (hgt : h.envs.size > h.maxObjs) : h.full = true := by
  simp [HeapOf.full, hgt]

/-- Kind: a refusal. Says: a charge of more steps than are left halts the run with the budget
at zero, so the work it stands for (growing an array, walking a string) is not done.
Does not say: that the charge is made before the work at every call (it is at the two places
that make dense arrays, `new Array(n)` and an assignment to `length`). -/
theorem charge_spent {H : Type} (h : HeapOf H) (k : Nat) (hk : k ≠ 0) (hlt : h.steps < k.toUInt64) :
    (charge k : JSM H Unit).run h = .error (.halt "step budget exhausted") { h with steps := 0 } := by
  simp [charge, hk, hlt, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, set, MonadStateOf.set, EStateM.set, throw, throwThe, MonadExceptOf.throw,
    EStateM.throw]

/-- Kind: a cost. Says: a charge within the budget takes exactly its steps. -/
theorem charge_step {H : Type} (h : HeapOf H) (k : Nat) (hk : k ≠ 0) (hge : ¬ h.steps < k.toUInt64)
    (hf : h.full = false) :
    (charge k : JSM H Unit).run h = .ok () { h with steps := h.steps - k.toUInt64 } := by
  simp [charge, hk, hge, hf, EStateM.run, bind, EStateM.bind, get, getThe, MonadStateOf.get,
    EStateM.get, set, MonadStateOf.set, EStateM.set]

/-- Kind: a bound. Says: the dense-array limit is below 2^31 (a scalar on 32-bit Wasm) and its
step charge, one step for 64 elements, is within one run's budget of a page (5,000,000 steps). -/
theorem maxDenseArray_bounds : maxDenseArray < 2 ^ 31 ∧ maxDenseArray / 64 < 5000000 := by decide

/-! ## The string size limit (`checkStrLen`) -/

/-- Kind: a refusal (a safety property of the host process).
Says: asking for a string of more than `maxStringBytes` bytes always ends in a thrown value
(the RangeError), never in the string: the continuation that would allocate it does not run.
Does not say: that every place that makes a string asks (`+`, `+=`, templates, `join`,
`concat`, `replace`, `repeat` and `padStart` do; that is read from the code and checked by
`#guard`s), or anything about arrays, whose growth is bounded by the step budget only. -/
theorem checkStrLen_refuses {H : Type} (h : HeapOf H) (bytes : Nat) (hb : bytes > maxStringBytes) :
    ∃ v h', (checkStrLen bytes : JSM H Unit).run h = .error (.throw v) h' := by
  unfold checkStrLen
  simp only [hb, ↓reduceIte]
  unfold throwErr
  simp only [bind, EStateM.bind, EStateM.run, throw, throwThe, MonadExceptOf.throw, EStateM.throw]
  cases hm : (mkError (H := H) ErrKind.range "Invalid string length") h with
  | ok v h' => exact ⟨v, h', by simp [hm]⟩
  | error e h' =>
    -- `mkError` allocates and sets a property: it does not fail
    simp [mkError, bind, EStateM.bind, realm, alloc, setHidden, defineOwn, modifyObj, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet, pure, EStateM.pure, get, getThe, MonadStateOf.get, EStateM.get, modify] at hm

/-- Kind: a pass. Says: within the limit, `checkStrLen` does nothing: the heap and the step
count are unchanged, so a script that makes no large string pays one comparison. -/
theorem checkStrLen_passes {H : Type} (h : HeapOf H) (bytes : Nat) (hb : bytes ≤ maxStringBytes) :
    (checkStrLen bytes : JSM H Unit).run h = .ok () h := by
  unfold checkStrLen
  have : ¬ bytes > maxStringBytes := Nat.not_lt.mpr hb
  simp [this, EStateM.run, pure, EStateM.pure]

/-- AdvanceStringIndex always moves forward, by one or two units: the global match, replace,
split and RegExp String Iterator loops that step past an empty match make progress. -/
theorem advanceIndex_gt (s : String) (i : Nat) (u : Bool) :
    i < advanceIndex s i u ∧ advanceIndex s i u ≤ i + 2 := by
  unfold advanceIndex
  split
  · omega
  · split
    · split <;> omega
    · omega

/-! ## Realms (`ColdHeap.realms`, `switchRealm`)

A host may make more realms in one heap (a test host's `$262.createRealm`); a call of a
function of another realm runs in that realm (`inRealm`). A heap with one realm, every page's,
must pay nothing for it. -/

/-- Kind: a cost. Says: with one realm (`realms` empty), changing the running realm changes
nothing at all: the heap comes back as it was.
Does not say: what a call costs with one realm (each call site tests `realms.isEmpty` once). -/
theorem switchRealm_one_realm {H : Type} (h : HeapOf H) (k : Nat) (hr : h.realms = #[]) :
    (switchRealm k : JSM H Unit).run h = .ok () h := by
  simp [switchRealm, hr, EStateM.run, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- Kind: a refusal. Says: a realm number that is not a realm of the heap is never made the
running realm: the heap comes back as it was. -/
theorem switchRealm_unknown {H : Type} (h : HeapOf H) (k : Nat) (hk : h.realms.size ≤ k) :
    (switchRealm k : JSM H Unit).run h = .ok () h := by
  simp [switchRealm, hk, EStateM.run, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-- Kind: a cost. Says: in realm 0 a new function object is not recorded anywhere (`tagFn` leaves
the heap as it was), so the map of function realms stays empty in a page. -/
theorem tagFn_realm0 {H : Type} (h : HeapOf H) (id : Nat) (h0 : h.curRealm = 0) :
    (tagFn id : JSM H Unit).run h = .ok () h := by
  simp [tagFn, h0, EStateM.run, modify, modifyGet, MonadStateOf.modifyGet, EStateM.modifyGet]

/-! ### Parser early errors -/

theorem mixesCoalesce_iff (l o : LogOp) :
    mixesCoalesce l (some o) = true ↔ ((l = .coalesce) ≠ (o = .coalesce)) := by
  cases l <;> cases o <;> decide

theorem mixesCoalesce_none (l : LogOp) : mixesCoalesce l none = false := rfl

theorem lexVarClash_iff (lex : List String) (vars : Array String) (before : Nat) :
    lexVarClash lex vars before = true ↔ ∃ x ∈ (vars.extract before vars.size).toList, x ∈ lex := by
  unfold lexVarClash
  constructor
  · intro h
    simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at h
    obtain ⟨_, h⟩ := h
    obtain ⟨x, hx, hc⟩ := Array.any_eq_true'.mp h
    exact ⟨x, Array.mem_toList_iff.mpr hx, by simpa using hc⟩
  · rintro ⟨x, hx, hl⟩
    have hne : lex.isEmpty = false := by
      cases lex with
      | nil => simp at hl
      | cons _ _ => rfl
    simp only [hne, Bool.not_false, Bool.true_and]
    exact Array.any_eq_true'.mpr ⟨x, Array.mem_toList_iff.mp hx, by simpa using hl⟩

/-- A string literal whose raw text has no backslash is never a legacy-escape literal. -/
theorem legacyEscapeIn_noBackslash (cs : Array Char) (j : Nat) :
    ∀ (fuel i : Nat), (∀ k, i ≤ k → k < j → cs[k]! ≠ '\\') → legacyEscapeIn cs j fuel i = false := by
  intro fuel
  induction fuel with
  | zero => intro i _; rfl
  | succ f ih =>
    intro i h
    unfold legacyEscapeIn
    by_cases hj : i + 1 ≥ j
    · simp [hj]
    · have hne : cs[i]! ≠ '\\' := h i (Nat.le_refl _) (by omega)
      simp only [hj, if_false, bne_iff_ne, ne_eq, hne, not_false_eq_true, if_true]
      exact ih (i + 1) (fun k hk hkj => h k (by omega) hkj)

/-! ### TypedArrayLength (§10.4.5.12) -/

/-- Every element below TypedArrayLength lies inside the buffer: a view in bounds never reads
past its bytes, a length-tracking one included. -/
theorem typedLenOf_fits (d : Bool) (off len elem size : Nat) :
    off + typedLenOf d off len elem size * elem ≤ size ∨ typedLenOf d off len elem size = 0 := by
  unfold typedLenOf typedOob
  by_cases hd : d = true
  · simp [hd]
  · by_cases ha : len = autoLen
    · by_cases ho : off > size
      · simp [hd, ha, ho]
      · left
        simp only [hd, ha, ho, Bool.false_or, beq_self_eq_true, if_true, decide_false, Bool.false_eq_true, if_false]
        have := Nat.div_mul_le_self (size - off) elem
        omega
    · by_cases ho : off + len * elem > size
      · simp [hd, ha, ho]
      · left
        have hb : (len == autoLen) = false := by simp [ha]
        simp only [hd, hb, ho, Bool.false_or, Bool.false_eq_true, if_false, decide_false]
        omega

theorem typedLenOf_fixed (off len elem size : Nat) (ha : len ≠ autoLen) (hin : off + len * elem ≤ size) :
    typedLenOf false off len elem size = len := by
  have hb : (len == autoLen) = false := by simp [ha]
  have ho : ¬ (off + len * elem > size) := by omega
  simp [typedLenOf, typedOob, hb, ho]

theorem typedLenOf_auto (off elem size : Nat) (hin : off ≤ size) :
    typedLenOf false off autoLen elem size = (size - off) / elem := by
  have ho : ¬ (off > size) := by omega
  simp [typedLenOf, typedOob, ho]

/-! ### CanBeHeldWeakly (§9.13) -/

section Weak
open Natives

theorem holdableIn_obj (reg : Option Obj) (i : Nat) : holdableIn reg (.obj i) = true := rfl

theorem holdableIn_registered (o : Obj) (sid : Nat) (h : symRegistered o sid = true) :
    holdableIn (some o) (.sym sid) = false := by
  simp [holdableIn, h]

theorem holdableIn_unregistered (reg : Option Obj) (sid : Nat)
    (h : ∀ o, reg = some o → symRegistered o sid = false) : holdableIn reg (.sym sid) = true := by
  cases reg with
  | none => rfl
  | some o => simp [holdableIn, h o rfl]

theorem holdableIn_prim (reg : Option Obj) (v : Value) (hv : ∀ i, v ≠ .obj i) (hs : ∀ s, v ≠ .sym s) :
    holdableIn reg v = false := by
  cases v with
  | obj i => exact absurd rfl (hv i)
  | sym s => exact absurd rfl (hs s)
  | _ => rfl

end Weak

/-! ## The register machine's global name cache -/

section GlobalCache
variable {H : Type}

theorem sameKeys_eq {a b : Array String} (h : sameKeys a b = true) : a = b := by
  unfold sameKeys at h
  rw [withPtrEq] at h
  exact beq_iff_eq.mp h

/-- An environment whose names and index pass the check of a hop gives the hop's `slotN`. -/
theorem Env.slotN_of_hop (env : Env) (p : GHop) (x : String) (hn : sameKeys env.names p.names = true)
    (hi : sameIdx env.index p.index = true) : env.slotN x = p.slotN x := by
  have hn' := sameKeys_eq hn
  unfold sameIdx at hi
  rw [withPtrEq] at hi
  unfold Env.slotN GHop.slotN
  rw [hn']
  have key : ∀ a b : Option (Std.HashMap String Nat), idxEq a b = true →
      (match a with | some m => (m.get? x).getD p.names.size | none => Env.scan p.names x 0) =
      (match b with | some m => (m.get? x).getD p.names.size | none => Env.scan p.names x 0) := by
    intro a b h
    match a, b, h with
    | none, none, _ => rfl
    | none, some _, h => simp [idxEq] at h
    | some _, none, h => simp [idxEq] at h
    | some m, some m', h =>
      simp only [idxEq] at h
      have hl : m.toList = m'.toList := beq_iff_eq.mp h
      have hg : m.get? x = m'.get? x := by
        apply Option.ext
        intro v
        rw [Std.HashMap.get?_eq_getElem?, Std.HashMap.get?_eq_getElem?,
          ← Std.HashMap.mem_toList_iff_getElem?_eq_some, ← Std.HashMap.mem_toList_iff_getElem?_eq_some, hl]
      simp only [hg]
  exact key _ _ hi

/-- **Kind: soundness of a cache guard.** When the scope chain of an entry passes `chainOk` from
`e`, no environment from `e` outward binds `x`: `findEnv` answers `none`, with any fuel of at
least the chain's length.

Does not say: that an entry is ever filled, or how often the check passes. -/
theorem chainOk_findEnv (h : HeapOf H) (x : String) :
    ∀ (hops : List (GHopOk x)) (e fuel : Nat), h.chainOk x hops e = true → hops.length ≤ fuel →
      h.findEnv x fuel e = none := by
  intro hops
  induction hops with
  | nil => intro e fuel hc; simp [HeapOf.chainOk] at hc
  | cons p ps ih =>
    intro e fuel hc hl
    obtain ⟨k, rfl⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by simp at hl; omega⟩
    unfold HeapOf.chainOk at hc
    simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hc
    obtain ⟨⟨⟨hw, hn⟩, hi⟩, hrest⟩ := hc
    have hs := Env.slotN_of_hop _ _ x hn hi
    have hn' := sameKeys_eq hn
    have hhas : (h.envs.getD e default).has x = false := by
      unfold Env.has; rw [hs, p.2, hn']; simp
    rw [HeapOf.findEnv]
    simp only [hhas, Bool.false_eq_true, ↓reduceIte]
    have hw' : (h.envs.getD e default).withObj = none := Option.isNone_iff_eq_none.mp hw
    rw [hw']
    rcases hrest with h0 | hr
    · simp [h0]
    · by_cases h0 : e = 0
      · simp [h0]
      · simp only [beq_iff_eq, h0, ↓reduceIte]
        exact ih _ k hr (by simp at hl; omega)

/-- A passing `chainHit` at a site: `findEnv` from `env` answers `none`. -/
theorem chainHit_findEnv (h : HeapOf H) (env : Nat) (x : String) (site : Nat)
    (hc : h.chainHit env x site = true) : h.findEnv x 100000 env = none := by
  unfold HeapOf.chainHit at hc
  split at hc
  · rename_i y hops _
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    obtain ⟨⟨hy, hlen⟩, hok⟩ := hc
    subst hy
    exact chainOk_findEnv h y hops env 100000 hok (by omega)
  · contradiction

/-- **Kind: soundness of a cache guard.**

Says: when `vmGlobalHit` answers a value (not `Value.hole`), no environment from `env` outward
binds `x`, and the global object's property map gives `x` a data property with that value.
Hypothesis `hsmall`: in a small map (no hash map), `x` is in at most one slot.

Does not say: that the machine's read of a global name equals the evaluator's `lookup` (that also
needs the `with` objects and the prototype chain, which this does not cover); anything about
`vmGlobalSet`. -/
theorem vmGlobalHit_sound (h : HeapOf H) (env : Nat) (x : String) (site : Nat) (v : Value)
    (hv : vmGlobalHit h env x site = v) (hh : v ≠ .hole)
    (hsmall : (h.obj h.realm.globalObj).props.big = none → ∀ (i j : Nat), j < i →
      (h.obj h.realm.globalObj).props.ks[j]? = some x → (h.obj h.realm.globalObj).props.ks[i]? ≠ some x) :
    h.findEnv x 100000 env = none ∧
      ∃ w e c, (h.obj h.realm.globalObj).props.get? x = some (.data v w e c) := by
  unfold vmGlobalHit at hv
  cases hch : h.chainHit env x site with
  | false =>
    rw [hch] at hv
    exact absurd hv.symm hh
  | true =>
    rw [hch] at hv
    refine ⟨chainHit_findEnv h env x site hch, ?_⟩
    simp only [Bool.not_true, Bool.false_eq_true, ↓reduceIte] at hv
    split at hv
    · rename_i k w0 w e c hks hvs
      split at hv
      · rename_i hc
        simp only [Bool.and_eq_true, beq_iff_eq] at hc
        obtain ⟨hkx, hl⟩ := hc
        subst hkx
        subst hv
        refine ⟨w, e, c, ?_⟩
        rw [PropMap.get?_of_slot _ _ _ hks hl (fun hb j hj hjk => hsmall hb _ j hj hjk hks), hvs]
      · exact absurd hv.symm hh
    · exact absurd hv.symm hh

#print axioms chainOk_findEnv
#print axioms vmGlobalHit_sound

end GlobalCache

end L4Factoidal.JS
