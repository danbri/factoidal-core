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

theorem loopNext_break (ls : List String) : loopNext (H := Unit) ls (.brk none) = some .normal := rfl
theorem loopNext_continue (ls : List String) : loopNext (H := Unit) ls (.cont none) = none := rfl
theorem loopNext_normal (ls : List String) : loopNext (H := Unit) ls .normal = none := rfl
theorem loopNext_return (ls : List String) (v : Value) : loopNext (H := Unit) ls (.ret v) = some (.ret v) := rfl
theorem loopNext_label (l : String) (ls : List String) :
    loopNext (H := Unit) (l :: ls) (.brk (some l)) = some .normal := by simp [loopNext]

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

/-- Kind: a refusal. Says: a view that is in bounds is on a live buffer and its bytes fit in it. -/
theorem typedOob_false (d : Bool) (off len e size : Nat) (h : typedOob d off len e size = false) :
    d = false ∧ off + len * e ≤ size := by
  simp [typedOob] at h
  exact ⟨h.1, h.2⟩

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

end L4Factoidal.JS
