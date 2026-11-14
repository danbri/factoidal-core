/-
L4Factoidal.ClientStorage.IdbKey — IndexedDB keys (Indexed Database API 3.0 §2.4 "Keys",
§2.5 "Key ranges"): the key type, the comparison of two keys, key ranges, and the form a
key has at the `web_api` boundary.

## Decisions

* A key is a number, a date, a string, binary data or an array of keys. An array is the
  spine `cons head tail` ended by `nil`, so `Key` is one plain inductive type and every
  proof is a plain induction (`Key.ofList`, `Key.items` give the list view).
* A number or date is held as the order image of its IEEE 754 double (`numImage`): the 63
  magnitude bits as an integer, negated when the sign bit is set. NaN is not a key (§2.4),
  -0 and +0 are one key, and for all other doubles the integer order is the numeric order
  (the usual property of sign-and-magnitude bit patterns; tested here, not proved against a
  model of doubles). No floating-point arithmetic is done on keys.
* A string is its UTF-16 code units, because §2.4 compares strings by code unit (so U+10000
  sorts before U+FFFF).
* An array key is read to a nesting of at most `Key.maxDepth` (64) arrays; a deeper one is
  not a key (`DataError`). This bounds the recursion of comparison.
* `Key.cmp` is "compare two keys" of §2.4. The theorems below say it is a total order and
  that the types sort Array > Binary > String > Date > Number.

Recursion is structural on the key or the list, or bounded by a fuel (the token count).
-/
import L4Factoidal.ClientStorage.Core

namespace L4Factoidal.ClientStorage.Idb

/-! ## Comparators on integers, naturals and lists -/

def cmpInt (a b : Int) : Ordering := if a < b then .lt else if a = b then .eq else .gt
def cmpNat (a b : Nat) : Ordering := if a < b then .lt else if a = b then .eq else .gt

theorem cmpInt_refl (a : Int) : cmpInt a a = .eq := by simp [cmpInt]
theorem cmpInt_eq {a b : Int} (h : cmpInt a b = .eq) : a = b := by
  unfold cmpInt at h
  by_cases h1 : a < b
  · simp [h1] at h
  · by_cases h2 : a = b
    · exact h2
    · simp [h1, h2] at h
theorem cmpInt_swap (a b : Int) : cmpInt b a = (cmpInt a b).swap := by
  unfold cmpInt
  by_cases h1 : a < b
  · have h2 : ¬ b < a := by omega
    have h3 : ¬ b = a := by omega
    simp [h1, h2, h3]
  · by_cases h2 : a = b
    · subst h2; simp
    · have h3 : b < a := by omega
      have h4 : ¬ b = a := fun e => h2 e.symm
      simp [h1, h2, h3]
theorem cmpInt_lt {a b : Int} : cmpInt a b = .lt ↔ a < b := by
  unfold cmpInt
  by_cases h1 : a < b
  · simp [h1]
  · by_cases h2 : a = b <;> simp [h1, h2]
theorem cmpInt_trans {a b c : Int} (h1 : cmpInt a b = .lt) (h2 : cmpInt b c = .lt) : cmpInt a c = .lt := by
  rw [cmpInt_lt] at *; omega

theorem cmpNat_refl (a : Nat) : cmpNat a a = .eq := by simp [cmpNat]
theorem cmpNat_eq {a b : Nat} (h : cmpNat a b = .eq) : a = b := by
  unfold cmpNat at h
  by_cases h1 : a < b
  · simp [h1] at h
  · by_cases h2 : a = b
    · exact h2
    · simp [h1, h2] at h
theorem cmpNat_swap (a b : Nat) : cmpNat b a = (cmpNat a b).swap := by
  unfold cmpNat
  by_cases h1 : a < b
  · have h2 : ¬ b < a := by omega
    have h3 : ¬ b = a := by omega
    simp [h1, h2, h3]
  · by_cases h2 : a = b
    · subst h2; simp
    · have h3 : b < a := by omega
      have h4 : ¬ b = a := fun e => h2 e.symm
      simp [h1, h2, h3]
theorem cmpNat_lt {a b : Nat} : cmpNat a b = .lt ↔ a < b := by
  unfold cmpNat
  by_cases h1 : a < b
  · simp [h1]
  · by_cases h2 : a = b <;> simp [h1, h2]
theorem cmpNat_trans {a b c : Nat} (h1 : cmpNat a b = .lt) (h2 : cmpNat b c = .lt) : cmpNat a c = .lt := by
  rw [cmpNat_lt] at *; omega

theorem then_eq {o p : Ordering} : o.then p = .eq ↔ o = .eq ∧ p = .eq := by
  cases o <;> cases p <;> simp [Ordering.then]
theorem then_lt {o p : Ordering} : o.then p = .lt ↔ o = .lt ∨ (o = .eq ∧ p = .lt) := by
  cases o <;> cases p <;> simp [Ordering.then]
theorem then_swap (o p : Ordering) : (o.then p).swap = o.swap.then p.swap := by
  cases o <;> cases p <;> rfl

/-- Lexicographic comparison of two lists of naturals (code units, or bytes); a proper
prefix is less (§2.4 steps for strings and binary keys). -/
def cmpNats : List Nat → List Nat → Ordering
  | [], [] => .eq
  | [], _ :: _ => .lt
  | _ :: _, [] => .gt
  | a :: as, b :: bs => match cmpNat a b with | .eq => cmpNats as bs | o => o

theorem cmpNats_cons (a b : Nat) (as bs : List Nat) :
    cmpNats (a :: as) (b :: bs) = (cmpNat a b).then (cmpNats as bs) := by
  cases h : cmpNat a b <;> simp [cmpNats, h, Ordering.then]

theorem cmpNats_refl (a : List Nat) : cmpNats a a = .eq := by
  induction a with
  | nil => rfl
  | cons x xs ih => rw [cmpNats_cons, cmpNat_refl, ih]; rfl

theorem cmpNats_eq : ∀ {a b : List Nat}, cmpNats a b = .eq → a = b := by
  intro a
  induction a with
  | nil => intro b h; cases b with | nil => rfl | cons y ys => simp [cmpNats] at h
  | cons x xs ih =>
    intro b h
    cases b with
    | nil => simp [cmpNats] at h
    | cons y ys =>
      rw [cmpNats_cons, then_eq] at h
      rw [cmpNat_eq h.1, ih h.2]

theorem cmpNats_swap : ∀ (a b : List Nat), cmpNats b a = (cmpNats a b).swap := by
  intro a
  induction a with
  | nil => intro b; cases b <;> rfl
  | cons x xs ih =>
    intro b
    cases b with
    | nil => rfl
    | cons y ys => rw [cmpNats_cons, cmpNats_cons, then_swap, ← cmpNat_swap, ← ih]

theorem cmpNats_trans : ∀ {a b c : List Nat}, cmpNats a b = .lt → cmpNats b c = .lt → cmpNats a c = .lt := by
  intro a
  induction a with
  | nil => intro b c h1 h2; cases b <;> cases c <;> simp_all [cmpNats]
  | cons x xs ih =>
    intro b c h1 h2
    cases b with
    | nil => simp [cmpNats] at h1
    | cons y ys =>
      cases c with
      | nil => simp [cmpNats] at h2
      | cons z zs =>
        rw [cmpNats_cons, then_lt] at h1 h2 ⊢
        rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
        · exact .inl (cmpNat_trans h1 h2)
        · rw [← cmpNat_eq e2]; exact .inl h1
        · rw [cmpNat_eq e1]; exact .inl h2
        · rw [cmpNat_eq e1, e2]; exact .inr ⟨rfl, ih h1 h2⟩

/-! ## Keys -/

/-- An IndexedDB key (§2.4). `number` and `date` hold the order image of the double
(`numImage`); `string` holds UTF-16 code units; `binary` holds bytes; an array is a spine
of `cons` ended by `nil`. -/
inductive Key where
  | number (v : Int)
  | date (v : Int)
  | string (units : List Nat)
  | binary (bytes : List Nat)
  | nil
  | cons (head : Key) (tail : Key)
  deriving DecidableEq, Repr, Inhabited

/-- The rank of a key's type in §2.4's order: Number < Date < String < Binary < Array. -/
def Key.rank : Key → Nat
  | .number _ => 0 | .date _ => 1 | .string _ => 2 | .binary _ => 3 | .nil => 4 | .cons _ _ => 4

/-- "Compare two keys" (§2.4): by type first, then by value; arrays item by item, a proper
prefix first. -/
def Key.cmp : Key → Key → Ordering
  | .number a, .number b => cmpInt a b
  | .date a, .date b => cmpInt a b
  | .string a, .string b => cmpNats a b
  | .binary a, .binary b => cmpNats a b
  | .nil, .nil => .eq
  | .nil, .cons _ _ => .lt
  | .cons _ _, .nil => .gt
  | .cons a as, .cons b bs => match Key.cmp a b with | .eq => Key.cmp as bs | o => o
  | a, b => cmpNat a.rank b.rank

theorem Key.cmp_cons (a as b bs : Key) :
    (Key.cons a as).cmp (.cons b bs) = (a.cmp b).then (as.cmp bs) := by
  cases h : a.cmp b <;> simp [Key.cmp, h, Ordering.then]

/-- The array key of a list of keys. -/
def Key.ofList (l : List Key) : Key := l.foldr (fun k acc => .cons k acc) .nil

def Key.itemsAux : Key → List Key → List Key
  | .cons h t, acc => Key.itemsAux t (h :: acc)
  | _, acc => acc.reverse

/-- The items of an array key (`[]` for a key that is not an array). -/
def Key.items (k : Key) : List Key := Key.itemsAux k []

/-- The number of items of an array key. -/
def Key.len : Key → Nat → Nat
  | .cons _ t, n => Key.len t (n + 1)
  | _, n => n

def Key.isArray : Key → Bool
  | .nil | .cons _ _ => true
  | _ => false

theorem Key.itemsAux_ofList (l : List Key) : ∀ acc, Key.itemsAux (Key.ofList l) acc = acc.reverse ++ l := by
  induction l with
  | nil => intro acc; simp [Key.ofList, Key.itemsAux]
  | cons k ks ih =>
    intro acc
    have h : Key.ofList (k :: ks) = .cons k (Key.ofList ks) := rfl
    rw [h, Key.itemsAux, ih]
    simp

theorem Key.items_ofList (l : List Key) : (Key.ofList l).items = l := by
  simp [Key.items, Key.itemsAux_ofList]

/-- Kind: order law (reflexivity). Says: a key compares equal to itself. -/
theorem Key.cmp_refl (a : Key) : a.cmp a = .eq := by
  induction a with
  | number v => simp [Key.cmp, cmpInt_refl]
  | date v => simp [Key.cmp, cmpInt_refl]
  | string u => simp [Key.cmp, cmpNats_refl]
  | binary u => simp [Key.cmp, cmpNats_refl]
  | nil => simp [Key.cmp]
  | cons h t ih1 ih2 => rw [Key.cmp_cons, ih1, ih2]; rfl

/-- Kind: order law (antisymmetry). Says: two keys that compare equal are the same key, so
a store never holds two records whose keys compare equal. Does not say: that two JavaScript
values with the same key are the same value (-0 and 0 are one key). -/
theorem Key.eq_of_cmp : ∀ (a b : Key), a.cmp b = .eq → a = b := by
  intro a
  induction a with
  | number v => intro b h; cases b with
    | number w => simp only [Key.cmp] at h; rw [cmpInt_eq h]
    | _ => simp [Key.cmp, Key.rank, cmpNat] at h
  | date v => intro b h; cases b with
    | date w => simp only [Key.cmp] at h; rw [cmpInt_eq h]
    | _ => simp [Key.cmp, Key.rank, cmpNat] at h
  | string u => intro b h; cases b with
    | string w => simp only [Key.cmp] at h; rw [cmpNats_eq h]
    | _ => simp [Key.cmp, Key.rank, cmpNat] at h
  | binary u => intro b h; cases b with
    | binary w => simp only [Key.cmp] at h; rw [cmpNats_eq h]
    | _ => simp [Key.cmp, Key.rank, cmpNat] at h
  | nil => intro b h; cases b with
    | nil => rfl
    | _ => simp [Key.cmp, Key.rank, cmpNat] at h
  | cons x xs ih1 ih2 => intro b h; cases b with
    | cons y ys => rw [Key.cmp_cons, then_eq] at h; rw [ih1 y h.1, ih2 ys h.2]
    | _ => simp [Key.cmp, Key.rank, cmpNat] at h

/-- Kind: order law (totality: the two directions agree). Says: comparing in the other
order gives the opposite answer, so of `a < b`, `a = b`, `a > b` exactly one holds. -/
theorem Key.cmp_swap : ∀ (a b : Key), b.cmp a = (a.cmp b).swap := by
  intro a
  induction a with
  | number v => intro b; cases b with
    | number w => simp only [Key.cmp]; exact cmpInt_swap v w
    | _ => simp [Key.cmp, Key.rank, cmpNat]
  | date v => intro b; cases b with
    | date w => simp only [Key.cmp]; exact cmpInt_swap v w
    | _ => simp [Key.cmp, Key.rank, cmpNat]
  | string u => intro b; cases b with
    | string w => simp only [Key.cmp]; exact cmpNats_swap u w
    | _ => simp [Key.cmp, Key.rank, cmpNat]
  | binary u => intro b; cases b with
    | binary w => simp only [Key.cmp]; exact cmpNats_swap u w
    | _ => simp [Key.cmp, Key.rank, cmpNat]
  | nil => intro b; cases b <;> simp [Key.cmp, Key.rank, cmpNat]
  | cons x xs ih1 ih2 => intro b; cases b with
    | cons y ys => rw [Key.cmp_cons, Key.cmp_cons, then_swap, ← ih1, ← ih2]
    | _ => simp [Key.cmp, Key.rank, cmpNat]

/-- Kind: order law (transitivity). Says: `a < b` and `b < c` give `a < c`. With
`cmp_refl`, `eq_of_cmp` and `cmp_swap`: `Key.cmp` is a strict total order on keys. -/
theorem Key.cmp_trans : ∀ (a b c : Key), a.cmp b = .lt → b.cmp c = .lt → a.cmp c = .lt := by
  intro a
  induction a with
  | number v => intro b c h1 h2; cases b <;> cases c <;> simp [Key.cmp, Key.rank, cmpNat] at h1 h2 ⊢
                exact cmpInt_trans h1 h2
  | date v => intro b c h1 h2; cases b <;> cases c <;> simp [Key.cmp, Key.rank, cmpNat] at h1 h2 ⊢
              exact cmpInt_trans h1 h2
  | string u => intro b c h1 h2; cases b <;> cases c <;> simp [Key.cmp, Key.rank, cmpNat] at h1 h2 ⊢
                exact cmpNats_trans h1 h2
  | binary u => intro b c h1 h2; cases b <;> cases c <;> simp [Key.cmp, Key.rank, cmpNat] at h1 h2 ⊢
                exact cmpNats_trans h1 h2
  | nil => intro b c h1 h2; cases b <;> cases c <;> simp [Key.cmp, Key.rank, cmpNat] at h1 h2 ⊢
  | cons x xs ih1 ih2 =>
    intro b c h1 h2
    cases b with
    | cons y ys =>
      cases c with
      | cons z zs =>
        rw [Key.cmp_cons, then_lt] at h1 h2 ⊢
        rcases h1 with h1 | ⟨e1, h1⟩ <;> rcases h2 with h2 | ⟨e2, h2⟩
        · exact .inl (ih1 y z h1 h2)
        · rw [← Key.eq_of_cmp y z e2]; exact .inl h1
        · rw [Key.eq_of_cmp x y e1]; exact .inl h2
        · rw [Key.eq_of_cmp x y e1, e2]; exact .inr ⟨rfl, ih2 ys zs h1 h2⟩
      | _ => simp [Key.cmp, Key.rank, cmpNat] at h2
    | _ => simp [Key.cmp, Key.rank, cmpNat] at h1

/-- Kind: conformance to the specification's type order (§2.4: "Array is greater than
Binary is greater than String is greater than Date is greater than Number"). Says: a key
of a lower-ranked type is less than every key of a higher-ranked type, whatever the values.
Does not say: anything about two keys of one type (the value rules of `Key.cmp`). -/
theorem Key.cmp_rank (a b : Key) (h : a.rank < b.rank) : a.cmp b = .lt := by
  cases a <;> cases b <;> simp [Key.rank] at h <;> simp [Key.cmp, Key.rank, cmpNat]

theorem Key.cmp_gt {a b : Key} : a.cmp b = .gt ↔ b.cmp a = .lt := by
  rw [Key.cmp_swap a b]; cases a.cmp b <;> simp

/-! ## Key ranges (§2.5) -/

/-- A key range: optional bounds, each open or closed. -/
structure Range where
  lower : Option Key := none
  upper : Option Key := none
  lowerOpen : Bool := false
  upperOpen : Bool := false
  deriving Repr, Inhabited

/-- "A key is in a key range" (§2.5). -/
def Range.includes (r : Range) (k : Key) : Bool :=
  (match r.lower with
   | none => true
   | some l => match l.cmp k with | .lt => true | .eq => !r.lowerOpen | .gt => false) &&
  (match r.upper with
   | none => true
   | some u => match k.cmp u with | .lt => true | .eq => !r.upperOpen | .gt => false)

/-- The range of one key (`IDBKeyRange.only`). -/
def Range.only (k : Key) : Range := { lower := some k, upper := some k }

/-- A range is valid when its lower bound is not above its upper bound, and they are not
equal with an open end (`IDBKeyRange.bound` throws `DataError` otherwise). -/
def Range.valid (r : Range) : Bool :=
  match r.lower, r.upper with
  | some l, some u => match l.cmp u with | .lt => true | .eq => !r.lowerOpen && !r.upperOpen | .gt => false
  | _, _ => true

/-- Kind: functional law. Says: the range of one key includes exactly that key. -/
theorem Range.only_includes (k x : Key) : (Range.only k).includes x = true ↔ x = k := by
  simp only [Range.only, Range.includes]
  constructor
  · intro h
    have hx : x.cmp k = (k.cmp x).swap := Key.cmp_swap k x
    cases hc : k.cmp x <;> simp [hc, hx] at h
    exact (Key.eq_of_cmp k x hc).symm
  · intro e; subst e; simp [Key.cmp_refl]

/-! ## Numbers at the boundary: the bits of a double -/

def hexVal (b : UInt8) : Option Nat :=
  let n := b.toNat
  if 48 ≤ n && n ≤ 57 then some (n - 48) else if 97 ≤ n && n ≤ 102 then some (n - 87)
  else if 65 ≤ n && n ≤ 70 then some (n - 55) else none

/-- The number written by `len` hex digits of `b` from `i`. -/
def hexAt (b : ByteArray) (i len : Nat) : Option Nat :=
  (List.range len).foldl (fun acc j => match acc, hexVal (b.get! (i + j)) with
    | some n, some d => if i + j < b.size then some (n * 16 + d) else none
    | _, _ => none) (some 0)

def hexDigit (n : Nat) : UInt8 := if n < 10 then (48 + n).toUInt8 else (87 + n).toUInt8

/-- `n` (below 2^32) as 8 hex digits. -/
def hex8 (n : Nat) : ByteArray :=
  (List.range 8).foldl (fun acc j => acc.push (hexDigit ((n >>> (4 * (7 - j))) % 16))) ByteArray.empty

/-- The order image of a double given by the two halves of its bits (`hi` the upper 32,
`lo` the lower 32): `none` for NaN; else the 63 magnitude bits, negated when the sign bit
is set. -0 and +0 both give 0. -/
def numImage (hi lo : Nat) : Option Int :=
  let sign := hi / 32768 / 65536
  let mhi := hi - sign * 32768 * 65536
  if mhi > 2146435072 || (mhi == 2146435072 && lo != 0) then none
  else
    let mag : Int := Int.ofNat (mhi * 65536 * 65536 + lo)
    some (if sign == 1 then -mag else mag)

/-- The bits (as 16 hex digits) of the double whose order image is `v`. -/
def numBits (v : Int) : ByteArray :=
  let mag := v.natAbs
  let mhi := mag / 65536 / 65536
  let lo := mag - mhi * 65536 * 65536
  hex8 (if v < 0 then mhi + 32768 * 65536 else mhi) ++ hex8 lo

/-! ## Strings at the boundary: UTF-16 code units

A JavaScript string crosses the boundary as UTF-8; a code unit that UTF-8 cannot carry (a
lone surrogate) or U+0001 itself crosses as U+0001 and four hex digits (prelude `stEnc`). -/

def hexOfChar (c : Char) : Nat := (hexVal c.toNat.toUInt8).getD 0

def unitsOf.go : List Char → List Nat → List Nat
  | [], acc => acc.reverse
  | c :: cs, acc =>
    if c.toNat == 1 then
      match cs with
      | a :: b :: x :: y :: rest => unitsOf.go rest ((((hexOfChar a * 16 + hexOfChar b) * 16 + hexOfChar x) * 16 + hexOfChar y) :: acc)
      | _ => acc.reverse
    else if c.toNat < 65536 then unitsOf.go cs (c.toNat :: acc)
    else unitsOf.go cs ((56320 + (c.toNat - 65536) % 1024) :: (55296 + (c.toNat - 65536) / 1024) :: acc)

/-- The UTF-16 code units of a boundary string. -/
def unitsOf (s : String) : List Nat := unitsOf.go s.toList []

def escUnit (u : Nat) : List Char :=
  Char.ofNat 1 :: [u / 4096 % 16, u / 256 % 16, u / 16 % 16, u % 16].map fun d => Char.ofNat (hexDigit d).toNat

/-- `pending`: a high surrogate that waits for its low surrogate. The characters are
collected in reverse. -/
def stringOf.go : Option Nat → List Nat → List Char → List Char
  | none, [], acc => acc.reverse
  | some h, [], acc => ((escUnit h).reverse ++ acc).reverse
  | none, u :: rest, acc =>
    if 55296 ≤ u && u < 56320 then go (some u) rest acc
    else if (56320 ≤ u && u < 57344) || u == 1 then go none rest ((escUnit u).reverse ++ acc)
    else go none rest (Char.ofNat u :: acc)
  | some h, u :: rest, acc =>
    if 56320 ≤ u && u < 57344 then go none rest (Char.ofNat (65536 + (h - 55296) * 1024 + (u - 56320)) :: acc)
    else if 55296 ≤ u && u < 56320 then go (some u) rest ((escUnit h).reverse ++ acc)
    else if u == 1 then go none rest ((escUnit u).reverse ++ (escUnit h).reverse ++ acc)
    else go none rest (Char.ofNat u :: (escUnit h).reverse ++ acc)

/-- The boundary string of UTF-16 code units (surrogate pairs joined; a lone surrogate or
U+0001 escaped). -/
def stringOf (us : List Nat) : String := String.ofList (stringOf.go none us [])

/-! ## Keys at the boundary: tokens

A key crosses as tokens, one byte string each, in pre-order: `n` + 16 hex digits (a
number's bits), `d` + 16 hex digits (a date's time value), `s` + a boundary string, `b` +
the bytes, `A` + a count followed by that many keys (a dense array), and `V` + kind,
byte offset, byte length followed by a `b` token (a view on a buffer, in a stored value;
the key is the bytes the view covers). The page side walks
the JavaScript value ("convert a value to a key", §7.4) and writes `x` for a value that is
not a key; whether a number is a key (NaN) is decided here. -/

abbrev Tok := ByteArray

def tagOf (t : Tok) : Char := if t.size == 0 then ' ' else Char.ofNat (t.get! 0).toNat
def bodyOf (t : Tok) : ByteArray := t.extract 1 t.size
def bodyStr (t : Tok) : String := (String.fromUTF8? (bodyOf t)).getD ""
def tok (tag : Char) (body : String) : Tok := (String.singleton tag ++ body).toUTF8

def numOfTok (t : Tok) : Option Int :=
  match hexAt t 1 8, hexAt t 9 8 with
  | some hi, some lo => if t.size == 17 then numImage hi lo else none
  | _, _ => none

/-- Read one key from `ts` at `i`: the key and the index after it; `none` when the tokens
there are not a key (§7.4 answers "invalid"). `fuel` bounds the depth. -/
def Key.read : Nat → Array Tok → Nat → Option (Key × Nat)
  | 0, _, _ => none
  | fuel + 1, ts, i =>
    match ts[i]? with
    | none => none
    | some t =>
      match tagOf t with
      | 'n' => (numOfTok t).map fun v => (.number v, i + 1)
      | 'd' => (numOfTok t).map fun v => (.date v, i + 1)
      | 's' => some (.string (unitsOf (bodyStr t)), i + 1)
      | 'b' => some (.binary ((bodyOf t).toList.map (·.toNat)), i + 1)
      | 'V' =>
        -- a view on a buffer (a stored value's typed array or DataView): its bytes
        match (bodyStr t).splitOn ",", ts[i + 1]? with
        | [_, off, len], some b =>
          match off.toNat?, len.toNat? with
          | some off, some len =>
            if tagOf b == 'b' && off + len + 1 ≤ b.size then
              some (.binary ((b.extract (1 + off) (1 + off + len)).toList.map (·.toNat)), i + 2)
            else none
          | _, _ => none
        | _, _ => none
      | 'A' =>
        match (bodyStr t).toNat? with
        | none => none
        | some n =>
          ((List.range n).foldl (fun acc _ =>
            match acc with
            | none => none
            | some (items, pos) =>
              match Key.read fuel ts pos with
              | some (k, pos') => some (k :: items, pos')
              | none => none) (some ([], i + 1))).map fun (items, pos) => (Key.ofList items.reverse, pos)
      | _ => none

/-- The deepest nesting of arrays in a key that is read: a key nested deeper is not a key
here (`DataError`). The recursion of `Key.read`, `Key.cmp` and `Key.write` is the nesting
of a key, so it is at most this. -/
def Key.maxDepth : Nat := 64

/-- The key that is the whole of `ts`. -/
def Key.ofToks (ts : Array Tok) : Option Key :=
  match Key.read Key.maxDepth ts 0 with
  | some (k, n) => if n == ts.size then some k else none
  | none => none

/-- The tokens of a key, appended to `acc`. `items`: write the items of an array spine
with no count token (the rest of an array whose count is already written). -/
def Key.write (items : Bool) : Key → Array Tok → Array Tok
  | .number v, acc => acc.push ("n".toUTF8 ++ numBits v)
  | .date v, acc => acc.push ("d".toUTF8 ++ numBits v)
  | .string u, acc => acc.push (tok 's' (stringOf u))
  | .binary b, acc => acc.push ("b".toUTF8 ++ ByteArray.mk (b.map (·.toUInt8)).toArray)
  | .nil, acc => if items then acc else acc.push (tok 'A' "0")
  | .cons h t, acc =>
    let acc := if items then acc else acc.push (tok 'A' (toString (Key.len t 1)))
    Key.write true t (Key.write false h acc)

def Key.toToks (k : Key) : Array Tok := Key.write false k #[]

/-! ## Checks (§2.4, and WPT IndexedDB/keyorder.any.js, idbfactory_cmp.any.js, key_valid.any.js) -/

private def num (hi lo : Nat) : Key := .number ((numImage hi lo).getD 0)
-- doubles: -Infinity fff00000:0, -1 bff00000:0, -0 80000000:0, 0, 5e-324 0:1, 1 3ff00000:0, Infinity 7ff00000:0, NaN 7ff80000:0
#guard numImage 0x7ff80000 0 == none
#guard numImage 0xfff80000 0 == none
#guard numImage 0x7ff00000 1 == none
#guard (numImage 0x7ff00000 0).isSome && (numImage 0xfff00000 0).isSome
#guard numImage 0x80000000 0 == some 0
#guard (num 0xfff00000 0).cmp (num 0xbff00000 0) == .lt
#guard (num 0xbff00000 0).cmp (num 0x80000000 0) == .lt
#guard (num 0x80000000 0).cmp (num 0 0) == .eq
#guard (num 0 0).cmp (num 0 1) == .lt
#guard (num 0 1).cmp (num 0x3ff00000 0) == .lt
#guard (num 0x3ff00000 0).cmp (num 0x7ff00000 0) == .lt
#guard numBits ((numImage 0xbff00000 0).getD 0) == "bff0000000000000".toUTF8
#guard numBits ((numImage 0x3ff00000 7).getD 0) == "3ff0000000000007".toUTF8
#guard numBits ((numImage 0xfff00000 0).getD 0) == "fff0000000000000".toUTF8
-- the type order
#guard (num 0x7ff00000 0).cmp (.date 0) == .lt
#guard (Key.date 5).cmp (.string []) == .lt
#guard (Key.string [65535]).cmp (.binary []) == .lt
#guard (Key.binary [255]).cmp .nil == .lt
#guard (Key.ofList [.number 1]).cmp (.binary [1]) == .gt
-- strings by code unit: U+10000 (d800 dc00) before U+FFFF; a prefix first
#guard (Key.string (unitsOf (String.singleton (Char.ofNat 65536)))).cmp (.string (unitsOf "\uFFFF")) == .lt
#guard unitsOf (String.singleton (Char.ofNat 65536)) == [55296, 56320]
#guard (Key.string (unitsOf "a")).cmp (.string (unitsOf "ab")) == .lt
#guard stringOf (unitsOf ("aé" ++ String.singleton (Char.ofNat 128512) ++ "z")) == "aé" ++ String.singleton (Char.ofNat 128512) ++ "z"
#guard unitsOf (stringOf [97, 55296, 98, 1, 56320]) == [97, 55296, 98, 1, 56320]
-- arrays: item by item, a prefix first, any array after any binary
#guard (Key.ofList []).cmp (Key.ofList [.number 0]) == .lt
#guard (Key.ofList [.number 1, .number 2]).cmp (Key.ofList [.number 1, .number 3]) == .lt
#guard (Key.ofList [.number 2]).cmp (Key.ofList [.number 1, .number 3]) == .gt
#guard (Key.ofList [Key.ofList []]).cmp (Key.ofList [.number 9]) == .gt
-- ranges
#guard ({ lower := some (.number 1), upper := some (.number 3), upperOpen := true } : Range).includes (.number 1)
#guard !({ lower := some (.number 1), upper := some (.number 3), upperOpen := true } : Range).includes (.number 3)
#guard !({ lower := some (.number 1), lowerOpen := true } : Range).includes (.number 1)
#guard ({} : Range).includes (.string [])
#guard !({ lower := some (.number 3), upper := some (.number 1) } : Range).valid
#guard !({ lower := some (.number 1), upper := some (.number 1), lowerOpen := true } : Range).valid
-- tokens
private def k1 : Key := Key.ofList [.number 5, .string (unitsOf "x"), Key.ofList [], .binary [0, 255], .date (-7)]
#guard Key.ofToks k1.toToks == some k1
#guard k1.toToks.size == 6
#guard Key.ofToks #["n7ff8000000000000".toUTF8] == none
#guard Key.ofToks #["x".toUTF8] == none
#guard Key.ofToks #["A2".toUTF8, "n0000000000000000".toUTF8] == none
#guard Key.ofToks #["n3ff0000000000000".toUTF8] == some (num 0x3ff00000 0)

end L4Factoidal.ClientStorage.Idb
