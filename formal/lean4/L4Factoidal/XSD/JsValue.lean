/-
L4Factoidal.XSD.JsValue — the RDF literal of a JavaScript value, chosen by the
engine (https://github.com/danbri/factoidal/issues/894 item 3).

A SPARQL 1.1 §17.6 extension function registered from JavaScript answers a
JavaScript value. The host sends the value tagged with its JavaScript type
and nothing else (`{"js":"number","v":"1e+21"}`; for a number, `v` is the
ECMAScript `Number::toString` text, which is the shortest decimal that rounds
to the binary64 value). This module chooses the datatype and the lexical form:

  * `boolean`  -> `xsd:boolean`, `"true"` / `"false"`
  * `string`   -> `xsd:string`, the string
  * `bigint`   -> `xsd:integer`, the XSD 1.1 canonical integer form
  * `number`   -> `xsd:integer` when the text is an integer within
                  ±(2^53 − 1) (`Number.isSafeInteger`: the text is then the
                  exact value), else `xsd:double` in the XSD 1.1 canonical
                  form (§3.3.5.2: one non-zero digit before the point, at
                  least one after, `E`, the exponent): `1e+21` -> `"1.0E21"`,
                  `0.1` -> `"1.0E-1"`, `-0` -> `"-0.0E0"`, `NaN` -> `"NaN"`,
                  `Infinity` -> `"INF"`.

Theorems:
  * `doubleLexical_inLexicalSpace` : the `xsd:double` lexical form is in the
    lexical space (`parseLexical`, the front of `lexicalMap .double`) and
    denotes the same decimal number as the JavaScript text (`sameDecimal`);
    so the lexical mapping (`canonDouble`, the rounding of that decimal)
    gives the double the JavaScript text denotes.
  * `integerLexical_inLexicalSpace` : the `xsd:integer` lexical form is in the
    lexical space (`parseIntegerLex`) and maps to the integer of the text.
-/
import L4Factoidal.XSD.IEEE754
import L4Factoidal.XSD.Datatypes

namespace L4Factoidal.XSD.JsValue

open L4Factoidal.XSD

/-! ## Decimal digits -/

def digitCh : Nat → Char
  | 0 => '0' | 1 => '1' | 2 => '2' | 3 => '3' | 4 => '4'
  | 5 => '5' | 6 => '6' | 7 => '7' | 8 => '8' | _ => '9'

/-- The digit value `IEEE754.digitsToNat` reads from one character. -/
def ieeeDigit (c : Char) : Nat :=
  let raw := c.toNat
  if raw < 48 || raw > 57 then 0 else raw - 48

theorem ieeeDigit_digitCh {d : Nat} (h : d < 10) : ieeeDigit (digitCh d) = d := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => rfl
  | k + 10, h => omega

theorem natDigit_digitCh {d : Nat} (h : d < 10) : (digitCh d).toNat - 48 = d := by
  match d, h with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ | 7, _ | 8, _ | 9, _ => rfl
  | k + 10, h => omega

theorem isDigitChar_digitCh (d : Nat) : isDigitChar (digitCh d) = true := by
  unfold digitCh; split <;> decide

theorem isDigitC_digitCh (d : Nat) : isDigitC (digitCh d) = true := by
  unfold digitCh; split <;> decide

/-- Decimal digits of a natural number, most significant first. -/
def natLex (n : Nat) : List Char :=
  if n < 10 then [digitCh n] else natLex (n / 10) ++ [digitCh (n % 10)]
termination_by n
decreasing_by omega

theorem digitsToNat_append (acc : Nat) (xs ys : List Char) :
    digitsToNat acc (xs ++ ys) = digitsToNat (digitsToNat acc xs) ys := by
  induction xs generalizing acc with
  | nil => rfl
  | cons c r ih => simp only [List.cons_append, digitsToNat]; exact ih _

theorem digitsToNat_single (acc : Nat) (c : Char) :
    digitsToNat acc [c] = acc * 10 + ieeeDigit c := rfl

theorem digitsToNat_natLex (n : Nat) : digitsToNat 0 (natLex n) = n := by
  induction n using natLex.induct with
  | case1 n h =>
      rw [natLex, if_pos h, digitsToNat_single, ieeeDigit_digitCh h]; omega
  | case2 n h ih =>
      rw [natLex, if_neg h, digitsToNat_append, ih, digitsToNat_single,
        ieeeDigit_digitCh (Nat.mod_lt n (by omega))]
      omega

theorem natOfDigits_natLex (n : Nat) : natOfDigits (natLex n) = n := by
  induction n using natLex.induct with
  | case1 n h =>
      rw [natLex, if_pos h]; simp [natOfDigits, natDigit_digitCh h]
  | case2 n h ih =>
      rw [natLex, if_neg h]
      have hd := natDigit_digitCh (Nat.mod_lt n (show 10 > 0 by omega))
      simp only [natOfDigits, List.foldl_append, List.foldl_cons, List.foldl_nil] at ih ⊢
      rw [ih, hd]; omega

theorem natLex_ne_nil (n : Nat) : natLex n ≠ [] := by
  rw [natLex]; split <;> simp

theorem allDigits_natLex (n : Nat) : allDigits (natLex n) = true := by
  induction n using natLex.induct with
  | case1 n h => rw [natLex, if_pos h]; simp [allDigits, isDigitChar_digitCh]
  | case2 n h ih =>
      rw [natLex, if_neg h]; simp only [allDigits, List.all_append] at ih ⊢
      simp [ih, isDigitChar_digitCh]

theorem all_isDigitC_natLex (n : Nat) : (natLex n).all isDigitC = true := by
  induction n using natLex.induct with
  | case1 n h => rw [natLex, if_pos h]; simp [isDigitC_digitCh]
  | case2 n h ih =>
      rw [natLex, if_neg h]; simp only [List.all_append] at ih ⊢
      simp [ih, isDigitC_digitCh]

/-- The decimal digits of an integer, with `-` when it is negative. -/
def intLex (i : Int) : List Char :=
  if i < 0 then '-' :: natLex i.natAbs else natLex i.toNat

/-! ## Character facts the parsers need -/

theorem digit_ne_of_isDigitChar {c d : Char} (hc : isDigitChar c = true)
    (hd : isDigitChar d = false) : c ≠ d := by
  intro h; subst h; rw [hc] at hd; exact Bool.noConfusion hd

theorem splitAtChar_of_not_mem (ch : Char) (l : List Char) (h : ch ∉ l) :
    splitAtChar ch l = (l, none) := by
  induction l with
  | nil => rfl
  | cons c r ih =>
      have hc : c ≠ ch := fun e => h (e ▸ List.mem_cons_self)
      have hr : ch ∉ r := fun m => h (List.mem_cons_of_mem _ m)
      simp only [splitAtChar, beq_iff_eq, hc, if_false, ih hr]

theorem splitAtChar_append (ch : Char) (xs ys : List Char) (h : ch ∉ xs) :
    splitAtChar ch (xs ++ ch :: ys) = (xs, some ys) := by
  induction xs with
  | nil => simp [splitAtChar]
  | cons c r ih =>
      have hc : c ≠ ch := fun e => h (e ▸ List.mem_cons_self)
      have hr : ch ∉ r := fun m => h (List.mem_cons_of_mem _ m)
      simp only [List.cons_append, splitAtChar, beq_iff_eq, hc, if_false, ih hr]

theorem not_mem_of_all_digits {ch : Char} {l : List Char} (h : allDigits l = true)
    (hch : isDigitChar ch = false) : ch ∉ l := by
  intro m
  have := List.all_eq_true.mp h ch m
  rw [hch] at this; exact Bool.noConfusion this

theorem allDigits_cons (c : Char) (r : List Char) :
    allDigits (c :: r) = (isDigitChar c && allDigits r) := rfl

theorem parseSignedInt_natLex (n : Nat) : parseSignedInt (natLex n) = some (n : Int) := by
  have hne := natLex_ne_nil n
  have hall := allDigits_natLex n
  have hv := digitsToNat_natLex n
  match h : natLex n, hne, hall with
  | c :: cs, _, hall =>
    rw [h] at hv
    have hc : isDigitChar c = true := by
      rw [allDigits_cons, Bool.and_eq_true] at hall; exact hall.1
    have h1 : (c == '+') = false := beq_eq_false_iff_ne.mpr (digit_ne_of_isDigitChar hc (by decide))
    have h2 : (c == '-') = false := beq_eq_false_iff_ne.mpr (digit_ne_of_isDigitChar hc (by decide))
    unfold parseSignedInt
    simp only [h1, h2, Bool.false_eq_true, if_false, List.isEmpty_cons, Bool.not_false,
      Bool.true_and, hall, if_true, hv]

theorem parseSignedInt_negNatLex (n : Nat) :
    parseSignedInt ('-' :: natLex n) = some (-(n : Int)) := by
  have hne := natLex_ne_nil n
  have hall := allDigits_natLex n
  have hv := digitsToNat_natLex n
  unfold parseSignedInt
  have hd : (natLex n).isEmpty = false := by
    cases h : natLex n with
    | nil => exact absurd h hne
    | cons _ _ => rfl
  simp only [show ('-' == '+') = false from rfl, show ('-' == '-') = true from rfl,
    Bool.false_eq_true, if_false, if_true, hd, Bool.not_false, Bool.true_and, hall, hv]

theorem parseSignedInt_intLex (i : Int) : parseSignedInt (intLex i) = some i := by
  unfold intLex
  by_cases hi : i < 0
  · rw [if_pos hi, parseSignedInt_negNatLex]; congr 1; omega
  · rw [if_neg hi, parseSignedInt_natLex]; congr 1; omega

/-! ## The ECMAScript text of a finite number -/

/-- A finite decimal: sign, digits `ds` (all decimal digits), exponent `e`;
the value is `ds · 10^e`. -/
structure JsDec where
  neg : Bool
  ds : List Char
  e : Int

/-- The digits, fraction and exponent after the sign. -/
def readJsBody (neg : Bool) (body : List Char) : Option JsDec :=
  let (mant, ex) := splitAtChar 'e' body
  match (match ex with | none => some (0 : Int) | some ec => parseSignedInt ec) with
  | none => none
  | some e =>
    let (ip, fp) := splitAtChar '.' mant
    let fp := fp.getD []
    if allDigits ip && allDigits fp && !ip.isEmpty then
      some { neg, ds := ip ++ fp, e := e - (fp.length : Int) }
    else none

/-- Read the ECMAScript `Number::toString` form of a finite number:
`-`? digits (`.` digits)? (`e` (`+`|`-`) digits)?. -/
def readJsNumber (s : String) : Option JsDec :=
  match s.toList with
  | '-' :: r => readJsBody true r
  | r => readJsBody false r

/-- The value of a `JsDec`, as the double lexical parser represents values. -/
def JsDec.parsed (d : JsDec) : Parsed := .num d.neg (digitsToNat 0 d.ds) d.e

/-- Two parsed decimals denote the same number: the same sign and
`m1 · 10^e1 = m2 · 10^e2`, by cross multiplication. -/
def sameDecimal : Parsed → Parsed → Prop
  | .num n1 m1 e1, .num n2 m2 e2 =>
      n1 = n2 ∧ m1 * 10 ^ (e1 - min e1 e2).toNat = m2 * 10 ^ (e2 - min e1 e2).toNat
  | _, _ => False

/-! ## The XSD 1.1 canonical `xsd:double` form of a finite decimal -/

/-- Strip leading `0`s: the rest and how many were stripped. -/
def dropZerosN : List Char → List Char × Nat
  | [] => ([], 0)
  | c :: r => if c = '0' then ((dropZerosN r).1, (dropZerosN r).2 + 1) else (c :: r, 0)

theorem dropZerosN_spec (l : List Char) :
    l = List.replicate (dropZerosN l).2 '0' ++ (dropZerosN l).1 := by
  induction l with
  | nil => rfl
  | cons c r ih =>
      by_cases h : c = '0'
      · simp only [dropZerosN, if_pos h, List.replicate_succ, List.cons_append]
        rw [h]; exact congrArg _ ih
      · simp [dropZerosN, h]

theorem dropZerosN_head (l : List Char) :
    ∀ c r, (dropZerosN l).1 = c :: r → c ≠ '0' := by
  induction l with
  | nil => intro c r h; simp [dropZerosN] at h
  | cons x xs ih =>
      intro c r h
      by_cases hx : x = '0'
      · simp only [dropZerosN, if_pos hx] at h; exact ih c r h
      · simp only [dropZerosN, if_neg hx, List.cons.injEq] at h; rw [← h.1]; exact hx

theorem digitsToNat_replicate_zero (acc t : Nat) :
    digitsToNat acc (List.replicate t '0') = acc * 10 ^ t := by
  induction t generalizing acc with
  | zero => simp [digitsToNat]
  | succ t ih =>
      simp only [List.replicate_succ, digitsToNat]
      rw [ih, Nat.pow_succ]
      have h0 : (if '0'.toNat < 48 || '0'.toNat > 57 then 0 else '0'.toNat - 48) = 0 := by decide
      rw [h0, Nat.add_zero, Nat.mul_assoc, Nat.mul_comm 10 (10 ^ t)]

theorem digitsToNat_zeros_prefix (t : Nat) (l : List Char) :
    digitsToNat 0 (List.replicate t '0' ++ l) = digitsToNat 0 l := by
  rw [digitsToNat_append, digitsToNat_replicate_zero]; simp

/-- The mantissa of the canonical form and its exponent: the digits after
the leading digit, without trailing zeros (`["0"]` when none are left). -/
def fracOf (r : List Char) : List Char :=
  if (dropZerosN r.reverse).1.reverse.isEmpty then ['0'] else (dropZerosN r.reverse).1.reverse

/-- The canonical lexical form, as characters, of a decimal with digits `ds`
and exponent `e`, without the sign. -/
def doubleBody (ds : List Char) (e : Int) : List Char :=
  match (dropZerosN ds).1 with
  | [] => ['0', '.', '0', 'E', '0']
  | c :: r => c :: '.' :: (fracOf r ++ 'E' :: intLex (e + r.length))

def doubleChars (d : JsDec) : List Char :=
  if d.neg then '-' :: doubleBody d.ds d.e else doubleBody d.ds d.e

/-- The XSD 1.1 canonical `xsd:double` lexical form of a finite decimal. -/
def doubleLexical (d : JsDec) : String := String.ofList (doubleChars d)

theorem allDigits_append {xs ys : List Char} :
    allDigits (xs ++ ys) = (allDigits xs && allDigits ys) := by
  simp [allDigits, List.all_append]

theorem allDigits_fracOf {r : List Char} (h : allDigits r = true) : allDigits (fracOf r) = true := by
  unfold fracOf
  split
  · decide
  · have hs := dropZerosN_spec r.reverse
    have hr : allDigits r.reverse = true := by simpa [allDigits] using h
    rw [hs, allDigits_append] at hr
    simp only [Bool.and_eq_true] at hr
    simpa [allDigits] using hr.2

theorem fracOf_ne_nil (r : List Char) : fracOf r ≠ [] := by
  unfold fracOf; split
  · simp
  · rename_i h; simpa using h

/-- `parseDecimal` on the body: the canonical form reads back. -/
theorem parseDecimal_doubleBody (neg : Bool) (ds : List Char) (e : Int) (hd : allDigits ds = true) :
    parseDecimal neg (doubleBody ds e) =
      match (dropZerosN ds).1 with
      | [] => some (.num neg 0 (-1))
      | c :: r => some (.num neg (digitsToNat 0 (c :: fracOf r))
                          (e + r.length - (fracOf r).length)) := by
  unfold doubleBody
  split
  · cases neg <;> decide
  · rename_i c r hcr
    have hs := dropZerosN_spec ds
    rw [hcr] at hs
    have hall : allDigits (c :: r) = true := by
      rw [hs, allDigits_append] at hd; simp only [Bool.and_eq_true] at hd; exact hd.2
    rw [allDigits_cons, Bool.and_eq_true] at hall
    have hc : isDigitChar c = true := hall.1
    have hr : allDigits r = true := hall.2
    have hf := allDigits_fracOf hr
    have hfE : 'E' ∉ fracOf r := not_mem_of_all_digits hf (by decide)
    have hfe : 'e' ∉ fracOf r := not_mem_of_all_digits hf (by decide)
    have hfd : '.' ∉ fracOf r := not_mem_of_all_digits hf (by decide)
    have hcE : c ≠ 'E' := digit_ne_of_isDigitChar hc (by decide)
    have hce : c ≠ 'e' := digit_ne_of_isDigitChar hc (by decide)
    have hcd : c ≠ '.' := digit_ne_of_isDigitChar hc (by decide)
    have hexe : 'e' ∉ intLex (e + r.length) := by
      unfold intLex; split
      · intro m; simp only [List.mem_cons] at m
        rcases m with m | m
        · exact absurd m (by decide)
        · exact not_mem_of_all_digits (allDigits_natLex _) (by decide) m
      · exact not_mem_of_all_digits (allDigits_natLex _) (by decide)
    have hnoe : 'e' ∉ c :: '.' :: (fracOf r ++ 'E' :: intLex (e + r.length)) := by
      simp only [List.mem_cons, List.mem_append, not_or]
      exact ⟨fun h => hce h.symm, by decide, hfe, by decide, hexe⟩
    have hsplitE : splitAtChar 'E' (c :: '.' :: (fracOf r ++ 'E' :: intLex (e + r.length))) =
        (c :: '.' :: fracOf r, some (intLex (e + r.length))) := by
      have := splitAtChar_append 'E' (c :: '.' :: fracOf r) (intLex (e + r.length))
        (by simp only [List.mem_cons, not_or]; exact ⟨fun h => hcE h.symm, by decide, hfE⟩)
      simpa using this
    have hsplitD : splitAtChar '.' (c :: '.' :: fracOf r) = ([c], some (fracOf r)) := by
      simp [splitAtChar, hcd]
    simp only [parseDecimal, splitAtChar_of_not_mem 'e' _ hnoe, Option.isSome_none,
      Bool.false_eq_true, if_false, hsplitE, parseSignedInt_intLex, hsplitD, Option.getD_some]
    have hc1 : allDigits [c] = true := by simp [allDigits, hc]
    have hge : (decide ([c].length + (fracOf r).length ≥ 1)) = true := by
      simp
    simp only [hc1, hf, Bool.and_true, Bool.true_and, hge, if_true]
    rfl

/-- The canonical form denotes the same decimal number as the digits. -/
theorem sameDecimal_doubleBody (neg : Bool) (ds : List Char) (e : Int) (c : Char) (r : List Char)
    (hcr : (dropZerosN ds).1 = c :: r) :
    sameDecimal (.num neg (digitsToNat 0 (c :: fracOf r)) (e + r.length - (fracOf r).length))
      (.num neg (digitsToNat 0 ds) e) := by
  refine ⟨rfl, ?_⟩
  have hs := dropZerosN_spec ds
  rw [hcr] at hs
  have hds : digitsToNat 0 ds = digitsToNat 0 (c :: r) := by
    rw [hs, digitsToNat_zeros_prefix]
  -- the trailing zeros of r
  have ht := dropZerosN_spec r.reverse
  have hr : r = (dropZerosN r.reverse).1.reverse ++ List.replicate (dropZerosN r.reverse).2 '0' := by
    have := congrArg List.reverse ht
    simpa [List.reverse_append, List.reverse_replicate] using this
  have hfr : fracOf r = if (dropZerosN r.reverse).1.reverse.isEmpty then ['0']
      else (dropZerosN r.reverse).1.reverse := rfl
  generalize hf0 : (dropZerosN r.reverse).1.reverse = f0 at hr hfr
  generalize htn : (dropZerosN r.reverse).2 = t at hr
  have hlen : (r.length : Int) = f0.length + t := by
    rw [hr]; simp
  have hdr : digitsToNat 0 (c :: r) = digitsToNat 0 (c :: f0) * 10 ^ t := by
    rw [hr, ← List.cons_append, digitsToNat_append, digitsToNat_replicate_zero]
  rw [hds, hdr, hfr]
  by_cases hf : f0.isEmpty
  · have hf0n : f0 = [] := List.isEmpty_iff.mp hf
    subst hf0n
    simp only [List.isEmpty_nil, if_true, List.length_cons, List.length_nil] at hlen ⊢
    rw [show digitsToNat 0 [c, '0'] = digitsToNat 0 [c] * 10 by
      rw [show [c, '0'] = [c] ++ List.replicate 1 '0' from rfl, digitsToNat_append,
        digitsToNat_replicate_zero]; try simp]
    cases t with
    | zero =>
        have h1 : (e + (r.length : Int) - ((0 : Nat) + 1 : Nat) - min (e + r.length - ((0 : Nat) + 1 : Nat)) e).toNat = 0 := by omega
        have h2 : (e - min (e + r.length - ((0 : Nat) + 1 : Nat)) e).toNat = 1 := by omega
        simp only [Nat.zero_add] at h1 h2 ⊢
        rw [h1, h2]; simp
    | succ t =>
        have h1 : (e + (r.length : Int) - ((0 : Nat) + 1 : Nat) - min (e + r.length - ((0 : Nat) + 1 : Nat)) e).toNat = t := by omega
        have h2 : (e - min (e + r.length - ((0 : Nat) + 1 : Nat)) e).toNat = 0 := by omega
        simp only [Nat.zero_add] at h1 h2 ⊢
        rw [h1, h2, Nat.pow_succ]; simp only [Nat.pow_zero, Nat.mul_one]
        rw [Nat.mul_assoc, Nat.mul_comm 10 (10 ^ t)]
  · simp only [hf, if_false, Bool.false_eq_true]
    have h1 : (e + (r.length : Int) - f0.length - min (e + r.length - f0.length) e).toNat = t := by
      omega
    have h2 : (e - min (e + r.length - f0.length) e).toNat = 0 := by omega
    rw [h1, h2]; simp

/-- **The canonical `xsd:double` form is in the lexical space and denotes the
decimal of the JavaScript text.** `parseLexical` is the front of the XSD
lexical mapping (`lexicalMap .double s = (parseLexical s).map (.dbl ∘ canonDouble)`). -/
theorem doubleLexical_inLexicalSpace (d : JsDec) (hd : allDigits d.ds = true) :
    ∃ p, parseLexical (doubleLexical d) = some p ∧
      sameDecimal p d.parsed := by
  have hb := parseDecimal_doubleBody d.neg d.ds d.e hd
  -- the body starts with a digit
  have hhead : ∃ c rest, doubleBody d.ds d.e = c :: rest ∧ isDigitChar c = true := by
    unfold doubleBody; split
    · exact ⟨'0', _, rfl, by decide⟩
    · rename_i c r hcr
      have hs := dropZerosN_spec d.ds
      rw [hcr] at hs
      have hall : allDigits (c :: r) = true := by
        have := hd; rw [hs, allDigits_append] at this
        simp only [Bool.and_eq_true] at this; exact this.2
      rw [allDigits_cons, Bool.and_eq_true] at hall
      exact ⟨c, _, rfl, hall.1⟩
  obtain ⟨c0, rest, hbody, hc0⟩ := hhead
  have hne : ∀ s : String, s ∈ ["NaN", "INF", "+INF", "-INF"] →
      (String.ofList (doubleChars d) == s) = false := by
    intro s hs
    apply beq_eq_false_iff_ne.mpr
    intro he
    have h := congrArg String.toList he
    simp only [String.toList_ofList] at h
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs
    unfold doubleChars at h
    rw [hbody] at h
    have hN : isDigitChar 'N' = false := by decide
    have hI : isDigitChar 'I' = false := by decide
    have hP : isDigitChar '+' = false := by decide
    have hM : isDigitChar '-' = false := by decide
    rcases hs with rfl | rfl | rfl | rfl <;> cases hn : d.neg <;>
      simp only [hn, if_true, if_false, Bool.false_eq_true] at h <;>
      (first
        | (have := congrArg List.head? h; simp at this; subst this; simp_all)
        | (have := congrArg (fun l => l.tail.head?) h; simp at this; subst this; simp_all))
  have parse_eq : parseLexical (doubleLexical d) = parseDecimal d.neg (doubleBody d.ds d.e) := by
    unfold parseLexical doubleLexical
    rw [hne "NaN" (by simp), hne "INF" (by simp), hne "+INF" (by simp), hne "-INF" (by simp)]
    simp only [Bool.or_false, Bool.false_eq_true, if_false, String.toList_ofList]
    unfold doubleChars
    cases hn : d.neg
    · simp only [Bool.false_eq_true, if_false, hbody]
      have h1 : (c0 == '+') = false :=
        beq_eq_false_iff_ne.mpr (digit_ne_of_isDigitChar hc0 (by decide))
      have h2 : (c0 == '-') = false :=
        beq_eq_false_iff_ne.mpr (digit_ne_of_isDigitChar hc0 (by decide))
      simp only [h1, h2, Bool.false_eq_true, if_false]
    · simp only [if_true, show ('-' == '+') = false from rfl, show ('-' == '-') = true from rfl,
        Bool.false_eq_true, if_false]
  rw [parse_eq, hb]
  split
  · rename_i hz
    refine ⟨_, rfl, rfl, ?_⟩
    have hs := dropZerosN_spec d.ds
    rw [hz, List.append_nil] at hs
    have h0 : digitsToNat 0 d.ds = 0 := by rw [hs, digitsToNat_replicate_zero]; simp
    simp [JsDec.parsed, h0]
  · rename_i c r hcr
    exact ⟨_, rfl, sameDecimal_doubleBody d.neg d.ds d.e c r hcr⟩

/-! ## Integers -/

/-- The XSD 1.1 canonical `xsd:integer` form (§3.4.13.2): no sign for zero
and positive values, no leading zero. -/
def integerLexical (i : Int) : String := String.ofList (intLex i)

/-- **The canonical `xsd:integer` form is in the lexical space and maps to the
integer.** -/
theorem integerLexical_inLexicalSpace (i : Int) : parseIntegerLex (integerLexical i) = some i := by
  unfold integerLexical parseIntegerLex intLex
  by_cases hi : i < 0
  · rw [if_pos hi]
    simp only [String.toList_ofList]
    have ha : allDigitsL (natLex i.natAbs) = true := by
      simp [allDigitsL, natLex_ne_nil, all_isDigitC_natLex]
    simp only [ha, if_true, natOfDigits_natLex, if_true]
    congr 1; omega
  · rw [if_neg hi]
    simp only [String.toList_ofList]
    have hne := natLex_ne_nil i.toNat
    have hall := all_isDigitC_natLex i.toNat
    have hv := natOfDigits_natLex i.toNat
    match h : natLex i.toNat, hne, hall with
    | c :: cs, _, hall =>
      rw [h] at hv
      have hc : isDigitC c = true := by simp at hall; exact hall.1
      have ha : allDigitsL (c :: cs) = true := by simp [allDigitsL, hall]
      split
      · rename_i r heq
        simp only [List.cons.injEq] at heq
        rw [heq.1] at hc; exact absurd hc (by decide)
      · rename_i r heq
        simp only [List.cons.injEq] at heq
        rw [heq.1] at hc; exact absurd hc (by decide)
      · simp only [ha, if_true, hv, Bool.false_eq_true, if_false]
        congr 1; omega

/-! ## The literal of a tagged JavaScript value -/

/-- 2^53 − 1, `Number.MAX_SAFE_INTEGER`. -/
def maxSafeInteger : Nat := 9007199254740991

/-- The datatype local name (`boolean`, `string`, `integer`, `double`) and
the lexical form for a tagged JavaScript value; `none` when the tag or the
text is not one this mapping reads. -/
def jsLiteral (tag v : String) : Option (String × String) :=
  if tag == "boolean" then
    if v == "true" then some ("boolean", "true")
    else if v == "false" then some ("boolean", "false") else none
  else if tag == "string" then some ("string", v)
  else if tag == "bigint" then
    (parseIntegerLex v).bind fun i =>
      if allDigitsL (match v.toList with | '-' :: r => r | r => r) then
        some ("integer", integerLexical i) else none
  else if tag == "number" then
    if v == "NaN" then some ("double", "NaN")
    else if v == "Infinity" then some ("double", "INF")
    else if v == "-Infinity" then some ("double", "-INF")
    else
      match readJsNumber v with
      | none => none
      | some d =>
          -- An integer text within the safe range is the exact value;
          -- `-0` is a double (its sign has no xsd:integer form).
          let isIntText := !(v.toList.contains '.') && !(v.toList.contains 'e')
          let n := digitsToNat 0 d.ds
          if isIntText && n ≤ maxSafeInteger && !(d.neg && n == 0) then
            some ("integer", integerLexical (if d.neg then -(n : Int) else n))
          else some ("double", doubleLexical d)
  else none


/-! ## What `jsLiteral` answers for a JavaScript number -/

theorem readJsBody_allDigits {neg : Bool} {body : List Char} {d : JsDec}
    (h : readJsBody neg body = some d) : allDigits d.ds = true := by
  unfold readJsBody at h
  generalize splitAtChar 'e' body = me at h
  obtain ⟨mant, ex⟩ := me
  simp only at h
  split at h
  · simp at h
  · generalize splitAtChar '.' mant = sp at h
    obtain ⟨ip, fp⟩ := sp
    simp only at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hc
      rw [allDigits_append]; simp [hc.1.1, hc.1.2]
    · simp at h

theorem readJsNumber_allDigits {s : String} {d : JsDec} (h : readJsNumber s = some d) :
    allDigits d.ds = true := by
  unfold readJsNumber at h
  split at h <;> exact readJsBody_allDigits h

theorem readJsBody_int {neg : Bool} {body : List Char} {d : JsDec}
    (h : readJsBody neg body = some d) (hd : '.' ∉ body) (he : 'e' ∉ body) : d.e = 0 := by
  unfold readJsBody at h
  rw [splitAtChar_of_not_mem 'e' body he] at h
  simp only at h
  rw [splitAtChar_of_not_mem '.' body hd] at h
  simp only [Option.getD_none, List.length_nil] at h
  split at h
  · simp only [Option.some.injEq] at h; subst h; simp
  · simp at h

/-- An integer text (no `.`, no `e`) reads with exponent 0. -/
theorem readJsNumber_int {s : String} {d : JsDec} (h : readJsNumber s = some d)
    (hdot : s.toList.contains '.' = false) (he : s.toList.contains 'e' = false) : d.e = 0 := by
  have hnd : '.' ∉ s.toList := by simpa using hdot
  have hne : 'e' ∉ s.toList := by simpa using he
  unfold readJsNumber at h
  split at h
  · rename_i r hr
    rw [hr] at hnd hne
    exact readJsBody_int h (fun m => hnd (List.mem_cons_of_mem _ m))
      (fun m => hne (List.mem_cons_of_mem _ m))
  · exact readJsBody_int h hnd hne

/-- **A JavaScript number that `jsLiteral` writes as `xsd:double`** is `NaN`,
`INF` or `-INF` (the texts `NaN`, `Infinity`, `-Infinity`), or the canonical
form of the finite decimal of its text: in the lexical space, and the same
decimal number. -/
theorem jsLiteral_number_double (v lex : String) (h : jsLiteral "number" v = some ("double", lex)) :
    (v = "NaN" ∧ lex = "NaN") ∨ (v = "Infinity" ∧ lex = "INF") ∨ (v = "-Infinity" ∧ lex = "-INF") ∨
    ∃ d, readJsNumber v = some d ∧ lex = doubleLexical d ∧
      ∃ p, parseLexical lex = some p ∧ sameDecimal p d.parsed := by
  unfold jsLiteral at h
  simp only [show ("number" == "boolean") = false from by decide,
    show ("number" == "string") = false from by decide,
    show ("number" == "bigint") = false from by decide,
    show ("number" == "number") = true from by decide, if_true, if_false, Bool.false_eq_true] at h
  split at h
  · rename_i h1; simp only [Option.some.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨by simpa using h1, h.2.symm⟩
  · split at h
    · rename_i _ h2; simp only [Option.some.injEq, Prod.mk.injEq] at h
      exact Or.inr (Or.inl ⟨by simpa using h2, h.2.symm⟩)
    · split at h
      · rename_i _ _ h3; simp only [Option.some.injEq, Prod.mk.injEq] at h
        exact Or.inr (Or.inr (Or.inl ⟨by simpa using h3, h.2.symm⟩))
      · split at h
        · exact absurd h (by simp)
        · rename_i d hd
          split at h
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            exact absurd h.1 (by decide)
          · simp only [Option.some.injEq, Prod.mk.injEq] at h
            refine Or.inr (Or.inr (Or.inr ⟨d, hd, h.2.symm, ?_⟩))
            rw [← h.2]
            exact doubleLexical_inLexicalSpace d (readJsNumber_allDigits hd)

/-- **A JavaScript number that `jsLiteral` writes as `xsd:integer`** has an
integer text (exponent 0) within ±(2^53 − 1), and the lexical form is in the
`xsd:integer` lexical space and maps to the integer that text denotes. -/
theorem jsLiteral_number_integer (v lex : String) (h : jsLiteral "number" v = some ("integer", lex)) :
    ∃ d, readJsNumber v = some d ∧ d.e = 0 ∧ digitsToNat 0 d.ds ≤ maxSafeInteger ∧
      parseIntegerLex lex = some (if d.neg then -(digitsToNat 0 d.ds : Int) else digitsToNat 0 d.ds) := by
  unfold jsLiteral at h
  simp only [show ("number" == "boolean") = false from by decide,
    show ("number" == "string") = false from by decide,
    show ("number" == "bigint") = false from by decide,
    show ("number" == "number") = true from by decide, if_true, if_false, Bool.false_eq_true] at h
  split at h
  · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.1 (by decide)
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.1 (by decide)
    · split at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.1 (by decide)
      · split at h
        · exact absurd h (by simp)
        · rename_i d hd
          split at h
          · rename_i hc
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hc
            refine ⟨d, hd, readJsNumber_int hd hc.1.1.1 hc.1.1.2, hc.1.2, ?_⟩
            rw [← h.2]; exact integerLexical_inLexicalSpace _
          · simp only [Option.some.injEq, Prod.mk.injEq] at h; exact absurd h.1 (by decide)

/-! ## Build-time checks (positive and negative) -/

#guard jsLiteral "number" "1e+21" == some ("double", "1.0E21")
#guard jsLiteral "number" "0.1" == some ("double", "1.0E-1")
#guard jsLiteral "number" "123.456" == some ("double", "1.23456E2")
#guard jsLiteral "number" "1.5e-7" == some ("double", "1.5E-7")
#guard jsLiteral "number" "-0" == some ("double", "-0.0E0")
#guard jsLiteral "number" "0" == some ("integer", "0")
#guard jsLiteral "number" "42" == some ("integer", "42")
#guard jsLiteral "number" "-42" == some ("integer", "-42")
#guard jsLiteral "number" "9007199254740991" == some ("integer", "9007199254740991")
#guard jsLiteral "number" "9007199254740992" == some ("double", "9.007199254740992E15")
#guard jsLiteral "number" "1152921504606847000" == some ("double", "1.152921504606847E18")
#guard jsLiteral "number" "100" == some ("integer", "100")
#guard jsLiteral "number" "1e+300" == some ("double", "1.0E300")
#guard jsLiteral "number" "NaN" == some ("double", "NaN")
#guard jsLiteral "number" "-Infinity" == some ("double", "-INF")
#guard jsLiteral "number" "abc" == none
#guard jsLiteral "number" "1.2.3" == none
#guard jsLiteral "bigint" "123456789012345678901234567890" ==
  some ("integer", "123456789012345678901234567890")
#guard jsLiteral "bigint" "1.5" == none
#guard jsLiteral "boolean" "true" == some ("boolean", "true")
#guard jsLiteral "boolean" "yes" == none
#guard jsLiteral "string" "a\"b" == some ("string", "a\"b")
#guard jsLiteral "symbol" "x" == none
-- the double denotes the JavaScript value (XSD lexical mapping, binary64)
#guard doubleValueEq "1.0E21" "1e+21"
#guard doubleValueEq "1.0E-1" "0.1"
#guard doubleValueEq "9.007199254740992E15" "9007199254740992"
#guard (parseIntegerLex "1e+21").isNone

#print axioms doubleLexical_inLexicalSpace
#print axioms integerLexical_inLexicalSpace
#print axioms jsLiteral_number_double
#print axioms jsLiteral_number_integer

end L4Factoidal.XSD.JsValue
