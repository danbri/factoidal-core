/-!
# L4Factoidal.JS.Str — JavaScript strings as UTF-16 code units (§6.1.4)

An ECMAScript String value is a sequence of 16-bit code units. BubblePopJS keeps a string
as a Lean `String` (UTF-8, so ASCII text takes one byte a unit, as V8's one-byte strings
do), read as code units by `units`:

- a character below U+10000 is one unit;
- a character from U+10000 is two units, a surrogate pair;
- a lone surrogate unit `u` (U+D800 to U+DFFF, which a Lean `Char` cannot be) is the
  character U+10F000 + (u − 0xD800), in the last private use plane (`loneChar`). The
  characters U+10F000 to U+10F7FF are kept for this, so a code point there, which as UTF-16
  is a pair of `\uDBFC`/`\uDBFD` and a low surrogate, is held as its two units, both
  lone characters (`decodeUnits`).

So every sequence of code units has exactly one form (`decodeUnits`, `units`; theorems
`units_decodeUnits` and `decodeUnits_units`), and equal JavaScript strings are equal Lean
strings. A string that the host gives (DOM text, a source file) is Unicode text: `ofHost`
turns the characters U+10F000 to U+10F7FF into their units, and `toHost` gives text back
with each lone surrogate as U+FFFD (WebIDL's USVString conversion, the policy at the DOM
boundary, whose arena holds Unicode scalar values).

The fast paths: an ASCII string (`isAscii`: as many bytes as characters, both counts kept
by the runtime) is indexed by byte, in constant time. Other strings are walked, as before.
-/

namespace L4Factoidal.JS.Str

/-! ## The representation -/

/-- The characters that hold lone surrogate units: U+10F000 to U+10F7FF. -/
def isLoneChar (c : Char) : Bool := 0x10F000 ≤ c.toNat && c.toNat < 0x10F800

def isHigh (u : Nat) : Bool := 0xD800 ≤ u && u < 0xDC00
def isLow (u : Nat) : Bool := 0xDC00 ≤ u && u < 0xE000
def isSurrogate (u : Nat) : Bool := 0xD800 ≤ u && u < 0xE000

/-- The character of a lone surrogate unit. -/
def loneChar (u : Nat) : Char := Char.ofNat (u - 0xD800 + 0x10F000)

/-- The character of a unit that is not part of a pair. -/
def unitChar (u : Nat) : Char := if isSurrogate u then loneChar u else Char.ofNat u

/-- The code units of one character of the representation. -/
def charUnits (c : Char) : List Nat :=
  if isLoneChar c then [c.toNat - 0x10F000 + 0xD800]
  else if c.toNat < 0x10000 then [c.toNat]
  else [0xD800 + (c.toNat - 0x10000) / 0x400, 0xDC00 + (c.toNat - 0x10000) % 0x400]

/-- How many units a character of the representation is. -/
def unitLen (c : Char) : Nat := if isLoneChar c || c.toNat < 0x10000 then 1 else 2

/-- The JavaScript string a Lean string holds: its code units. -/
def units (s : String) : List Nat := s.toList.flatMap charUnits

/-- Code units back to the representation: a surrogate pair is one character, unless its
code point is one that holds a lone unit (then the two lone characters); any other
surrogate is a lone character. -/
def decodeUnits : List Nat → List Char
  | [] => []
  | u :: rest =>
    match rest with
    | l :: rest' =>
      if isHigh u && isLow l then
        let cp := 0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00)
        if 0x10F000 ≤ cp && cp < 0x10F800 then loneChar u :: loneChar l :: decodeUnits rest'
        else Char.ofNat cp :: decodeUnits rest'
      else unitChar u :: decodeUnits (l :: rest')
    | [] => [unitChar u]

def ofUnits (us : List Nat) : String := String.ofList (decodeUnits us)

/-! ## Theorems: `length` counts code units, and the representation is a bijection -/

/-- `.length` of a JavaScript string, by the definition: the number of its code units. -/
def lengthSpec (s : String) : Nat := (s.toList.map unitLen).sum

theorem charUnits_length (c : Char) : (charUnits c).length = unitLen c := by
  unfold charUnits unitLen
  by_cases h : isLoneChar c <;> by_cases h' : c.toNat < 0x10000 <;> simp [h, h']

theorem units_length (s : String) : (units s).length = lengthSpec s := by
  unfold units lengthSpec
  induction s.toList with
  | nil => rfl
  | cons c cs ih => simp [List.flatMap_cons, charUnits_length, ih]

theorem toNat_ofNat_of_valid (n : Nat) (h : n < 0xD800 ∨ (0xDFFF < n ∧ n < 0x110000)) :
    (Char.ofNat n).toNat = n := by
  have hv : n.isValidChar := by unfold Nat.isValidChar; omega
  simp [Char.ofNat, hv, Char.ofNatAux, Char.toNat, UInt32.toNat_ofNatLT]

theorem loneChar_toNat (u : Nat) (h : isSurrogate u = true) :
    (loneChar u).toNat = u - 0xD800 + 0x10F000 := by
  unfold isSurrogate at h
  simp at h
  exact toNat_ofNat_of_valid _ (by omega)

theorem charRange (c : Char) : c.toNat < 0xD800 ∨ (0xDFFF < c.toNat ∧ c.toNat < 0x110000) := by
  have hv := c.valid
  unfold UInt32.isValidChar Nat.isValidChar at hv
  simp only [Char.toNat]
  omega

theorem unitChar_toNat (c : Char) (h : c.toNat < 0x10000) : unitChar c.toNat = c := by
  have hr := charRange c
  have : isSurrogate c.toNat = false := by unfold isSurrogate; simp; omega
  simp [unitChar, this]

set_option maxRecDepth 20000 in
/-- A character of a Unicode text that is not one of the kept characters is its UTF-16
encoding, and that encoding decodes to it. -/
theorem decodeUnits_charUnits (c : Char) (rest : List Nat) (hc : isLoneChar c = false) :
    decodeUnits (charUnits c ++ rest) = c :: decodeUnits rest := by
  have hr := charRange c
  unfold isLoneChar at hc
  simp at hc
  by_cases hb : c.toNat < 0x10000
  · have h1 : charUnits c = [c.toNat] := by
      simp [charUnits, isLoneChar, hb]; omega
    rw [h1]
    have hu := unitChar_toNat c hb
    cases rest with
    | nil => simp [decodeUnits, hu]
    | cons l rest' =>
      have : isHigh c.toNat = false := by unfold isHigh; simp; omega
      simp [decodeUnits, this, hu]
  · have h1 : charUnits c = [0xD800 + (c.toNat - 0x10000) / 0x400, 0xDC00 + (c.toNat - 0x10000) % 0x400] := by
      simp [charUnits, isLoneChar, hb]; omega
    rw [h1]
    have hh : isHigh (0xD800 + (c.toNat - 0x10000) / 0x400) = true := by unfold isHigh; simp; omega
    have hl : isLow (0xDC00 + (c.toNat - 0x10000) % 0x400) = true := by unfold isLow; simp; omega
    have hcp : 0x10000 + (0xD800 + (c.toNat - 0x10000) / 0x400 - 0xD800) * 0x400 +
        (0xDC00 + (c.toNat - 0x10000) % 0x400 - 0xDC00) = c.toNat := by omega
    simp only [List.cons_append, List.nil_append, decodeUnits, hh, hl, Bool.and_self, ite_true, hcp]
    have hn : ¬ ((decide (0x10F000 ≤ c.toNat) && decide (c.toNat < 0x10F800)) = true) := by
      simp; omega
    rw [if_neg hn, Char.ofNat_toNat]

/-- Round trip of well-formed text: a Lean string with none of the kept characters, written
as UTF-16 code units and read back, is the same string. -/
theorem decodeUnits_flatMap (cs : List Char) (h : ∀ c ∈ cs, isLoneChar c = false) :
    decodeUnits (cs.flatMap charUnits) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    rw [List.flatMap_cons, decodeUnits_charUnits c _ (h c (by simp)), ih (fun d hd => h d (by simp [hd]))]

theorem decodeUnits_units (s : String) (h : ∀ c ∈ s.toList, isLoneChar c = false) :
    ofUnits (units s) = s := by
  unfold ofUnits units
  rw [decodeUnits_flatMap _ h, String.ofList_toList]

theorem charUnits_loneChar (u : Nat) (h : isSurrogate u = true) : charUnits (loneChar u) = [u] := by
  have ht := loneChar_toNat u h
  unfold isSurrogate at h
  simp at h
  have hl : isLoneChar (loneChar u) = true := by unfold isLoneChar; simp; omega
  simp [charUnits, hl, ht]
  omega

theorem charUnits_unitChar (u : Nat) (hu : u < 0x10000) : charUnits (unitChar u) = [u] := by
  by_cases hs : isSurrogate u = true
  · simp [unitChar, hs, charUnits_loneChar u hs]
  · have hs' : isSurrogate u = false := by simpa using hs
    unfold isSurrogate at hs'
    simp at hs'
    have ht : (Char.ofNat u).toNat = u := toNat_ofNat_of_valid u (by omega)
    have hl : isLoneChar (Char.ofNat u) = false := by unfold isLoneChar; simp [ht]; omega
    have hs2 : isSurrogate u = false := by unfold isSurrogate; simp; omega
    simp [unitChar, hs2, charUnits, hl, ht, hu]

/-- Every sequence of code units has its form: read as units again, it is the same sequence. -/
theorem units_decodeUnits (us : List Nat) (h : ∀ u ∈ us, u < 0x10000) :
    (decodeUnits us).flatMap charUnits = us := by
  induction us using decodeUnits.induct with
  | case1 => rfl
  | case2 u l rest' hp cp hR ih =>
    have hR' : 0x10F000 ≤ 0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00) ∧
        0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00) < 0x10F800 := by
      simp only [cp] at hR; simpa using hR
    have hp' : isHigh u = true ∧ isLow l = true := by simpa using hp
    unfold isHigh isLow at hp'
    simp at hp'
    have hu : isSurrogate u = true := by unfold isSurrogate; simp; omega
    have hl : isSurrogate l = true := by unfold isSurrogate; simp; omega
    rw [decodeUnits]
    simp only [hp]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hR ⊢
    rw [if_pos hR']
    simp [List.flatMap_cons, charUnits_loneChar u hu, charUnits_loneChar l hl,
      ih (fun v hv => h v (by simp [hv]))]
  | case3 u l rest' hp cp hR ih =>
    have hR' : ¬ (0x10F000 ≤ 0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00) ∧
        0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00) < 0x10F800) := by
      simp only [cp] at hR; simpa using hR
    have hp' : isHigh u = true ∧ isLow l = true := by simpa using hp
    unfold isHigh isLow at hp'
    simp at hp'
    have hcpv := toNat_ofNat_of_valid (0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00)) (by omega)
    rw [decodeUnits]
    simp only [hp]
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hR ⊢
    rw [if_neg hR']
    have hnl : isLoneChar (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00))) = false := by
      unfold isLoneChar; rw [hcpv]; simp; omega
    have hc : charUnits (Char.ofNat (0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00))) = [u, l] := by
      simp only [charUnits, hnl, hcpv, Bool.false_eq_true, if_false]
      rw [if_neg (by omega)]
      simp only [List.cons.injEq, and_true]
      constructor <;> omega
    simp [List.flatMap_cons, hc, ih (fun v hv => h v (by simp [hv]))]
  | case4 u l rest' hp ih =>
    rw [decodeUnits]
    simp only [hp, Bool.false_eq_true, if_false]
    rw [List.flatMap_cons, charUnits_unitChar u (h u (by simp)),
      ih (fun v hv => h v (List.mem_cons_of_mem _ hv))]
    rfl
  | case5 u =>
    simp [decodeUnits, charUnits_unitChar u (h u (by simp))]

/-! ## The operations of the evaluator, with their fast paths -/

/-- `decodeUnits` as a loop (a tail call, so a long string does not grow the stack); the
characters are gathered in reverse. Checked against `decodeUnits` below. -/
def decodeGo : List Nat → List Char → List Char
  | [], acc => acc.reverse
  | [u], acc => (unitChar u :: acc).reverse
  | u :: l :: rest, acc =>
    if isHigh u && isLow l then
      let cp := 0x10000 + (u - 0xD800) * 0x400 + (l - 0xDC00)
      if 0x10F000 ≤ cp && cp < 0x10F800 then decodeGo rest (loneChar l :: loneChar u :: acc)
      else decodeGo rest (Char.ofNat cp :: acc)
    else decodeGo (l :: rest) (unitChar u :: acc)

/-- `ofUnits`, by the loop. -/
def ofUnitsFast (us : List Nat) : String := String.ofList (decodeGo us [])


/-- Every character is ASCII: as many bytes as characters (both counts kept by the
runtime, so this is constant time). -/
@[inline] def isAscii (s : String) : Bool := s.utf8ByteSize == s.length

/-- Every character is one unit (no supplementary character, no lone surrogate): then the
units are the characters, and character indices are unit indices. -/
def isBmp (s : String) : Bool := isAscii s || s.all (fun c : Char => decide (c.toNat < 0x10000))

/-- `.length` (§6.1.4): the number of code units, `lengthSpec` (checked below). -/
def jsLength (s : String) : Nat :=
  if isAscii s then s.length else s.foldl (fun n c => n + unitLen c) 0

/-- A unit as a character: itself below U+10000, else its lone character. -/
def unitAsChar (u : Nat) : Char := unitChar u

/-- The unit that a character of `unitChars` stands for. -/
def charUnit (c : Char) : Nat := if isLoneChar c then c.toNat - 0x10F000 + 0xD800 else c.toNat

/-- The code units of a string, one character each (`unitAsChar`): index `i` is unit `i`.
The evaluator's string methods index this array. -/
def unitChars (s : String) : Array Char :=
  if isBmp s then s.toList.toArray
  else ((units s).map unitAsChar).toArray

/-- The string of a run of `unitChars`: a high and a low surrogate next to each other are
one character again (`decodeUnits`). -/
def ofUnitChars (cs : Array Char) : String :=
  if cs.all (fun c : Char => !isLoneChar c) then String.ofList cs.toList
  else ofUnitsFast (cs.toList.map charUnit)

/-- The canonical form of a string whose lone characters may stand next to each other as
a pair (built by joining parts). -/
def canonical (s : String) : String :=
  if isAscii s || s.all (fun c : Char => !isLoneChar c) then s else ofUnitsFast (units s)

/-- Concatenation (§6.1.4.1 string-concatenation): a high surrogate at the end of `a` and a
low one at the start of `b` become one character. -/
def jsAppend (a b : String) : String :=
  if a.isEmpty || b.isEmpty then a ++ b else
  let x := a.back
  let y := b.front
  if isLoneChar x && isLoneChar y then
    let h := charUnit x
    let l := charUnit y
    let cp := 0x10000 + (h - 0xD800) * 0x400 + (l - 0xDC00)
    if isHigh h && isLow l && !(0x10F000 ≤ cp && cp < 0x10F800) then
      (a.dropEnd 1).toString ++ String.singleton (Char.ofNat cp) ++ (b.drop 1).toString
    else a ++ b
  else a ++ b

/-- The unit at index `i`. -/
def unitAt? (s : String) (i : Nat) : Option Nat :=
  if isAscii s then
    if h : (⟨i⟩ : String.Pos.Raw) < s.rawEndPos then some (s.getUTF8Byte ⟨i⟩ h).toNat else none
  else (unitChars s)[i]?.map charUnit

/-- The one-unit string at index `i` (`s[i]`, `charAt`). -/
def unitStrAt? (s : String) (i : Nat) : Option String :=
  (unitAt? s i).map fun u => String.singleton (unitChar u)

/-- Units `i` to `j` (exclusive). -/
def sliceUnits (s : String) (i j : Nat) : String :=
  if j ≤ i then ""
  else if isAscii s then String.Pos.Raw.extract s ⟨i⟩ ⟨j⟩
  else ofUnitChars ((unitChars s).extract i j)

/-- The string of code units (`String.fromCharCode`). -/
def ofCodeUnits (us : List Nat) : String := ofUnitsFast (us.map (· % 0x10000))

/-- The string of a code point (`String.fromCodePoint`, a `\u{...}` escape): a surrogate
code point is a lone unit. -/
def ofCodePoint (cp : Nat) : String :=
  if cp < 0x10000 then String.singleton (unitChar cp)
  else ofUnits [0xD800 + (cp - 0x10000) / 0x400, 0xDC00 + (cp - 0x10000) % 0x400]

/-- Host text (a scalar value string: DOM text, a source file, a host answer) as a
JavaScript string: the characters U+10F000 to U+10F7FF become their two units. -/
def ofHost (w : String) : String :=
  if isAscii w || w.all (fun c : Char => !isLoneChar c) then w
  else String.ofList (w.toList.flatMap fun c =>
    if isLoneChar c then [loneChar (0xD800 + (c.toNat - 0x10000) / 0x400), loneChar (0xDC00 + (c.toNat - 0x10000) % 0x400)]
    else [c])

/-- A JavaScript string as host text (WebIDL USVString): a lone surrogate is U+FFFD; a
pair held as two lone characters is its code point. -/
def toHost (s : String) : String :=
  if isAscii s || s.all (fun c : Char => !isLoneChar c) then s else String.ofList (go s.toList [])
where
  go : List Char → List Char → List Char
    | [], acc => acc.reverse
    | [c], acc => ((if isLoneChar c then '\uFFFD' else c) :: acc).reverse
    | c :: d :: rest, acc =>
      if isLoneChar c then
        let h := charUnit c
        let l := charUnit d
        if isLoneChar d && isHigh h && isLow l then
          go rest (Char.ofNat (0x10000 + (h - 0xD800) * 0x400 + (l - 0xDC00)) :: acc)
        else go (d :: rest) ('\uFFFD' :: acc)
      else go (d :: rest) (c :: acc)

/-- §22.1.3.32 toWellFormed: each lone surrogate replaced by U+FFFD. -/
def toWellFormed (s : String) : String := ofHost (toHost s)

/-- §22.1.3.10 isWellFormed: no lone surrogate. -/
def isWellFormed (s : String) : Bool := isAscii s || toWellFormed s == s

/-! Checks of the fast paths against the definitions. -/

def samples : List String :=
  ["", "abc", "é", "日本", "a😀b", "😀", ofUnits [0xD800], ofUnits [0xDC00, 0x61], ofUnits [0xDBFC, 0xDC00],
   ofUnits [0x61, 0xD83D], String.singleton (Char.ofNat 0x10FFFF) ++ "x"]

#guard samples.all fun s => jsLength s == lengthSpec s
#guard samples.all fun s => (unitChars s).toList.map charUnit == units s
#guard samples.all fun s => (List.range (jsLength s + 1)).all fun i => unitAt? s i == (units s)[i]?
#guard samples.all fun s => (List.range (jsLength s + 1)).all fun i => (List.range (jsLength s + 1)).all fun j =>
  units (sliceUnits s i j) == ((units s).drop i).take (j - i)
#guard samples.all fun a => samples.all fun b => jsAppend a b == ofUnits (units a ++ units b)
#guard samples.all fun s => canonical s == s
#guard ([[], [0x61], [0xD800], [0xDC00], [0xD83D, 0xDE00], [0xDBFC, 0xDC00], [0xD83D, 0x61, 0xDE00],
    [0xDE00, 0xD83D], [0xD83D, 0xD83D, 0xDE00], [0x61, 0xD800, 0xDC00, 0xDFFF]] : List (List Nat)).all fun us =>
  ofUnitsFast us == ofUnits us && decodeGo us [] == decodeUnits us
#guard jsLength "a😀b" == 4 && units (ofCodeUnits [0xD83D, 0xDE00]) == [0xD83D, 0xDE00] && ofCodeUnits [0xD83D, 0xDE00] == "😀"
#guard toHost (ofUnits [0x61, 0xD800, 0x62]) == "a\uFFFDb" && toHost (ofUnits [0xDBFC, 0xDC00]) == String.singleton (Char.ofNat 0x10F000)
#guard ofHost (String.singleton (Char.ofNat 0x10F000)) == ofUnits [0xDBFC, 0xDC00]
#guard isWellFormed "a😀" && !isWellFormed (ofUnits [0xD800]) && isWellFormed (ofUnits [0xDBFC, 0xDC00])
#guard ["abc", "日本", "a😀b", String.singleton (Char.ofNat 0x10F000) ++ "é"].all fun w => toHost (ofHost w) == w

end L4Factoidal.JS.Str
