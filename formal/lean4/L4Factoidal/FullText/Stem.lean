/-
L4Factoidal.FullText.Stem — the stemming option of the full-text
implementation (XQuery and XPath Full Text 3.0 §3.4.4: the effect of
"stemming" is implementation-defined; it "is expected that this option
allows to match linguistic variants of the query tokens").

For English (the default language, and any language tag that starts with
`en`) the stemmer is the algorithm of M. F. Porter, "An algorithm for
suffix stripping", Program 14(3), 1980, pp. 130-137, steps 1a to 5b, on
lower-case words. Two tokens match under stemming when their stems are
equal. For another language there is no stemmer: the stem is the word.
-/
namespace L4Factoidal.FullText.Porter

/-- Porter's consonant: not a, e, i, o, u, and not a `y` after a consonant. -/
def isCons (w : Array Char) : Nat → Bool
  | 0 => match w.getD 0 ' ' with
    | 'a' | 'e' | 'i' | 'o' | 'u' => false
    | _ => true
  | i + 1 => match w.getD (i + 1) ' ' with
    | 'a' | 'e' | 'i' | 'o' | 'u' => false
    | 'y' => !isCons w i
    | _ => true

/-- The measure m of the first `len` letters: the number of VC sequences. -/
def measure (w : Array Char) (len : Nat) : Nat := Id.run do
  let mut m := 0
  let mut prevVowel := false
  for i in [0:len] do
    let c := isCons w i
    if c && prevVowel then m := m + 1
    prevVowel := !c
  return m

def hasVowel (w : Array Char) (len : Nat) : Bool :=
  (List.range len).any (fun i => !isCons w i)

def endsDouble (w : Array Char) (len : Nat) : Bool :=
  len ≥ 2 && w.getD (len - 1) ' ' == w.getD (len - 2) ' ' && isCons w (len - 1)

/-- `*o`: the stem ends cvc, and the second c is not w, x or y. -/
def cvc (w : Array Char) (len : Nat) : Bool :=
  len ≥ 3 && isCons w (len - 3) && !isCons w (len - 2) && isCons w (len - 1) &&
  !(w.getD (len - 1) ' ' == 'w' || w.getD (len - 1) ' ' == 'x' || w.getD (len - 1) ' ' == 'y')

def arr (s : String) : Array Char := s.toList.toArray

/-- The stem before the suffix `suf` (`s` ends with `suf`). -/
def before (s suf : String) : String := String.ofList (s.toList.take (s.length - suf.length))

/-- The measure of a string. -/
def m (s : String) : Nat := measure (arr s) s.length

def step1a (s : String) : String :=
  if s.endsWith "sses" then before s "es"
  else if s.endsWith "ies" then before s "es"
  else if s.endsWith "ss" then s
  else if s.endsWith "s" then before s "s"
  else s

def step1bFix (t : String) : String :=
  let a := arr t
  if t.endsWith "at" || t.endsWith "bl" || t.endsWith "iz" then t ++ "e"
  else if endsDouble a t.length && !(t.endsWith "l" || t.endsWith "s" || t.endsWith "z") then
    String.ofList (t.toList.take (t.length - 1))
  else if m t == 1 && cvc a t.length then t ++ "e"
  else t

def step1b (s : String) : String :=
  if s.endsWith "eed" then
    let t := before s "eed"
    if m t > 0 then before s "d" else s
  else if s.endsWith "ed" then
    let t := before s "ed"
    if hasVowel (arr t) t.length then step1bFix t else s
  else if s.endsWith "ing" then
    let t := before s "ing"
    if hasVowel (arr t) t.length then step1bFix t else s
  else s

def step1c (s : String) : String :=
  if s.endsWith "y" then
    let t := before s "y"
    if hasVowel (arr t) t.length then t ++ "i" else s
  else s

/-- Apply the rule of the longest suffix in `rules` that `s` ends with,
    when the measure of the stem is above `minM`. -/
def applyRules (rules : List (String × String)) (minM : Nat) (s : String) : String :=
  let sorted := rules.toArray.qsort (fun a b => a.1.length > b.1.length)
  match sorted.toList.find? (fun r => s.endsWith r.1) with
  | some (suf, rep) =>
    let t := before s suf
    if m t > minM then t ++ rep else s
  | none => s

def step2Rules : List (String × String) :=
  [("ational", "ate"), ("tional", "tion"), ("enci", "ence"), ("anci", "ance"), ("izer", "ize"),
   ("abli", "able"), ("alli", "al"), ("entli", "ent"), ("eli", "e"), ("ousli", "ous"),
   ("ization", "ize"), ("ation", "ate"), ("ator", "ate"), ("alism", "al"), ("iveness", "ive"),
   ("fulness", "ful"), ("ousness", "ous"), ("aliti", "al"), ("iviti", "ive"), ("biliti", "ble")]

def step3Rules : List (String × String) :=
  [("icate", "ic"), ("ative", ""), ("alize", "al"), ("iciti", "ic"), ("ical", "ic"),
   ("ful", ""), ("ness", "")]

def step4Suffixes : List String :=
  ["al", "ance", "ence", "er", "ic", "able", "ible", "ant", "ement", "ment", "ent", "ion",
   "ou", "ism", "ate", "iti", "ous", "ive", "ize"]

def step4 (s : String) : String :=
  let sorted := step4Suffixes.toArray.qsort (fun a b => a.length > b.length)
  match sorted.toList.find? (fun suf => s.endsWith suf) with
  | some suf =>
    let t := before s suf
    if m t > 1 then
      if suf == "ion" then (if t.endsWith "s" || t.endsWith "t" then t else s) else t
    else s
  | none => s

def step5a (s : String) : String :=
  if s.endsWith "e" then
    let t := before s "e"
    let mt := m t
    if mt > 1 || (mt == 1 && !cvc (arr t) t.length) then t else s
  else s

def step5b (s : String) : String :=
  if m s > 1 && endsDouble (arr s) s.length && s.endsWith "l" then
    String.ofList (s.toList.take (s.length - 1))
  else s

/-- The Porter stem of a lower-case word. Words of one or two letters are
    their own stem. -/
def stem (s : String) : String :=
  if s.length ≤ 2 then s
  else step5b (step5a (step4 (applyRules step3Rules 0 (applyRules step2Rules 0
    (step1c (step1b (step1a s)))))))

#guard stem "caresses" == "caress"
#guard stem "ponies" == "poni"
#guard stem "plastered" == "plaster"
#guard stem "motoring" == "motor"
#guard stem "hopping" == "hop"
#guard stem "filing" == "file"
#guard stem "relational" == "relat"
#guard stem "generalizations" == "gener"
#guard stem "improves" == stem "improving"
#guard stem "performed" == stem "performing"

end L4Factoidal.FullText.Porter
