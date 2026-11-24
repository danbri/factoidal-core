import L4Factoidal.Rendering.CssValues.Token

/-! The `content` property of `::before` and `::after` (CSS 2.1 §12.2; CSS Content 3 §2):
which values make a box, and the text of that box.

A value is `none` or `normal` (no box), or a list of strings, `attr()` references, quote
keywords, images and counters, with an optional alternative text after `/`. This profile
gives the strings, the attribute values of the originating element and the quotation
marks; an image and a counter stand for nothing (the box is still made, so a sized or
cleared `::after` with an image lays out).

Bounds (both from the page: a sheet can repeat `attr()` of a long attribute): a value has
at most `maxPieces` parts (`read_parts_le`; one with more is not a value) and the text of a
box has at most `maxChars` characters (`chars_le`). -/
namespace L4Factoidal.Rendering.CSS.Content

/-- One part of a `content` value. -/
inductive Piece where
  | text (s : String)
  /-- `attr(name)`: the value of that attribute of the originating element. -/
  | attr (name : String)
  /-- An image that is not a `url()`, `no-open-quote`: nothing in this profile. -/
  | blank
  /-- `url(...)` (CSS Content 3 §2.1, CSS 2.1 §12.2): an image, drawn as an inline replaced
  box of its natural size. The URL is as the sheet gave it (the engine makes it absolute
  against the sheet's URL when it reads the sheet, CSS Values 4 §4.5). An image that cannot be
  displayed draws nothing. -/
  | image (url : String)
  /-- `counter(name, style)` (CSS 2.1 §12.4; CSS Lists 3 §4.3): the innermost counter of
  that name, in that style (`decimal` when none is given). -/
  | counter (name style : String)
  /-- `counters(name, separator, style)`: every counter of that name in scope, outermost
  first, joined with the separator. -/
  | counters (name sep style : String)
  deriving Repr, BEq, DecidableEq

/-- What a `content` value says. -/
inductive Value where
  /-- `none` or `normal`: the pseudo-element makes no box. -/
  | noBox
  | parts (ps : List Piece)
  deriving Repr, BEq, DecidableEq

/-- The most parts a value may have. -/
def maxPieces : Nat := 64

/-- The most characters the text of one pseudo-element has; the rest is cut. -/
def maxChars : Nat := 65536

/-- The functions that give an image (CSS Images 3 and 4). -/
def imageFunctions : List String :=
  ["url", "image", "image-set", "cross-fade", "element", "linear-gradient", "radial-gradient",
   "conic-gradient", "repeating-linear-gradient", "repeating-radial-gradient", "repeating-conic-gradient"]

private def isComma : CssValues.CV → Bool
  | .tok .comma => true
  | _ => false

/-- The arguments of a function split at its commas, white space left out. -/
def commaParts (args : List CssValues.CV) : List (List CssValues.CV) :=
  (args.foldr (fun a (acc : List (List CssValues.CV)) =>
    if isComma a then [] :: acc else match acc with
      | [] => [[a]]
      | c :: rest => (a :: c) :: rest) [[]]).map CssValues.stripWs

/-- The part for `url(u)`: an empty URL names no image (CSS Images 3 §4.1). -/
def imageOf (u : String) : Piece := if (u.trimAscii.toString).isEmpty then .blank else .image u.trimAscii.toString

/-- One component of the value as a part; `none` when it is not one. -/
def piece : CssValues.CV → Option Piece
  | .tok (.str s) => some (.text s)
  | .tok (.url u) => some (imageOf u)
  | .tok (.ident k) =>
    match CssValues.lower k with
    | "open-quote" => some (.text "\u201C")
    | "close-quote" => some (.text "\u201D")
    | "no-open-quote" | "no-close-quote" => some .blank
    | _ => none
  | .fn name args =>
    let name := CssValues.lower name
    if name == "url" then
      match CssValues.stripWs args with
      | [.tok (.str u)] => some (imageOf u)
      | _ => none
    else if name == "attr" then
      match CssValues.stripWs args with
      | .tok (.ident a) :: _ => some (.attr a)
      | _ => none
    else if name == "counter" then
      match commaParts args with
      | [[.tok (.ident n)]] => some (.counter n "decimal")
      | [[.tok (.ident n)], [.tok (.ident st)]] => some (.counter n (CssValues.lower st))
      | _ => none
    else if name == "counters" then
      match commaParts args with
      | [[.tok (.ident n)], [.tok (.str sep)]] => some (.counters n sep "decimal")
      | [[.tok (.ident n)], [.tok (.str sep)], [.tok (.ident st)]] => some (.counters n sep (CssValues.lower st))
      | _ => none
    else if imageFunctions.contains name then some .blank
    else none
  | _ => none

private def isSlash : CssValues.CV → Bool
  | .tok (.delim '/') => true
  | _ => false

/-- The value of a `content` declaration; `none` when the text is not one (the declaration
is then dropped, as CSS drops an invalid one). -/
def read (value : String) : Option Value :=
  let all := CssValues.stripWs (CssValues.CV.parse value)
  -- the alternative text after `/` is for speech
  let main := all.takeWhile (!isSlash ·)
  match main with
  | [] => none
  | [.tok (.ident k)] =>
    let k := CssValues.lower k
    if k == "none" || k == "normal" then some .noBox
    else (piece (.tok (.ident k))).map fun p => .parts [p]
  | _ =>
    if main.length > maxPieces then none else (main.mapM piece).map .parts

/-- The characters of the parts after `acc`, cut at `maxChars`. `attr` reads an attribute
of the originating element. -/
def chars (attr : String → String) : List Piece → List Char → List Char
  | [], acc => acc
  | p :: rest, acc =>
    if acc.length ≥ maxChars then acc else
    let more := match p with
      | .text s => s.toList
      | .attr name => (attr name).toList
      | .blank | .image _ | .counter .. | .counters .. => []
    chars attr rest ((acc ++ more).take maxChars)

/-- The text of a box with these parts. -/
def text (attr : String → String) (ps : List Piece) : String := String.ofList (chars attr ps [])

/-- **The text of a pseudo-element is bounded**, whatever the attributes hold. -/
theorem chars_le (attr : String → String) (ps : List Piece) (acc : List Char) (h : acc.length ≤ maxChars) :
    (chars attr ps acc).length ≤ maxChars := by
  induction ps generalizing acc with
  | nil => simpa [chars] using h
  | cons p rest ih =>
    unfold chars
    split
    · exact h
    · exact ih _ (by simp [List.length_take]; omega)

/-- What is already there stays: the parts only add characters after it. -/
theorem chars_prefix (attr : String → String) (ps : List Piece) (acc : List Char) (h : acc.length ≤ maxChars) :
    acc <+: chars attr ps acc := by
  induction ps generalizing acc with
  | nil => simp [chars]
  | cons p rest ih =>
    unfold chars
    split
    · exact List.prefix_refl _
    · rename_i short
      have keep : acc <+: (acc ++ (match p with
          | .text s => s.toList
          | .attr name => (attr name).toList
          | .blank | .image _ | .counter .. | .counters .. => [])).take maxChars := by
        rw [List.prefix_take_iff]
        exact ⟨List.prefix_append _ _, h⟩
      exact List.IsPrefix.trans keep (ih _ (by simp [List.length_take]; omega))

/-- No parts, no text. -/
theorem chars_nil (attr : String → String) (acc : List Char) : chars attr [] acc = acc := rfl

private theorem mapM_length {α β : Type} (f : α → Option β) :
    ∀ (l : List α) (r : List β), l.mapM f = some r → r.length = l.length
  | [], r, h => by
    simp at h
    subst h
    rfl
  | a :: l, r, h => by
    rw [List.mapM_cons] at h
    cases fa : f a with
    | none => simp [fa] at h
    | some b =>
      cases fl : l.mapM f with
      | none => simp [fa, fl] at h
      | some bs =>
        simp [fa, fl] at h
        subst h
        simp [mapM_length f l bs fl]

/-- **A value has at most `maxPieces` parts.** -/
theorem read_parts_le (value : String) (ps : List Piece) (h : read value = some (.parts ps)) :
    ps.length ≤ maxPieces := by
  unfold read at h
  simp only [] at h
  split at h
  · cases h
  · split at h
    · cases h
    · cases hp : piece (.tok (.ident (CssValues.lower ‹String›))) with
      | none => simp [hp] at h
      | some p =>
        simp only [hp, Option.map_some, Option.some.injEq, Value.parts.injEq] at h
        subst h
        simp [maxPieces]
  · split at h
    · cases h
    · rename_i fits
      cases hm : List.mapM piece (List.takeWhile (fun x => !isSlash x) (CssValues.stripWs (CssValues.CV.parse value))) with
      | none => simp [hm] at h
      | some qs =>
        simp only [hm, Option.map_some, Option.some.injEq, Value.parts.injEq] at h
        subst h
        have same := mapM_length piece _ _ hm
        omega

#guard read "none" == some .noBox
#guard read "NORMAL" == some .noBox
#guard read "\"\"" == some (.parts [.text ""])
#guard read "''" == some (.parts [.text ""])
#guard read "\"a\" 'b'" == some (.parts [.text "a", .text "b"])
#guard read "\"\\201C\"" == some (.parts [.text "\u201C"])
#guard read "\"\\f101\"" == some (.parts [.text (String.singleton (Char.ofNat 0xf101))])
#guard read "attr(title)" == some (.parts [.attr "title"])
#guard read "\"(\" attr(href) \")\"" == some (.parts [.text "(", .attr "href", .text ")"])
#guard read "open-quote" == some (.parts [.text "\u201C"])
#guard read "counter(item) \". \"" == some (.parts [.counter "item" "decimal", .text ". "])
#guard read "counter(item, upper-roman)" == some (.parts [.counter "item" "upper-roman"])
#guard read "counters(item, \".\")" == some (.parts [.counters "item" "." "decimal"])
#guard read "counters(item, \".\", lower-alpha)" == some (.parts [.counters "item" "." "lower-alpha"])
#guard read "counter(1)" == none
#guard read "url(a.png)" == some (.parts [.image "a.png"])
#guard read "url(a.png) / \"alt\"" == some (.parts [.image "a.png"])
#guard read "url(\"a b.png\")" == some (.parts [.image "a b.png"])
#guard read "url('s.svg')" == some (.parts [.image "s.svg"])
#guard read "URL( \"s.svg\" )" == some (.parts [.image "s.svg"])
#guard read "\"a\" url(i.png) \"b\"" == some (.parts [.text "a", .image "i.png", .text "b"])
#guard read "url(\"\")" == some (.parts [.blank])
#guard read "url(a.png b.png)" == none
#guard read "linear-gradient(red, blue)" == some (.parts [.blank])
#guard read "\"x\" / \"alt\"" == some (.parts [.text "x"])
#guard read "" == none
#guard read "12px" == none
#guard read "\"a\" bogus" == none
#guard read "inherit" == none
#guard text (fun _ => "v") [.text "a", .attr "x", .blank, .text "b"] == "avb"
#guard text (fun _ => "v") [.text "a", .image "i.png", .text "b"] == "ab"
#guard text (fun _ => "") [] == ""
#guard (text (fun _ => String.ofList (List.replicate 70000 'x')) [.attr "a", .attr "a"]).length == maxChars

/-! ### Counters (CSS 2.1 §12.4, CSS Lists 3 §4)

`counter-reset`, `counter-increment` and `counter-set` name counters with an optional integer;
`counter()` and `counters()` show their values in a counter style. -/

/-- The names and integers of a `counter-reset`, `counter-increment` or `counter-set` value;
`dflt` for a name with no integer. `none` gives no pair; `none` as the answer: not a value. -/
def counterPairs (dflt : Int) : List CssValues.CV → Option (List (String × Int))
  | [] => some []
  | .tok (.ident n) :: .tok (.num v true) :: rest =>
    if bad n then none else (counterPairs dflt rest).map ((n, v.num) :: ·)
  | .tok (.ident n) :: rest => if bad n then none else (counterPairs dflt rest).map ((n, dflt) :: ·)
  | _ => none
where bad (n : String) : Bool :=
  ["none", "initial", "inherit", "unset", "default", "revert", "revert-layer"].contains (CssValues.lower n)

private def counterPairsGo (dflt : Int) : List CssValues.CV → List (String × Int) → Option (List (String × Int))
  | [], acc => some acc.reverse
  | .tok (.ident n) :: .tok (.num v true) :: rest, acc =>
    if counterPairs.bad n then none else counterPairsGo dflt rest ((n, v.num) :: acc)
  | .tok (.ident n) :: rest, acc =>
    if counterPairs.bad n then none else counterPairsGo dflt rest ((n, dflt) :: acc)
  | _, _ => none

private theorem counterPairsGo_eq (dflt : Int) (xs : List CssValues.CV) (acc : List (String × Int)) :
    counterPairsGo dflt xs acc = (counterPairs dflt xs).map (acc.reverse ++ ·) := by
  fun_induction counterPairs dflt xs generalizing acc <;>
    simp_all [counterPairsGo, counterPairs, Option.map_map, Function.comp_def, List.reverse_cons, List.append_assoc]

def counterPairsLoop (dflt : Int) (xs : List CssValues.CV) : Option (List (String × Int)) :=
  counterPairsGo dflt xs []

@[csimp] theorem counterPairs_eq_loop : @counterPairs = @counterPairsLoop := by
  funext dflt xs
  simp [counterPairsLoop, counterPairsGo_eq]

#print axioms counterPairs_eq_loop

/-- The names of `reversed(name)` with no integer in a `counter-reset` value (CSS Lists 3
§4.4): such a counter starts at the number its increments count down from (`Generated`). -/
def reversedNames (value : String) : List String :=
  let cvs := CssValues.stripWs (CssValues.CV.parse value)
  (List.range cvs.length).filterMap fun i => match (cvs[i]? : Option CssValues.CV), (cvs[i+1]? : Option CssValues.CV) with
    | some (.fn f args), next =>
      if CssValues.lower f != "reversed" then none else
      match CssValues.stripWs args, next with
      | [.tok (.ident n)], some (.tok (.num _ true)) => none
      | [.tok (.ident n)], _ => some n
      | _, _ => none
    | _, _ => none

/-- `reversed(name)` read as the name (its start is worked out later). -/
def unreverse : List CssValues.CV → List CssValues.CV
  | [] => []
  | .fn f args :: rest =>
    if CssValues.lower f == "reversed" then
      match CssValues.stripWs args with
      | [one] => one :: unreverse rest
      | _ => .fn f args :: unreverse rest
    else .fn f args :: unreverse rest
  | c :: rest => c :: unreverse rest

def unreverseLoop (xs : List CssValues.CV) : List CssValues.CV :=
  xs.map fun c => match c with
    | .fn f args =>
      if CssValues.lower f == "reversed" then
        match CssValues.stripWs args with
        | [one] => one
        | _ => c
      else c
    | _ => c

@[csimp] theorem unreverse_eq_loop : @unreverse = @unreverseLoop := by
  funext xs
  fun_induction unreverse xs <;> simp_all [unreverse, unreverseLoop]

#print axioms unreverse_eq_loop

/-- A counter declaration's value: `none` gives no pairs. -/
def counterList (value : String) (dflt : Int) : Option (List (String × Int)) :=
  match unreverse (CssValues.stripWs (CssValues.CV.parse value)) with
  | [.tok (.ident k)] => if CssValues.lower k == "none" then some [] else counterPairs dflt [.tok (.ident k)]
  | cvs => counterPairs dflt cvs

#guard counterList "none" 0 == some []
#guard counterList "item" 0 == some [("item", 0)]
#guard counterList "a 2 b" 1 == some [("a", 2), ("b", 1)]
#guard counterList "a -3" 0 == some [("a", -3)]
#guard counterList "a 1.5" 0 == none
#guard counterList "inherit" 0 == none
#guard counterList "reversed(foo)" 0 == some [("foo", 0)]
#guard counterList "reversed(foo) 5 bar" 0 == some [("foo", 5), ("bar", 0)]
#guard reversedNames "reversed(foo) bar reversed(baz) 3" == ["foo"]

private def romanDigits : List (Nat × String) :=
  [(1000,"m"),(900,"cm"),(500,"d"),(400,"cd"),(100,"c"),(90,"xc"),(50,"l"),(40,"xl"),(10,"x"),(9,"ix"),(5,"v"),(4,"iv"),(1,"i")]

/-- Lower-case Roman numerals of `n` (1 to 3999). -/
def roman (n : Nat) : String := Id.run do
  let mut k := n
  let mut out := ""
  for (v, d) in romanDigits do
    for _ in [0:4] do
      if k ≥ v then
        out := out ++ d
        k := k - v
  return out

/-- `n` (at least 1) in the alphabetic system of `letters` (CSS Counter Styles 3 §3.1.3). -/
def alphabetic (letters : Array Char) (n : Nat) : String := Id.run do
  if letters.isEmpty then return toString n
  let mut k := n
  let mut out : List Char := []
  for _ in [0:64] do
    if k > 0 then
      k := k - 1
      out := letters[k % letters.size]! :: out
      k := k / letters.size
  return String.ofList out

private def latin : Array Char := "abcdefghijklmnopqrstuvwxyz".toList.toArray
private def greek : Array Char := "αβγδεζηθικλμνξοπρστυφχψω".toList.toArray

/-- `n` in the counter style `style` (CSS Counter Styles 3 §6, the predefined styles this
profile draws). An unknown style, and a value outside a style's range, is `decimal`. -/
def formatCounter (style : String) (n : Int) : String :=
  let pos := n.toNat
  match style with
  | "none" => ""
  | "disc" => "\u2022"
  | "circle" => "\u25E6"
  | "square" => "\u25AA"
  | "decimal-leading-zero" =>
    if 0 ≤ n && n < 10 then "0" ++ toString n
    else if -10 < n && n < 0 then "-0" ++ toString n.natAbs else toString n
  | "lower-roman" => if 1 ≤ n && n ≤ 3999 then roman pos else toString n
  | "upper-roman" => if 1 ≤ n && n ≤ 3999 then (roman pos).toUpper else toString n
  | "lower-alpha" | "lower-latin" => if 1 ≤ n then alphabetic latin pos else toString n
  | "upper-alpha" | "upper-latin" => if 1 ≤ n then (alphabetic latin pos).toUpper else toString n
  | "lower-greek" => if 1 ≤ n then alphabetic greek pos else toString n
  | _ => toString n

#guard formatCounter "decimal" 12 == "12"
#guard formatCounter "decimal" (-3) == "-3"
#guard formatCounter "upper-roman" 1994 == "MCMXCIV"
#guard formatCounter "lower-roman" 4 == "iv"
#guard formatCounter "lower-alpha" 1 == "a"
#guard formatCounter "lower-alpha" 27 == "aa"
#guard formatCounter "upper-alpha" 52 == "AZ"
#guard formatCounter "lower-greek" 2 == "β"
#guard formatCounter "decimal-leading-zero" 7 == "07"
#guard formatCounter "lower-roman" 0 == "0"
#guard formatCounter "none" 5 == ""

/-- The parts with each counter written as text: `values name` are the counters of that name
in scope, outermost first; a name with none is 0. -/
def withCounters (values : String → List Int) (ps : List Piece) : List Piece :=
  ps.map fun p => match p with
    | .counter n st => .text (formatCounter st ((values n).getLast?.getD 0))
    | .counters n sep st =>
      let vs := values n
      .text (sep.intercalate ((if vs.isEmpty then [0] else vs).map (formatCounter st)))
    | other => other

#guard withCounters (fun _ => [1, 2]) [.counter "a" "decimal", .counters "a" "." "decimal"] ==
  [.text "2", .text "1.2"]

/-! ### Images among the parts

`content: "a" url(i.png) "b"` is a text, an image and a text, in order (CSS 2.1 §12.2). -/

/-- A run of text, or an image, of a pseudo-element's content. -/
inductive Seg where
  | text (s : String)
  | image (url : String)
  deriving Repr, BEq, DecidableEq

/-- Whether a value has an image to draw. -/
def hasImage (ps : List Piece) : Bool := ps.any fun p => match p with | .image _ => true | _ => false

/-- The parts as runs of text and images in order: the text of each run of non-image parts
(`text`, so each at most `maxChars` characters), then the image. At most `ps.length + 1`
segments. -/
def segments (attr : String → String) (ps : List Piece) : List Seg :=
  let (segs, run) := ps.foldl (fun (acc : List Seg × List Piece) p => match p with
    | .image u => ((if acc.2.isEmpty then acc.1 else .text (text attr acc.2.reverse) :: acc.1) |> (Seg.image u :: ·), [])
    | other => (acc.1, other :: acc.2)) ([], [])
  (if run.isEmpty then segs else .text (text attr run.reverse) :: segs).reverse

#guard segments (fun _ => "v") [.text "a", .attr "x", .image "i.png", .text "b"] == [.text "av", .image "i.png", .text "b"]
#guard segments (fun _ => "") [.image "i.png"] == [.image "i.png"]
#guard segments (fun _ => "") [.image "a", .image "b"] == [.image "a", .image "b"]
#guard segments (fun _ => "") [.text "x"] == [.text "x"]
#guard hasImage [.text "x", .image "u"]
#guard !hasImage [.text "x", .blank]

end L4Factoidal.Rendering.CSS.Content
