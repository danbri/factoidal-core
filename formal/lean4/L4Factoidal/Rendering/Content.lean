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
  /-- An image, a counter, `no-open-quote`: nothing in this profile. -/
  | blank
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

/-- One component of the value as a part; `none` when it is not one. -/
def piece : CssValues.CV → Option Piece
  | .tok (.str s) => some (.text s)
  | .tok (.url _) => some .blank
  | .tok (.ident k) =>
    match CssValues.lower k with
    | "open-quote" => some (.text "\u201C")
    | "close-quote" => some (.text "\u201D")
    | "no-open-quote" | "no-close-quote" => some .blank
    | _ => none
  | .fn name args =>
    let name := CssValues.lower name
    if name == "attr" then
      match CssValues.stripWs args with
      | .tok (.ident a) :: _ => some (.attr a)
      | _ => none
    else if name == "counter" || name == "counters" || imageFunctions.contains name then some .blank
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
      | .blank => []
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
          | .blank => [])).take maxChars := by
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
#guard read "counter(item) \". \"" == some (.parts [.blank, .text ". "])
#guard read "url(a.png)" == some (.parts [.blank])
#guard read "url(a.png) / \"alt\"" == some (.parts [.blank])
#guard read "\"x\" / \"alt\"" == some (.parts [.text "x"])
#guard read "" == none
#guard read "12px" == none
#guard read "\"a\" bogus" == none
#guard read "inherit" == none
#guard text (fun _ => "v") [.text "a", .attr "x", .blank, .text "b"] == "avb"
#guard text (fun _ => "") [] == ""
#guard (text (fun _ => String.ofList (List.replicate 70000 'x')) [.attr "a", .attr "a"]).length == maxChars

end L4Factoidal.Rendering.CSS.Content
