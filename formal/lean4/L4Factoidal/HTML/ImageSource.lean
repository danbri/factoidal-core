/-
L4Factoidal.HTML.ImageSource — which image an `img` element asks for (HTML §4.8.4.2 and
§4.8.4.3): "parse a srcset attribute" (`parseSrcset`), "parse a sizes attribute"
(`sourceSize`), "update the source set" with the `source` children of a `picture`
(`sourceSet`), "normalize the source densities" and "select an image source"
(`selectFrom`, `selected`).

One function for both users: the page's `img.currentSrc` (node_query 195) and the list of
images a document wants (`selected` for each `img`).

Numbers are exact (`Rat`): a density descriptor is the decimal it is written as, so the
choice does not depend on floating-point rounding. Choosing among the densities is
"implementation-defined" in the standard; this takes the first density, in ascending order,
that is not below the device pixel ratio, and prefers the one before it when the ratio is
below their geometric mean (as Chromium does), compared exactly as `a·b ≤ r²`.

Limits: `sizes=auto` is read as no size (the next entry, or 100vw); the `type` of a `source`
is compared with the list `supportedTypes`; a density exponent beyond ±400 is clamped.
-/
import L4Factoidal.DOM.Arena
import L4Factoidal.Rendering.CssValues.Numeric
import L4Factoidal.Rendering.MediaQuery

namespace L4Factoidal.HTML.ImageSource
open L4Factoidal.DOM
open L4Factoidal.Rendering

/-- An image source: a URL and at most one of a width descriptor and a pixel density
descriptor. -/
structure Source where
  url : String
  width : Option Nat := none
  density : Option Rat := none
  deriving Repr, BEq, Inhabited

def isWs (c : Char) : Bool := c == ' ' || c == '\t' || c == '\n' || c == '\x0c' || c == '\r'

/-! ## Numbers (HTML §2.3.4) -/

def natOf (ds : List Char) : Nat := ds.foldl (fun a c => a * 10 + (c.toNat - 48)) 0

/-- A valid non-negative integer: one or more ASCII digits. -/
def nat? (cs : List Char) : Option Nat :=
  if !cs.isEmpty && cs.all Char.isDigit then some (natOf cs) else none

def pow10 (n : Nat) : Rat := ((10 ^ n : Nat) : Rat)

/-- The most a decimal exponent moves the point: more is clamped. -/
def maxExponent : Nat := 400

/-- A valid floating-point number, as the exact decimal it writes: an optional "-", digits
with an optional fraction or a fraction alone, and an optional exponent. -/
def float? (cs : List Char) : Option Rat :=
  let (neg, cs) := match cs with
    | '-' :: r => (true, r)
    | _ => (false, cs)
  let (ip, r1) := cs.span Char.isDigit
  let (fp, r2, fracOk) := match r1 with
    | '.' :: r => let (f, r') := r.span Char.isDigit; (f, r', !f.isEmpty)
    | _ => ([], r1, true)
  if !fracOk || (ip.isEmpty && fp.isEmpty) then none else
  let (expNeg, ex, r3, expOk) := match r2 with
    | c :: r =>
      if c == 'e' || c == 'E' then
        let (sneg, r') := match r with
          | '-' :: t => (true, t)
          | '+' :: t => (false, t)
          | _ => (false, r)
        let (e, r'') := r'.span Char.isDigit
        (sneg, natOf (e.take 6), r'', !e.isEmpty)
      else (false, 0, c :: r, true)
    | [] => (false, 0, [], true)
  if !expOk || !r3.isEmpty then none else
  let mant : Rat := ((natOf (ip ++ fp) : Nat) : Rat)
  -- the value is mant · 10^(±ex − |fp|)
  let up := if expNeg then 0 else Nat.min ex maxExponent
  let down := (if expNeg then Nat.min ex maxExponent else 0) + fp.length
  let v := mant * pow10 up / pow10 down
  some (if neg then -v else v)

/-! ## "Parse a srcset attribute" (§4.8.4.3.6) -/

inductive St where
  | desc | parens | after

def pushDesc (cur : List Char) (out : Array String) : Array String :=
  if cur.isEmpty then out else out.push (String.ofList cur.reverse)

/-- The descriptor tokenizer: the descriptors of one candidate (`cur` is the current
descriptor, reversed) and the input after the comma that ends it. One character a round. -/
def tokenizeDescriptors : St → List Char → List Char → Array String → Array String × List Char
  | _, [], cur, out => (pushDesc cur out, [])
  | .desc, c :: cs, cur, out =>
    if isWs c then tokenizeDescriptors .after cs [] (pushDesc cur out)
    else if c == ',' then (pushDesc cur out, cs)
    else if c == '(' then tokenizeDescriptors .parens cs (c :: cur) out
    else tokenizeDescriptors .desc cs (c :: cur) out
  | .parens, c :: cs, cur, out =>
    if c == ')' then tokenizeDescriptors .desc cs (c :: cur) out
    else tokenizeDescriptors .parens cs (c :: cur) out
  | .after, c :: cs, cur, out =>
    if isWs c then tokenizeDescriptors .after cs cur out
    else if c == ',' then (out, cs)
    else if c == '(' then tokenizeDescriptors .parens cs [c] out
    else tokenizeDescriptors .desc cs [c] out

/-- The descriptor parser: the source of a URL and its descriptors, or none on an error. -/
def withDescriptors (url : String) (ds : List String) : Option Source :=
  let step := fun (acc : Option (Option Nat × Option Rat × Option Nat)) (d : String) =>
    acc.bind fun (w, x, h) =>
      let cs := d.toList
      match cs.getLast? with
      | some 'w' =>
        match nat? cs.dropLast with
        | some n => if w.isSome || x.isSome || n == 0 then none else some (some n, x, h)
        | none => none
      | some 'x' =>
        match float? cs.dropLast with
        | some v => if w.isSome || x.isSome || h.isSome || v < 0 then none else some (w, some v, h)
        | none => none
      | some 'h' =>
        match nat? cs.dropLast with
        | some n => if h.isSome || x.isSome || n == 0 then none else some (w, x, some n)
        | none => none
      | _ => none
  match ds.foldl step (some (none, none, none)) with
  | some (w, x, h) => if h.isSome && w.isNone then none else some { url, width := w, density := x }
  | none => none

/-- The splitting loop: one candidate a round. -/
def parseGo : Nat → List Char → Array Source → Array Source
  | 0, _, out => out
  | fuel + 1, cs, out =>
    let cs := cs.dropWhile fun c => isWs c || c == ','
    if cs.isEmpty then out else
    let (url, rest) := cs.span fun c => !isWs c
    if url.getLast? == some ',' then
      let url := (url.reverse.dropWhile (· == ',')).reverse
      parseGo fuel rest (if url.isEmpty then out else out.push { url := String.ofList url })
    else
      let (ds, rest) := tokenizeDescriptors .desc (rest.dropWhile isWs) [] #[]
      match withDescriptors (String.ofList url) ds.toList with
      | some s => parseGo fuel rest (out.push s)
      | none => parseGo fuel rest out

/-- "Parse a srcset attribute": the image sources, in order. -/
def parseSrcset (s : String) : List Source := (parseGo (s.length + 1) s.toList #[]).toList

/-! ## "Parse a sizes attribute" (§4.8.4.3.7) -/

/-- What lengths and media conditions are evaluated against. -/
structure Env where
  /-- The viewport of the element's document, in CSS pixels. -/
  viewportW : Rat := 800
  viewportH : Rat := 600
  /-- Device pixels to a CSS pixel. -/
  dpr : Rat := 1
  deriving Repr, Inhabited

def Env.ctx (e : Env) : CssValues.Ctx := { viewportW := e.viewportW, viewportH := e.viewportH }

def ratFloat (r : Rat) : Float := Float.ofInt r.num / Float.ofNat r.den

def Env.media (e : Env) : MediaQuery.Env := { width := some (ratFloat e.viewportW), height := some (ratFloat e.viewportH) }

def dropEndWs (cvs : List CssValues.CV) : List CssValues.CV := (cvs.reverse.dropWhile CssValues.CV.isWs).reverse

/-- A valid non-negative source size value (a length, or a math function that is one), in
CSS pixels. A math function below zero is zero. -/
def sizeValue (e : Env) (cv : CssValues.CV) : Option Rat :=
  match CssValues.numeric (some e.ctx) { kind := .length, lo := some 0 } cv with
  | some (.tok (.dim v _ _)) => some v
  | _ => none

/-- The size of one entry of `sizes`, when its media condition (if any) holds. -/
def entrySize (e : Env) (entry : List CssValues.CV) : Option Rat :=
  match (dropEndWs entry).reverse with
  | [] => none
  | last :: before =>
    match sizeValue e last with
    | none => none
    | some v =>
      let condition := dropEndWs before.reverse
      if condition.all CssValues.CV.isWs then some v
      else if MediaQuery.applies e.media (CssValues.serialize (CssValues.trimWs condition)) then some v
      else none

/-- "Parse a sizes attribute": the source size in CSS pixels; 100vw when no entry gives one. -/
def sourceSize (e : Env) (sizes : String) : Rat :=
  match (CssValues.splitCommas (CssValues.CV.parse sizes)).findSome? (entrySize e) with
  | some v => v
  | none => e.viewportW

/-! ## Choosing (§4.8.4.3.8, §4.8.4.3.9) -/

/-- A density with no bound: a width descriptor over a source size of zero. -/
def unbounded : Rat := pow10 60

/-- "Normalize the source densities": the density of a source for a source size. -/
def densityOf (size : Rat) (s : Source) : Rat :=
  match s.density, s.width with
  | some d, _ => d
  | none, some w => if size ≤ 0 then unbounded else (w : Rat) / size
  | none, none => 1

/-- Of the entries with one density the first stays. -/
def dedupe (l : List (Source × Rat)) : List (Source × Rat) :=
  l.foldl (fun out x => if out.any (·.2 == x.2) then out else out ++ [x]) []

/-- The choice among densities in ascending order, for a device pixel ratio. -/
def choose (dpr : Rat) : List (Source × Rat) → Option (Source × Rat)
  | [] => none
  | [a] => some a
  | a :: b :: rest =>
    if b.2 < dpr then choose dpr (b :: rest)
    else if (dpr ≤ 1 && a.2 < dpr) || a.2 * b.2 ≤ dpr * dpr then some b
    else some a

/-- "Select an image source from a source set": the source and its density. -/
def selectFrom (dpr size : Rat) (set : List Source) : Option (Source × Rat) :=
  choose dpr ((dedupe (set.map fun s => (s, densityOf size s))).mergeSort fun a b => decide (a.2 ≤ b.2))

/-! ## The source set of an element (§4.8.4.3.5 "update the source set") -/

def attr (x : Node) (name : String) : Option String :=
  (x.attrs.find? fun a => a.ns.isNone && a.lname == name).map (·.value)

/-- The image types a `source` may name: those the engine decodes. -/
def supportedTypes : List String :=
  ["image/png", "image/jpeg", "image/gif", "image/webp", "image/svg+xml", "image/bmp", "image/x-icon", "image/vnd.microsoft.icon"]

/-- The essence of a MIME type string: lower case, without parameters and white space. -/
def essence (t : String) : String :=
  let head := (t.splitOn ";").headD ""
  String.ofList ((head.toList.filter fun c => !isWs c).map Char.toLower)

/-- "Create a source set" for the element itself: its `srcset`, and its `src` as the
default source when no source has the density 1 or a width. -/
def ownSet (x : Node) : List Source :=
  let set := parseSrcset ((attr x "srcset").getD "")
  match attr x "src" with
  | some src =>
    if !src.isEmpty && !set.any (fun s => s.density == some 1 || s.width.isSome) then set ++ [{ url := src }] else set
  | none => set

/-- The source set and source size of an `img`: of the first `source` before it in its
`picture` parent that has sources and whose `media` and `type` hold, else its own. -/
def sourceSet (d : Dom) (img : NodeId) (e : Env) : List Source × Rat :=
  let x := d.get img
  let own := (ownSet x, sourceSize e ((attr x "sizes").getD ""))
  match x.parent with
  | none => own
  | some p =>
    if !Dom.isHtmlElement (d.get p) "picture" then own else
    let before := (d.get p).kids.toList.takeWhile (· != img)
    let pick := before.findSome? fun k =>
      let c := d.get k
      if !Dom.isHtmlElement c "source" then none else
      match attr c "srcset" with
      | none => none
      | some srcset =>
        let set := parseSrcset srcset
        if set.isEmpty then none
        else if (attr c "media").any fun m => !(MediaQuery.applies e.media m) then none
        else if (attr c "type").any fun t => !supportedTypes.contains (essence t) then none
        else some (set, sourceSize e ((attr c "sizes").getD ""))
    pick.getD own

/-- The URL (as written) and density of the image an `img` element asks for. -/
def selected (d : Dom) (img : NodeId) (e : Env) : Option (String × Rat) :=
  let (set, size) := sourceSet d img e
  (selectFrom e.dpr size set).map fun (s, density) => (s.url, density)

/-! ## Wire (node_query 195) -/

/-- A decimal number of the page ("1", "1.5", "0.75"); zero when it is not one. -/
def ratOf (s : String) : Rat := (float? s.toList).getD 0

/-- node_query 195 on an `img`: `q` is the device pixel ratio, U+0000, the viewport's width,
U+0000, its height (decimals). Answers "" when the element asks for no image, else "1" and
the URL as written. -/
def answer (d : Dom) (img : NodeId) (q : String) : String :=
  match q.splitOn "\x00" with
  | [dpr, w, h] =>
    match selected d img { dpr := ratOf dpr, viewportW := ratOf w, viewportH := ratOf h } with
    | some (url, _) => "1" ++ url
    | none => ""
  | _ => ""

/-! ## What is proved -/

theorem choose_mem (dpr : Rat) : ∀ (l : List (Source × Rat)) (x : Source × Rat), choose dpr l = some x → x ∈ l := by
  intro l
  induction l with
  | nil => intro x h; simp [choose] at h
  | cons a t ih =>
    intro x h
    cases t with
    | nil => simp [choose] at h; simp [h]
    | cons b rest =>
      simp only [choose] at h
      split at h
      · exact List.mem_cons_of_mem _ (ih x h)
      · split at h
        · cases h; simp
        · cases h; simp

theorem dedupe_sub (l : List (Source × Rat)) : ∀ x, x ∈ dedupe l → x ∈ l := by
  have key : ∀ (l acc : List (Source × Rat)) (x : Source × Rat),
      x ∈ l.foldl (fun out y => if out.any (·.2 == y.2) then out else out ++ [y]) acc → x ∈ acc ∨ x ∈ l := by
    intro l
    induction l with
    | nil => intro acc x h; exact Or.inl h
    | cons y t ih =>
      intro acc x h
      simp only [List.foldl_cons] at h
      rcases ih _ x h with h1 | h1
      · split at h1
        · exact Or.inl h1
        · rcases List.mem_append.mp h1 with h2 | h2
          · exact Or.inl h2
          · simp at h2; exact Or.inr (by simp [h2])
      · exact Or.inr (List.mem_cons_of_mem _ h1)
  intro x h
  rcases key l [] x h with h1 | h1
  · cases h1
  · exact h1

/-- Says: the selected image source is one of the sources of the set: the engine never asks
for a URL that the element does not list. -/
theorem selectFrom_mem (dpr size : Rat) (set : List Source) (x : Source × Rat)
    (h : selectFrom dpr size set = some x) : x.1 ∈ set := by
  unfold selectFrom at h
  have h1 := choose_mem dpr _ x h
  have h2 := dedupe_sub _ x ((List.mem_mergeSort).mp h1)
  rcases List.mem_map.mp h2 with ⟨s, hs, rfl⟩
  exact hs

/-- Says: an empty source set selects nothing, and a set of one source selects it. -/
theorem selectFrom_nil (dpr size : Rat) : selectFrom dpr size [] = none := by
  simp [selectFrom, dedupe, choose]

/-- Says: the splitting loop with no input gives no source. -/
theorem parseSrcset_empty : parseSrcset "" = [] := by decide

/-! ## Tests (srcset/parse-a-srcset-attribute.html, sizes/support/sizes-iframed.sub.html) -/

private def pick (srcset : String) : String :=
  match selectFrom 1 800 (parseSrcset srcset) with
  | some (s, _) => s.url
  | none => ""

-- the splitting loop
#guard pick "" == "" && pick "," == "" && pick ",,," == ""
#guard pick "  data:,a  1x  " == "data:,a" && pick "\t\tdata:,a\t\t1x\t\t" == "data:,a" && pick "\n\ndata:,a\n\n1x\n\n" == "data:,a"
#guard pick "\x0bdata:,a\x0b1x\x0b" == "\x0bdata:,a\x0b1x\x0b"
#guard pick "data:,a" == "data:,a" && pick "data:,a " == "data:,a" && pick "data:,a ," == "data:,a" && pick "data:,a," == "data:,a"
#guard pick "data:,a, " == "data:,a" && pick "data:,a,,," == "data:,a" && pick "data:,a,, , " == "data:,a"
#guard pick " data:,a" == "data:,a" && pick ",,,data:,a" == "data:,a" && pick " , ,,data:,a" == "data:,a"
-- the descriptor tokenizer
#guard pick "data:,a 1x" == "data:,a" && pick "data:,a 1x " == "data:,a" && pick "data:,a 1x," == "data:,a"
#guard pick "data:,a ( , data:,b 1x, ), data:,c" == "data:,c" && pick "data:,a ((( , data:,b 1x, ), data:,c" == "data:,c"
#guard pick "data:,a [ , data:,b 1x, ], data:,c" == "data:,b" && pick "data:,a { , data:,b 1x, }, data:,c" == "data:,b"
#guard pick "data:,a \" , data:,b 1x, \", data:,c" == "data:,b" && pick "data:,a \\,data:;\\,b, data:,c" == "data:;\\,b"
#guard pick "data:,a, data:,b (" == "data:,a" && pick "data:,a, data:,b (  " == "data:,a" && pick "data:,a, data:,b (," == "data:,a"
#guard pick "data:,a, data:,b (x" == "data:,a" && pick "data:,a, data:,b ()" == "data:,a" && pick "data:,a (, data:,b" == ""
#guard pick "data:,a /*, data:,b, data:,c */" == "data:,b" && pick "data:,a //, data:,b" == "data:,b"
-- the descriptor parser
#guard pick "data:,a foo" == "" && pick "data:,a foo foo" == "" && pick "data:,a foo 1x" == "" && pick "data:,a foo 1x foo" == ""
#guard pick "data:,a foo 1w" == "" && pick "data:,a 1x 1x" == "" && pick "data:,a 1w 1w" == "" && pick "data:,a 1w 1x" == "" && pick "data:,a 1x 1w" == ""
#guard pick "data:,a 1w 1h" == "data:,a" && pick "data:,a 1h 1w" == "data:,a" && pick "data:,a 1h" == "" && pick "data:,a 1h 1x" == ""
#guard pick "data:,a 0w" == "" && pick "data:,a -1w" == "" && pick "data:,a 1.0w" == "" && pick "data:,a +1w" == "" && pick "data:,a 1e0w" == ""
#guard pick "data:,a 0x" == "data:,a" && pick "data:,a -0x" == "data:,a" && pick "data:,a -1x" == "" && pick "data:,a +1x" == ""
#guard pick "data:,a 1.x" == "" && pick "data:,a .5x" == "data:,a" && pick "data:,a 1e2x" == "data:,a" && pick "data:,a 1e-2x" == "data:,a"
#guard pick "data:,a 1x, data:,b 2x" == "data:,a" && pick "data:,a 2x, data:,b 1x" == "data:,b"
#guard float? "1.5".toList == some ((3 : Rat) / 2) && float? "1e2".toList == some 100 && float? ".5e1".toList == some 5 &&
  float? "-0".toList == some 0 && float? "1.".toList == none && float? "".toList == none && float? "1e".toList == none &&
  float? "2e-1".toList == some ((1 : Rat) / 5) && float? "1e999999".toList == some (pow10 maxExponent)
-- sizes: the source size for a viewport of 1000 by 1000
private def size (sizes : String) : Rat := sourceSize { viewportW := 1000, viewportH := 1000 } sizes
#guard size "" == 1000 && size "100vw" == 1000 && size "1px" == 1 && size "0" == 0 && size "-0" == 0 && size "+0" == 0
#guard size "+1px" == 1 && size ".1px" == (1 : Rat) / 10 && size "0.1em" == (16 : Rat) / 10 && size "0.1vw" == 1 && size "0.1vh" == 1
#guard size "/* */1px/* */" == 1 && size " /**/ /**/ 1px /**/ /**/ " == 1
#guard size "-1px" == 1000 && size "1" == 1000 && size "1%" == 1000 && size "x" == 1000
#guard size "calc(1px)" == 1 && size "calc(1px + 1px)" == 2 && size "calc(-5px)" == 0
#guard size "(min-width:0) 1px" == 1 && size "(min-width:2000px) 1px, 2px" == 2 && size "(min-width:2000px) 1px" == 1000
#guard size "not (min-width:2000px) 1px" == 1 && size "1px, 2px" == 1 && size "-1px, 2px" == 2
-- widths: 300w and 301w at 100vw of 1000 are both below 1: the larger; at 1px both are above: the smaller
#guard (selectFrom 1 1000 (parseSrcset "a 300w, b 301w")).map (·.1.url) == some "b"
#guard (selectFrom 1 1 (parseSrcset "a 50w, b 51w")).map (·.1.url) == some "a"
#guard (selectFrom 2 1000 (parseSrcset "a 1x, b 2x, c 3x")).map (·.1.url) == some "b"
#guard (selectFrom ((3 : Rat) / 2) 1000 (parseSrcset "a 1x, b 2x")).map (·.1.url) == some "b"
#guard (selectFrom ((13 : Rat) / 10) 1000 (parseSrcset "a 1x, b 2x")).map (·.1.url) == some "a"
#guard (selectFrom 1 1000 (parseSrcset "a 1x, b 1x")).map (·.1.url) == some "a"

private def pictureDoc : Dom := { nodes := #[
  { type := .document, kids := #[1], htmlDoc := true },
  { type := .element, ns := some htmlNS, lname := "picture", parent := some 0, kids := #[2, 3, 4] },
  { type := .element, ns := some htmlNS, lname := "source", parent := some 1,
    attrs := #[{ lname := "srcset", value := "wide.png" }, { lname := "media", value := "(min-width: 2000px)" }] },
  { type := .element, ns := some htmlNS, lname := "source", parent := some 1,
    attrs := #[{ lname := "srcset", value := "a.avif" }, { lname := "type", value := "image/avif" }] },
  { type := .element, ns := some htmlNS, lname := "img", parent := some 1,
    attrs := #[{ lname := "src", value := "fallback.png" }, { lname := "srcset", value := "two.png 2x" }] },
  { type := .element, ns := some htmlNS, lname := "img", attrs := #[{ lname := "src", value := "plain.png" }] },
  { type := .element, ns := some htmlNS, lname := "img" }] }

#guard (selected pictureDoc 4 {}).map (·.1) == some "fallback.png"
#guard (selected pictureDoc 4 { dpr := 2 }).map (·.1) == some "two.png"
#guard (selected pictureDoc 4 { viewportW := 2400 }).map (·.1) == some "wide.png"
#guard (selected pictureDoc 5 {}).map (·.1) == some "plain.png" && selected pictureDoc 6 {} == none
#guard answer pictureDoc 4 "2\x00800\x00600" == "1two.png" && answer pictureDoc 6 "1\x00800\x00600" == ""

end L4Factoidal.HTML.ImageSource
