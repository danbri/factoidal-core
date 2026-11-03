import L4Factoidal.Rendering.SfntKern

/-!
# GSUB substitution in Lean

Third stage of the Lean shaper (https://github.com/danbri/factoidal/issues/1233).
Features: the ones HarfBuzz enables by default for a horizontal run of the
default shaper, `rvrn`, `ccmp`, `locl`, `rlig`, `liga`, `clig`, `calt`, plus
the required feature of the language system. As in HarfBuzz, `rvrn` lookups
run in a first stage; all other lookups then run once each, in lookup list
order, over the whole run.

Lookup types: 1 (single), 2 (multiple), 4 (ligature), 5 (context) and 6
(chained context), formats 1 to 3, and 7 (extension of these). Lookup flags IgnoreBaseGlyphs, IgnoreLigatures, IgnoreMarks and the
mark attachment type use the GDEF glyph and mark attachment classes of the
current glyphs. Nested lookups of a context rule apply in record order at the
matched positions, with recursion bounded at depth 8. Refused, with a message
naming the lookup: types 3 and 8, and mark filtering sets.
Feature variations (`rvrn` substitutions chosen by axis values) are not read;
the default feature table is used. OpenType GSUB chapter is the reference;
HarfBuzz is the differential oracle.
-/
namespace L4Factoidal.Rendering.SfntSubst
open FontPolicy SfntMetrics SfntKern

private def need (b : ByteArray) (i n : Nat) (what : String) : Except String Unit :=
  if i + n ≤ b.size then pure () else throw s!"font.file.malformed: GSUB {what} out of bounds"
private def u16 (b : ByteArray) (i : Nat) : Nat := (b.get! i).toNat * 256 + (b.get! (i + 1)).toNat
private def u32 (b : ByteArray) (i : Nat) : Nat := u16 b i * 65536 + u16 b (i + 2)
private def tagAt (b : ByteArray) (i : Nat) : String :=
  String.ofList ((List.range 4).map fun k => Char.ofNat (b.get! (i + k)).toNat)

def defaultFeatures : List String := ["rvrn", "ccmp", "locl", "rlig", "liga", "clig", "calt"]

/-- Lookup indices of the given features (and the required feature) in the
default language system of `script` or `DFLT`, as (stage, index) with stage 0
for `rvrn`, sorted. -/
def featureLookups (b : ByteArray) (tbl : Nat) (script : String) (features : List String) :
    Except String (List (Nat × Nat)) := do
  need b tbl 10 "header"
  let scripts := tbl + u16 b (tbl + 4)
  let featureList := tbl + u16 b (tbl + 6)
  need b scripts 2 "script list"
  let ns := u16 b scripts
  need b (scripts + 2) (6 * ns) "script records"
  let find (tag : String) : Option Nat :=
    (List.range ns).findSome? fun k =>
      if tagAt b (scripts + 2 + 6 * k) == tag then some (scripts + u16 b (scripts + 2 + 6 * k + 4)) else none
  let some s := (find script).orElse (fun _ => find "DFLT") | return []
  need b s 4 "script table"
  if u16 b s == 0 then return []
  let lang := s + u16 b s
  need b lang 6 "language system"
  let required := u16 b (lang + 2)
  let nf := u16 b (lang + 4)
  need b (lang + 6) (2 * nf) "feature indices"
  need b featureList 2 "feature list"
  let nfl := u16 b featureList
  need b (featureList + 2) (6 * nfl) "feature records"
  let indices := (List.range nf).map (fun k => u16 b (lang + 6 + 2 * k)) ++ (if required == 0xFFFF then [] else [required])
  -- One flag for each (stage, lookup index); reading them in order gives the
  -- sorted, distinct list with no recursion.
  let mut used : Array Bool := Array.replicate (2 * 65536) false
  for fi in indices do
    if fi ≥ nfl then throw "font.file.malformed: GSUB feature index"
    let r := featureList + 2 + 6 * fi
    let tag := tagAt b r
    if features.contains tag || fi == required then
      let f := featureList + u16 b (r + 4)
      need b f 4 "feature table"
      let nl := u16 b (f + 2)
      need b (f + 4) (2 * nl) "feature lookups"
      for j in [0:nl] do
        let stage := if tag == "rvrn" then 0 else 1
        used := used.set! (stage * 65536 + u16 b (f + 4 + 2 * j)) true
  let mut out : Array (Nat × Nat) := #[]
  for k in [0:2 * 65536] do
    if used[k]! then out := out.push (k / 65536, k % 65536)
  return out.toList

/-- The result of one lookup at one position. -/
inductive Step where
  | none
  /-- Replace glyph i by these glyphs. -/
  | replace (glyphs : List Nat)
  /-- Replace glyph i by `lig` and delete these later positions. -/
  | ligate (lig : Nat) (remove : List Nat)

/-- Apply one subtable of type 1, 2 or 4 at position i. `next k` gives the next
position after k that the lookup flags do not skip. -/
def applySubtable (b : ByteArray) (ltype sub : Nat) (ids : Array Nat) (i : Nat)
    (next : Nat → Option Nat) : Except String Step := do
  need b sub 6 "subtable header"
  let fmt := u16 b sub
  let some ci ← coverage b (sub + u16 b (sub + 2)) ids[i]! | return .none
  match ltype with
  | 1 =>
    if fmt == 1 then return .replace [(ids[i]! + u16 b (sub + 4)) % 65536]
    else if fmt == 2 then
      let n := u16 b (sub + 4)
      if ci ≥ n then throw "font.file.malformed: single substitution index"
      need b (sub + 6) (2 * n) "single substitutes"
      return .replace [u16 b (sub + 6 + 2 * ci)]
    else throw s!"font.file.malformed: single substitution format {fmt}"
  | 2 =>
    let n := u16 b (sub + 4)
    if ci ≥ n then throw "font.file.malformed: multiple substitution index"
    need b (sub + 6) (2 * n) "sequence offsets"
    let seq := sub + u16 b (sub + 6 + 2 * ci)
    need b seq 2 "sequence"
    let m := u16 b seq
    need b (seq + 2) (2 * m) "sequence glyphs"
    return .replace ((List.range m).map fun k => u16 b (seq + 2 + 2 * k))
  | 4 =>
    let n := u16 b (sub + 4)
    if ci ≥ n then throw "font.file.malformed: ligature set index"
    need b (sub + 6) (2 * n) "ligature set offsets"
    let set := sub + u16 b (sub + 6 + 2 * ci)
    need b set 2 "ligature set"
    let count := u16 b set
    need b (set + 2) (2 * count) "ligature offsets"
    for k in [0:count] do
      let lig := set + u16 b (set + 2 + 2 * k)
      need b lig 4 "ligature"
      let comps := u16 b (lig + 2)
      if comps == 0 then throw "font.file.malformed: ligature with no components"
      need b (lig + 4) (2 * (comps - 1)) "ligature components"
      -- Match the components against the following unskipped glyphs.
      let mut pos := i
      let mut matched : List Nat := []
      let mut ok := true
      for c in [0:comps - 1] do
        match next pos with
        | some p =>
          if ids[p]! == u16 b (lig + 4 + 2 * c) then
            matched := matched ++ [p]
            pos := p
          else
            ok := false
            break
        | none =>
          ok := false
          break
      if ok then return .ligate (u16 b lig) matched
    return .none
  | t => throw s!"font.layout.unsupported: GSUB lookup type {t} (https://github.com/danbri/factoidal/issues/1233)"

/-- What a GSUB pass needs from the font. -/
structure Ctx where
  f : Face
  b : ByteArray
  lookupList : Nat
  count : Nat
  gdef? : Option Nat
  limits : Limits

/-- Lookup type (extensions resolved), flag and subtables (type, offset). -/
def lookupInfo (c : Ctx) (l : Nat) : Except String (Nat × Nat × Array (Nat × Nat)) := do
  let b := c.b
  if l ≥ c.count then throw "font.file.malformed: GSUB lookup index"
  need b (c.lookupList + 2 + 2 * l) 2 "lookup offset"
  let lk := c.lookupList + u16 b (c.lookupList + 2 + 2 * l)
  need b lk 6 "lookup"
  let ltype := u16 b lk
  let flag := u16 b (lk + 2)
  if flag &&& 0x10 != 0 then
    throw s!"font.layout.unsupported: GSUB lookup {l} uses a mark filtering set (https://github.com/danbri/factoidal/issues/1233)"
  let nsub := u16 b (lk + 4)
  need b (lk + 6) (2 * nsub) "subtable offsets"
  let mut subs : Array (Nat × Nat) := #[]
  for k in [0:nsub] do
    let s := lk + u16 b (lk + 6 + 2 * k)
    if ltype == 7 then
      need b s 8 "extension"
      subs := subs.push (u16 b (s + 2), s + u32 b (s + 4))
    else subs := subs.push (ltype, s)
  for (t, _) in subs do
    unless t == 1 || t == 2 || t == 4 || t == 5 || t == 6 do
      throw s!"font.layout.unsupported: GSUB lookup {l} has type {t} (https://github.com/danbri/factoidal/issues/1233)"
  return (if ltype == 7 then (subs[0]?.map (·.1)).getD 7 else ltype, flag, subs)

/-- Positions that a lookup flag does not skip. -/
def unskipped (c : Ctx) (flag : Nat) (run : Array NominalGlyph) : Except String (Array Bool) :=
  run.mapM fun g => do pure !(skips flag (← gdefClasses c.b c.gdef? g.id))

def nextOf (keep : Array Bool) (k : Nat) : Option Nat :=
  ((List.range (keep.size - k - 1)).map (k + 1 + ·)).find? (keep[·]!)
def prevOf (keep : Array Bool) (k : Nat) : Option Nat :=
  ((List.range k).reverse).find? (keep[·]!)

/-- Match `n` glyphs forward from after position `k` (exclusive) with `test`. -/
def matchForward (keep : Array Bool) (k n : Nat) (test : Nat → Nat → Except String Bool) :
    Except String (Option (List Nat)) := do
  let mut pos := k
  let mut acc : List Nat := []
  for j in [0:n] do
    let some p := nextOf keep pos | return none
    unless ← test j p do return none
    acc := acc ++ [p]
    pos := p
  return some acc

/-- Match `n` glyphs backward from before position `k`. -/
def matchBackward (keep : Array Bool) (k n : Nat) (test : Nat → Nat → Except String Bool) :
    Except String Bool := do
  let mut pos := k
  for j in [0:n] do
    let some p := prevOf keep pos | return false
    unless ← test j p do return false
    pos := p
  return true

/-- Match a context (type 5) or chained context (type 6) subtable at i.
Result: the input positions (first is i) and the (sequence index, lookup)
records. -/
def matchContext (c : Ctx) (t s : Nat) (ids : Array Nat) (keep : Array Bool) (i : Nat) :
    Except String (Option (List Nat × List (Nat × Nat))) := do
  let b := c.b
  need b s 2 "context header"
  let fmt := u16 b s
  let records (r n : Nat) : Except String (List (Nat × Nat)) := do
    need b r (4 * n) "lookup records"
    return (List.range n).map fun k => (u16 b (r + 4 * k), u16 b (r + 4 * k + 2))
  -- Read a rule (formats 1 and 2) and test it with `val k` = the value
  -- (glyph id or class) of position k.
  let rule (r : Nat) (val : Nat → Except String Nat) (bval lval : Nat → Except String Nat) :
      Except String (Option (List Nat × List (Nat × Nat))) := do
    if t == 5 then
      need b r 4 "context rule"
      let gc := u16 b r
      let sc := u16 b (r + 2)
      if gc == 0 then return none
      need b (r + 4) (2 * (gc - 1)) "context rule input"
      let some inp ← matchForward keep i (gc - 1) (fun j p => do pure ((← val p) == u16 b (r + 4 + 2 * j))) | return none
      return some (i :: inp, ← records (r + 4 + 2 * (gc - 1)) sc)
    else
      need b r 2 "chain rule"
      let bc := u16 b r
      need b (r + 2) (2 * bc + 2) "chain rule backtrack"
      let ok ← matchBackward keep i bc (fun j p => do pure ((← bval p) == u16 b (r + 2 + 2 * j)))
      if !ok then return none
      let ir := r + 2 + 2 * bc
      let ic := u16 b ir
      if ic == 0 then return none
      need b (ir + 2) (2 * (ic - 1) + 2) "chain rule input"
      let some inp ← matchForward keep i (ic - 1) (fun j p => do pure ((← val p) == u16 b (ir + 2 + 2 * j))) | return none
      let lr := ir + 2 + 2 * (ic - 1)
      let lc := u16 b lr
      need b (lr + 2) (2 * lc + 2) "chain rule lookahead"
      let last := (inp.getLast?).getD i
      let some _ ← matchForward keep last lc (fun j p => do pure ((← lval p) == u16 b (lr + 2 + 2 * j))) | return none
      let sr := lr + 2 + 2 * lc
      return some (i :: inp, ← records (sr + 2) (u16 b sr))
  let ruleSet (set : Nat) (val bval lval : Nat → Except String Nat) :
      Except String (Option (List Nat × List (Nat × Nat))) := do
    need b set 2 "rule set"
    let n := u16 b set
    need b (set + 2) (2 * n) "rule offsets"
    for k in [0:n] do
      if let some m ← rule (set + u16 b (set + 2 + 2 * k)) val bval lval then return some m
    return none
  let glyph (k : Nat) : Except String Nat := pure ids[k]!
  if fmt == 1 then
    need b s 6 "context format 1"
    let some ci ← coverage b (s + u16 b (s + 2)) ids[i]! | return none
    let n := u16 b (s + 4)
    if ci ≥ n then return none
    need b (s + 6) (2 * n) "rule set offsets"
    let off := u16 b (s + 6 + 2 * ci)
    if off == 0 then return none
    ruleSet (s + off) glyph glyph glyph
  else if fmt == 2 then
    let hdr := if t == 5 then 8 else 12
    need b s hdr "context format 2"
    let some _ ← coverage b (s + u16 b (s + 2)) ids[i]! | return none
    let cls (o : Nat) (k : Nat) : Except String Nat := if o == 0 then pure 0 else classOf b (s + o) ids[k]!
    let (bo, io, lo) := if t == 5 then (0, u16 b (s + 4), 0) else (u16 b (s + 4), u16 b (s + 6), u16 b (s + 8))
    let n := u16 b (s + hdr - 2)
    need b (s + hdr) (2 * n) "class rule set offsets"
    let c0 ← cls io i
    if c0 ≥ n then return none
    let off := u16 b (s + hdr + 2 * c0)
    if off == 0 then return none
    ruleSet (s + off) (cls io) (cls bo) (cls lo)
  else if fmt == 3 then
    let cov (o : Nat) (k : Nat) : Except String Bool := do pure (← coverage b (s + o) ids[k]!).isSome
    if t == 5 then
      need b s 6 "context format 3"
      let gc := u16 b (s + 2)
      let sc := u16 b (s + 4)
      if gc == 0 then return none
      need b (s + 6) (2 * gc) "context coverages"
      unless ← cov (u16 b (s + 6)) i do return none
      let some inp ← matchForward keep i (gc - 1) (fun j p => cov (u16 b (s + 6 + 2 * (j + 1))) p) | return none
      return some (i :: inp, ← records (s + 6 + 2 * gc) sc)
    else
      need b s 4 "chain format 3"
      let bc := u16 b (s + 2)
      need b (s + 4) (2 * bc + 2) "chain backtrack coverages"
      let ir := s + 4 + 2 * bc
      let ic := u16 b ir
      if ic == 0 then return none
      need b (ir + 2) (2 * ic + 2) "chain input coverages"
      unless ← cov (u16 b (ir + 2)) i do return none
      let ok ← matchBackward keep i bc (fun j p => cov (u16 b (s + 4 + 2 * j)) p)
      if !ok then return none
      let some inp ← matchForward keep i (ic - 1) (fun j p => cov (u16 b (ir + 2 + 2 * (j + 1))) p) | return none
      let lr := ir + 2 + 2 * ic
      let lc := u16 b lr
      need b (lr + 2) (2 * lc + 2) "chain lookahead coverages"
      let last := (inp.getLast?).getD i
      let some _ ← matchForward keep last lc (fun j p => cov (u16 b (lr + 2 + 2 * j)) p) | return none
      let sr := lr + 2 + 2 * lc
      return some (i :: inp, ← records (sr + 2) (u16 b sr))
  else throw s!"font.file.malformed: context format {fmt}"

/-- Replace position i by glyphs (multiple substitution) or by a ligature that
absorbs later positions. Returns the new run and a map from old to new
positions (none for absorbed ones). -/
def edit (c : Ctx) (run : Array NominalGlyph) (i : Nat) (step : Step) :
    Except String (Array NominalGlyph × (Nat → Option Nat)) := do
  match step with
  | .none => return (run, some)
  | .replace gs =>
    if gs.any (· ≥ c.f.numGlyphs) then throw "font.file.malformed: GSUB glyph id beyond numGlyphs"
    let src := run[i]!
    let repl := gs.toArray.map fun g => { src with id := g, advance := c.f.advances[g]! }
    let shift := gs.length
    return (run.extract 0 i ++ repl ++ run.extract (i + 1) run.size,
            fun k => if k < i then some k else if k == i then (if shift == 0 then none else some i) else some (k + shift - 1))
  | .ligate lig remove =>
    if lig ≥ c.f.numGlyphs then throw "font.file.malformed: GSUB glyph id beyond numGlyphs"
    let src := run[i]!
    let mut run := run.set! i { src with id := lig, advance := c.f.advances[lig]! }
    -- HarfBuzz merges the clusters of the whole matched range into the first.
    let last := remove.foldl max i
    for k in [i:last + 1] do
      let g := run[k]!
      run := run.set! k { g with cluster := min g.cluster src.cluster }
    let mut kept : Array NominalGlyph := #[]
    for k in [0:run.size] do
      unless remove.contains k do kept := kept.push run[k]!
    return (kept, fun k => if remove.contains k then none else some (k - (remove.filter (· < k)).length))

/-- Apply lookup `l` at position i once. Returns the new run and the position
after the matched input, or none when no subtable matched. Recursion through
context lookups is bounded by `depth`. -/
def applyAt (c : Ctx) : Nat → Nat → Array NominalGlyph → Nat → Except String (Option (Array NominalGlyph × Nat))
  | 0, _, _, _ => throw "font.layout.limit: nested GSUB context lookups deeper than 8"
  | depth + 1, l, run, i => do
    let (_, flag, subs) ← lookupInfo c l
    let keep ← unskipped c flag run
    if !keep[i]! then return none
    let ids := run.map (·.id)
    for (t, s) in subs do
      if t == 5 || t == 6 then
        let some (inputs, recs) ← matchContext c t s ids keep i | continue
        let mut cur := run
        let mut pos : List (Option Nat) := inputs.map some
        for (seq, nested) in recs do
          let some (some p) := pos[seq]? | continue
          match ← applyAt c depth nested cur p with
          | none => pure ()
          | some (next, _) =>
            -- Recompute where the remaining inputs are: positions after p shift
            -- by the change in length; positions inside a ligature are gone.
            let delta : Int := (next.size : Int) - cur.size
            pos := pos.map fun o => o.bind fun q =>
              if q < p then some q else if q == p then some p
              else if delta ≥ 0 then some (q + delta.toNat)
              else if (q : Int) + delta ≤ p then none else some (q - delta.natAbs)
            cur := next
        let lastIn := (pos.filterMap id).foldl max i
        return some (cur, lastIn + 1)
      else
        let step ← applySubtable c.b t s ids i (nextOf keep)
        match step with
        | .none => pure ()
        | _ =>
          let (next, _) ← edit c run i step
          let after := match step with
            | .replace gs => i + max 1 gs.length
            | _ => i + 1
          return some (next, after)
    return none

/-- Apply the default GSUB features to a nominal run. Advances are re-read
from `hmtx` for every substituted glyph. -/
def substitute (f : Face) (b : ByteArray) (dir : Array TableRecord) (text : String)
    (run : Array NominalGlyph) (limits : Limits := {}) : Except String (Array NominalGlyph) := do
  let some gsubRec := dir.find? (·.tag == "GSUB") | return run
  let gsub := gsubRec.offset
  let lookups ← featureLookups b gsub (scriptTag text) defaultFeatures
  let lookupList := gsub + u16 b (gsub + 8)
  need b lookupList 2 "lookup list"
  let c : Ctx := { f, b, lookupList, count := u16 b lookupList,
                   gdef? := (dir.find? (·.tag == "GDEF")).map (·.offset), limits }
  let mut out := run
  let mut ops := 0
  for (_, l) in lookups do
    let mut i := 0
    -- Each step moves i forward by at least one position.
    for _ in [0:limits.lookupOperationsPerRun] do
      if i ≥ out.size then break
      ops := ops + 1
      if ops > limits.lookupOperationsPerRun then
        throw s!"font.layout.limit: more than {limits.lookupOperationsPerRun} lookup operations in one run"
      match ← applyAt c 8 l out i with
      | none => i := i + 1
      | some (next, after) =>
        out := next
        i := max (i + 1) after
  return out

end L4Factoidal.Rendering.SfntSubst
