/-
Harness.SplitReadDiff — a Turtle or TriG document read by several readers,
one for each byte range between splits (`Syntax.SplitScan`,
`Source.Reader.resume`), against the single reader of the whole document
(https://github.com/danbri/factoidal/issues/842).

`l4split-diff FILE...` reads each `.ttl` and `.trig` file (other files are
ignored) as RDF 1.2 with the base `http://example.org/dir/doc`, and compares:

* the single reader: `Source.ByteReader` over the whole document, with the
  prefix of `Source.Prepass`;
* the split read: the readers of the ranges, as the packer runs them
  (`Source.Reader.resume` with the directives, the graph block and the
  generated blank-node counter at the split), their quads and graph
  declarations put one after the other in range order. A range that ends at a
  split must end with the counter the scan counted at that split; when it
  does not, the case is a count mismatch (the packer then reads the document
  as one range) and is counted apart.

Splits tried for each file: every split alone (two ranges; at most
`maxSingles` of them, spread over the file), and the plans for 2, 3, 4 and 8
workers (`SplitScan.planOf` with targets at `size * k / K`). A case agrees
when both reads refuse the document, or both give the same sequence of
quads and graph declarations, blank-node labels included. The scan's
underscore run must also equal the one of `Source.Prepass`.

A document with `<<`, `~` or `{|` is not split by the packer
(`SplitScan.Plan.doubleLt`, `SplitScan.Plan.uncounted`); it is counted as
skipped here.

The equality is not proved; this run is its measurement (row SR-1 of
`tests/known-defects/run.sh`, https://github.com/danbri/factoidal/issues/944).

Prints one DIFF line for each disagreement, then the counts; exit 0 when
every case agrees, 1 otherwise, 2 when no file was read.
-/
import L4Factoidal.RDF.Source

open L4Factoidal.Syntax
open L4Factoidal.RDF
open L4Factoidal.RDF.Source

/-- What a reader gives, in order. -/
inductive Ev where
  | quad (t : Triple) (g : Option Subject)
  | decl (g : Subject)
  deriving BEq, Repr

def stepEv : Step (Array Ev) := fun a t g => a.push (.quad t g)
def declEv : Decl (Array Ev) := fun a g => a.push (.decl g)

def base : Option String := some "http://example.org/dir/doc"

def chunk : Nat := 65536

/-- Feed bytes `[lo, hi)` in chunks. -/
def feedRange (r : ByteReader (Array Ev)) (bytes : ByteArray) (lo hi : Nat) :
    Except Failure (ByteReader (Array Ev)) := Id.run do
  let mut r := r
  let mut p := lo
  for _ in [0:(hi - lo) / chunk + 2] do
    if p ≥ hi then break
    let q := min hi (p + chunk)
    match r.feedD stepEv declEv (bytes.extract p q) with
    | .error f => return .error f
    | .ok next => r := next
    p := q
  return .ok r

def prefixOf (bytes : ByteArray) : Option String :=
  match ({} : Prepass).feed bytes with
  | .error _ => none
  | .ok p => p.finish.toOption

def readSingle (fmt : RdfFormat) (pfx : String) (bytes : ByteArray) : Option (Array Ev) :=
  match ByteReader.init {} fmt .rdf12 base pfx #[] with
  | .error _ => none
  | .ok r =>
    match feedRange r bytes 0 bytes.size with
    | .error _ => none
    | .ok r => (r.finishD stepEv declEv).toOption

/-- The text of the directive units before a split, each followed by a line
    end (a header by `{ }` and a line end). -/
def preludeOf (bytes : ByteArray) (units : Array SplitScan.Unit) (n : Nat) : Option String := do
  let mut out := ""
  for u in units.extract 0 n do
    let t ← String.fromUTF8? (bytes.extract u.start u.stop)
    out := out ++ t ++ (if u.header then " { }\n" else "\n")
  return out

/-- The result of a split read: the events, a refusal, or a range that ended
    with another counter than the scan counted. -/
inductive SplitResult where
  | events (es : Array Ev)
  | refused
  | countMismatch
  deriving BEq

def readSplit (fmt : RdfFormat) (pfx : String) (bytes : ByteArray) (plan : SplitScan.Plan)
    (splits : Array SplitScan.Split) : SplitResult := Id.run do
  let mut acc : Array Ev := #[]
  let n := splits.size
  for i in [0:n + 1] do
    let lo := if i == 0 then 0 else splits[i - 1]!.pos
    let hi := if i == n then bytes.size else splits[i]!.pos
    let some r := (ByteReader.init {} fmt .rdf12 base pfx acc).toOption
      | return .refused
    let r ← if i == 0 then pure r else
      let sp := splits[i - 1]!
      let some prelude := preludeOf bytes plan.directives sp.directives | return .refused
      let header ← match sp.block with
        | none => pure none
        | some (a, b) =>
          match String.fromUTF8? (bytes.extract a b) with
          | some h => pure (some h)
          | none => return .refused
      match r.resume prelude header (some sp.counter) with
      | .error _ => return .refused
      | .ok r => pure r
    let some r := (feedRange r bytes lo hi).toOption | return .refused
    if i == n then
      match r.finishD stepEv declEv with
      | .error _ => return .refused
      | .ok a => acc := a
    else
      match r.finishRangeCountD stepEv declEv with
      | .error _ => return .refused
      | .ok (a, c) =>
        if c != some splits[i]!.counter then return .countMismatch
        acc := a
  return .events acc

/-- At most this many single splits are tried for one file. -/
def maxSingles : Nat := 120

def main (args : List String) : IO UInt32 := do
  let mut files := 0
  let mut cases := 0
  let mut agree := 0
  let mut accepted := 0
  let mut differ := 0
  let mut skipped := 0
  let mut mismatches := 0
  let mut splitCases := 0
  for path in args do
    let fmt ← match formatOfPath path with
      | some .turtle => pure RdfFormat.turtle
      | some .trig => pure RdfFormat.trig
      | _ => continue
    let bytes ← IO.FS.readBinFile path
    files := files + 1
    let trig := fmt == .trig
    let all := SplitScan.allSplits trig bytes
    let pfxScan := freshBnodePrefixOfLongest all.longestUnderscore
    let pfx? := prefixOf bytes
    if let some p := pfx? then
      if p != pfxScan then
        differ := differ + 1
        cases := cases + 1
        IO.println s!"DIFF {path}: scan prefix {pfxScan}, pre-pass prefix {p}"
    if all.doubleLt || all.uncounted then
      skipped := skipped + 1
      continue
    let pfx := pfx?.getD pfxScan
    let want := (readSingle fmt pfx bytes)
    -- the sets of splits
    let mut sets : Array (String × Array SplitScan.Split) := #[]
    let ns := all.splits.size
    let step := max 1 ((ns + maxSingles - 1) / maxSingles)
    for j in [0:ns] do
      if j % step == 0 then sets := sets.push (s!"split@{all.splits[j]!.pos}", #[all.splits[j]!])
    for k in [2, 3, 4, 8] do
      let targets := (Array.range (k - 1)).map fun i => bytes.size * (i + 1) / k
      let plan := SplitScan.planOf trig targets bytes
      sets := sets.push (s!"workers={k}", plan.splits)
    for (name, sp) in sets do
      cases := cases + 1
      if !sp.isEmpty then splitCases := splitCases + 1
      let got := readSplit fmt pfx bytes all sp
      if got == .countMismatch then
        mismatches := mismatches + 1
        IO.println s!"COUNT {path} {name}: a range ended with another blank-node counter than the scan counted"
        continue
      let got : Option (Array Ev) := match got with
        | .events es => some es
        | _ => none
      if got == want then
        agree := agree + 1
        if want.isSome then accepted := accepted + 1
      else
        differ := differ + 1
        let show1 (o : Option (Array Ev)) : String :=
          match o with
          | none => "refused"
          | some es => s!"{es.size} events"
        IO.println s!"DIFF {path} {name}: single {show1 want}, split {show1 got}"
  IO.println s!"l4split-diff: {files} files ({skipped} not split: <<, ~ or the annotation syntax); {agree} agree ({accepted} accepted by both, {agree - accepted} refused by both), {differ} differ (out of {cases - mismatches} cases, {splitCases} with at least one split); {mismatches} count mismatches (read as one range by the packer)"
  if files == 0 then return 2
  return (if differ == 0 then 0 else 1)
