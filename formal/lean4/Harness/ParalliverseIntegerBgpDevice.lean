import L4Factoidal.Paralliverse.IntegerBgp

/-! Independent native-Lean expected outputs for actual GPU BGP execution.
The only generated data are integer-coded RDF triples. No JavaScript query
engine is used in these fixtures; each expected join and per-input row
count comes from the native Lean BGP specifications. -/

open L4Factoidal.Paralliverse.IntegerBgp

private def kp : UInt32 := 7
private def wp : UInt32 := 11
private def atlas : UInt32 := 12
private def orion : UInt32 := 13
private def labelPred : UInt32 := 15

private def term (i : Nat) : UInt32 := UInt32.ofNat (i+1)

private def makeGraph (n : Nat) : Triples :=
  (List.range n).flatMap fun i =>
    [⟨term i, kp, term ((i+1)%n)⟩,
     ⟨term i, kp, term ((i+7)%n)⟩,
     ⟨term i, wp, if i%4 == 0 then atlas else orion⟩,
     ⟨term i, labelPred, UInt32.ofNat (20000+i)⟩]

private def joinCountAt (g : Triples) (t : Triple) : Nat :=
  if t.p == kp then
    (g.filter fun b => b.p == wp && b.o == atlas && b.s == t.o).length
  else 0

private def array (values : List String) : String :=
  "[" ++ String.intercalate "," values ++ "]"

private def w (x : UInt32) : String := toString x.toNat

private def tripleJson (t : Triple) : String :=
  array [w t.s, w t.p, w t.o]

private def solutionJson (b : PairBinding) : String :=
  array [w b.person, w b.colleague]

private def fixtureJson (n : Nat) : String := Id.run do
  let g := makeGraph n
  let counts := g.map (joinCountAt g)
  let starts := counts.scanl (·+·) 0
  let expected := bgpSpec kp wp atlas g
  let left := selectKnows kp g
  let right := selectAtlas wp atlas g
  let joinCounts := matchCounts left right
  let joinOffsets := joinCounts.scanl (·+·) 0
  return "{" ++
    "\"kind\":\"fixture\"," ++
    "\"people\":" ++ toString n ++ "," ++
    "\"triples\":" ++ array (g.map tripleJson) ++ "," ++
    "\"counts\":" ++ array (counts.map toString) ++ "," ++
    "\"offsets\":" ++ array (starts.map toString) ++ "," ++
    "\"left\":" ++ array (left.map solutionJson) ++ "," ++
    "\"right\":" ++ array (right.map w) ++ "," ++
    "\"joinCounts\":" ++ array (joinCounts.map toString) ++ "," ++
    "\"joinOffsets\":" ++ array (joinOffsets.map toString) ++ "," ++
    "\"expected\":" ++ array (expected.map solutionJson) ++
    "}"

def main : IO Unit := do
  for n in [0,8,64,256,1024] do
    let g := makeGraph n
    let expected := bgpSpec kp wp atlas g
    let gpuCounts := g.map (joinCountAt g)
    if expected.length != gpuCounts.sum then
      throw (IO.userError s!"Native Lean BGP fixture {n}: count/joins disagree")
    IO.println (fixtureJson n)
