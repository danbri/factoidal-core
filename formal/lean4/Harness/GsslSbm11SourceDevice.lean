import L4Factoidal.Storage.Sbm11.PackSpec
import L4Factoidal.GpuDomainSpecificLanguage.Sbm11U64Lanes

/-!
Native Lean oracle for testing actual WebGPU against GSSL BGP over genuine
SBM11 TermId values, NOT handpicked JavaScript constants.

The RDF graph is generated here as WfIri, bnode, string literal and
RDF 1.2 triple terms. PackSpec.keysOf? produces the exact GDV1
byte-ordered deduplicated dictionary keys, and Sbm11.toId? produces
the tag/rank-aware canonical UInt64 TermIds. The independent reference
BGP rows are computed by the Lean Sbm11U64Lanes.bgpSpec.

This is an in-memory PackSpec dictionary rather than an activated
persisted generation read from disk. It does not authenticate a
generation manifest, bind the async query to an active graph, or prove
WGSL bytecode/driver semantics.
-/

namespace Harness.GsslSbm11SourceDevice

open L4Factoidal.RDF
open L4Factoidal.Storage.Sbm11
open L4Factoidal.Storage.Sbm11.PackSpec
open L4Factoidal.Storage.Sbm11.MemGen
open L4Factoidal.GpuDomainSpecificLanguage.Sbm11U64Lanes

private def iri? (s : String) : Option WfIri :=
  if h : isIri s then some ⟨s, h⟩ else none

private def person? (i : Nat) : Option WfIri :=
  iri? ("http://example.org/gssl/person/" ++ toString i)

/-- Distinct RDF triples, plus a BNode join and a non-joinable quoted term.
    These terms exercise genuine SBM11 tags 1, 2, 3, 9 and their ranks. -/
private def makeGraph? (n : Nat) : Option (Graph × WfIri × WfIri × WfIri) := do
  let knows ← iri? "http://example.org/gssl/knows"
  let works ← iri? "http://example.org/gssl/worksOn"
  let atlas ← iri? "http://example.org/gssl/Atlas"
  let orion ← iri? "http://example.org/gssl/Orion"
  let label ← iri? "http://example.org/gssl/label"
  let grouped ← (List.range n).mapM (fun i => do
    let person ← person? i
    let friend1 ← person? ((i+1)%n)
    let friend7 ← person? ((i+7)%n)
    let project := if i%4==0 then atlas else orion
    return [
      {s := Subject.iri person, p := knows, o := Term.iri friend1},
      {s := Subject.iri person, p := knows, o := Term.iri friend7},
      {s := Subject.iri person, p := works, o := Term.iri project},
      {s := Subject.iri person, p := label,
       o := Term.literal (Literal.string ("Person " ++ toString i))}
    ])
  let a ← person? 0
  let b ← person? 1
  let extras : Graph := [
    {s := .iri a, p := knows, o := .bnode "scope-one"},
    {s := .bnode "scope-one", p := works, o := .iri atlas},
    {s := .iri b, p := knows,
     o := .tripleTerm (.bnode "embedded") works (.iri atlas)}
  ]
  return (grouped.flatten ++ extras, knows, works, atlas)

private def codeTriple? (keys : List Key) (t : Triple) :
    Option IdTriple := do
  let s ← toId? keys t.s.toTerm
  let p ← toId? keys (.iri t.p)
  let o ← toId? keys t.o
  return ⟨s.bits, p.bits, o.bits⟩

private def jsonArray (xs : List String) : String :=
  "[" ++ String.intercalate "," xs ++ "]"

/-- Term IDs and outputs are QUOTED decimal strings: JavaScript Number must
    never see the high bits (which carry SBM11 type tags). -/
private def j64 (v : UInt64) : String := "\"" ++ toString v.toNat ++ "\""

private def jTriple (t : IdTriple) : String :=
  jsonArray [j64 t.s, j64 t.p, j64 t.o]

private def jPair (p : UInt64 × UInt64) : String :=
  jsonArray [j64 p.1, j64 p.2]

private def fixture? (n : Nat) : Option String := do
  let (g,knows,works,atlas) ← makeGraph? n
  let keys ← keysOf? (g.flatMap fun t =>
    [t.s.toTerm, .iri t.p, t.o])
  if !keysOk keys then none else
    let rows ← g.mapM (codeTriple? keys)
    let kp ← toId? keys (.iri knows)
    let wp ← toId? keys (.iri works)
    let ap ← toId? keys (.iri atlas)
    let expected := bgpSpec kp.bits wp.bits ap.bits rows
    let name := "\"PackSpec SBM11 keys and toId? / " ++ toString n ++ " people\""
    some ("{" ++
      "\"kind\":\"sbm11-pack-spec\"," ++
      "\"name\":" ++ name ++ "," ++
      "\"people\":" ++ toString n ++ "," ++
      "\"dictionaryKeys\":" ++ toString keys.length ++ "," ++
      "\"triples\":" ++ jsonArray (rows.map jTriple) ++ "," ++
      "\"queryConstants\":{" ++
      "\"knows\":" ++ j64 kp.bits ++ "," ++
      "\"works\":" ++ j64 wp.bits ++ "," ++
      "\"atlas\":" ++ j64 ap.bits ++ "}," ++
      "\"expected\":" ++ jsonArray (expected.map jPair) ++
      "}")

def main : IO Unit := do
  for n in [8,64] do
    match fixture? n with
    | none => throw (IO.userError s!"SBM11 source fixture refused: {n}")
    | some encoded => IO.println encoded

end Harness.GsslSbm11SourceDevice

/-- Lean --run entrypoint; the namespaced main is kept for reuse. -/
def main : IO Unit := Harness.GsslSbm11SourceDevice.main
