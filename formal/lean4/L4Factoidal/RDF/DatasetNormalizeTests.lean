/-
L4Factoidal.RDF.DatasetNormalizeTests — executable checks of
`RDF/DatasetNormalize.lean`, evaluated during `lake build`.

The theorem `parseNQuadsFast_toCanonicalNQuads` covers every dataset the
check `roundTripSafe` accepts. These guards check that the check is not
vacuous (it accepts the shapes real data has: repeated triples, upper-case
tags, named graphs with one name twice, blank nodes, escaped characters,
RDF 1.2 triple terms and base directions), that it refuses the shapes the
theorem does not cover, that `datasetForOps` agrees with the text round trip
on both kinds, and that the normalisation changes what RDF 1.1 Concepts §3
and §3.3 say it changes (a function that returned its input would fail
here). No executable imports this module.
-/
import L4Factoidal.RDF.DatasetNormalize
import L4Factoidal.Syntax.Turtle
import L4Factoidal.Syntax.TriG

namespace L4Factoidal.RDF.DatasetNormalizeTests

open L4Factoidal.RDF
open L4Factoidal.Syntax

private def ttl (s : String) (mode : Mode := .rdf12) : Dataset :=
  match parseTurtle s none mode with
  | .ok g => { default := g, named := [] }
  | .error _ => Dataset.empty

private def trig (s : String) : Dataset :=
  match parseTriG s none .rdf12 with
  | .ok ds => ds
  | .error _ => Dataset.empty

/-- The text round trip, for comparison. -/
private def viaText (mode : Mode) (ds : Dataset) : Option Dataset :=
  (parseNQuadsFast (Dataset.toCanonicalNQuads ds) mode).toOption

private def quadCount (ds : Dataset) : Nat :=
  ds.default.length + (ds.named.map (·.graph.length)).foldl (· + ·) 0

/-- Issue 724's example: one triple written twice, and a tag in upper case. -/
private def dsRepeat : Dataset :=
  ttl "@prefix e: <http://e/> .\ne:a e:p e:b .\ne:a e:p e:b .\ne:a e:q \"x\"@EN ."

/-- Escapes, a typed literal, blank nodes, a label with a dot inside. -/
private def dsMixed : Dataset :=
  ttl ("@prefix e: <http://e/> .\n" ++
    "e:a e:p \"line\\none \\\"q\\\" tab\\t back\\\\ cr\\r\" .\n" ++
    "e:a e:p \"5\"^^<http://www.w3.org/2001/XMLSchema#integer> .\n" ++
    "_:x.y e:p [ e:q \"z\"@en-GB ] .\n" ++
    "e:a e:r \"plain\" .")

/-- Named graphs: one name used twice, a blank-node name, a repeated triple in
a graph, and the same triple in the default graph. Built directly, because the
TriG reader already keeps one copy of each quad and one entry per name. -/
private def dsGraphs : Dataset :=
  let g := trig ("@prefix e: <http://e/> .\n" ++
    "e:g1 { e:a e:p e:b . e:c e:p e:d . }\n" ++
    "_:g { e:a e:p \"v\"@DE }")
  match g.named with
  | [g1, gb] =>
      match g1.graph with
      | [t1, t2] =>
          { default := [t1],
            named := [{ g1 with graph := [t1, t1] }, gb, { g1 with graph := [t2, t1] }] }
      | _ => Dataset.empty
  | _ => Dataset.empty

/-- RDF 1.2: a nested triple term and a base direction. -/
private def ds12 : Dataset :=
  ttl ("@prefix e: <http://e/> .\n" ++
    "e:a e:p <<( e:s e:p <<( _:b e:q \"in\"@FR--rtl )>> )>> .\n" ++
    "e:a e:p \"txt\"@en--ltr .")

-- The fixtures parsed (a parse failure would make every guard below vacuous).
#guard quadCount dsRepeat == 3
#guard quadCount dsMixed == 5
#guard quadCount dsGraphs == 6 && dsGraphs.named.length == 3
#guard quadCount ds12 == 2

-- The check accepts them, in both modes where the 1.1 grammar has the syntax.
#guard roundTripSafe .rdf12 dsRepeat && roundTripSafe .rdf11 dsRepeat
#guard roundTripSafe .rdf12 dsMixed && roundTripSafe .rdf11 dsMixed
#guard roundTripSafe .rdf12 dsGraphs && roundTripSafe .rdf11 dsGraphs
#guard roundTripSafe .rdf12 ds12
-- RDF 1.1 has no triple terms and no base direction.
#guard !roundTripSafe .rdf11 ds12

-- The theorem's equation, run: the normalised dataset is the text round trip.
#guard viaText .rdf12 dsRepeat == some (normalizeDataset dsRepeat)
#guard viaText .rdf11 dsRepeat == some (normalizeDataset dsRepeat)
#guard viaText .rdf12 dsMixed == some (normalizeDataset dsMixed)
#guard viaText .rdf11 dsMixed == some (normalizeDataset dsMixed)
#guard viaText .rdf12 dsGraphs == some (normalizeDataset dsGraphs)
#guard viaText .rdf12 ds12 == some (normalizeDataset ds12)

-- Teeth: the normalisation is not the identity. RDF 1.1 Concepts §3: the
-- repeated triple is one triple; §3.3: the tag is lower case.
#guard quadCount (normalizeDataset dsRepeat) == 2
#guard normalizeDataset dsRepeat != dsRepeat
#guard (normalizeDataset dsRepeat).default.any fun t =>
  match t.o with
  | .literal l => l.val.langTag == some "en"
  | _ => false
#guard !(normalizeDataset dsRepeat).default.any fun t =>
  match t.o with
  | .literal l => l.val.langTag == some "EN"
  | _ => false
-- Graphs of one name merge, and each graph keeps one copy of a triple.
#guard (normalizeDataset dsGraphs).named.length == 2
#guard quadCount (normalizeDataset dsGraphs) == 4
-- A dataset that is already normal is returned unchanged.
#guard normalizeDataset (normalizeDataset dsGraphs) == normalizeDataset dsGraphs
#guard normalizeDataset Dataset.empty == Dataset.empty

/-! ### What the check refuses, and `datasetForOps` there

Each of these falls back to the text round trip, so `datasetForOps` still
answers what the round trip answers. -/

private def iriW (s : String) : WfIri :=
  if h : isIri s then ⟨s, h⟩ else ⟨"x:y", rfl⟩

private def one (s : Subject) (p : String) (o : Term) : Dataset :=
  { default := [{ s := s, p := iriW p, o := o }], named := [] }

/-- An IRI with a space: `RDF.isIri` admits it, IRIREF does not. -/
private def dsIriSpace : Dataset := one (.iri (iriW "http://e/a b")) "http://e/p" (.iri (iriW "http://e/o"))
/-- A blank-node label that ends on a dot. -/
private def dsLabelDot : Dataset := one (.bnode "b.") "http://e/p" (.iri (iriW "http://e/o"))
/-- A lexical form with U+0001, which the canonical form writes as `\u0001`. -/
private def dsControl : Dataset :=
  one (.iri (iriW "http://e/a")) "http://e/p" (.literal (Literal.string (String.singleton (Char.ofNat 1))))
/-- A language tag with an empty subtag. -/
private def dsBadTag : Dataset :=
  one (.iri (iriW "http://e/a")) "http://e/p" (.literal (Literal.langString "x" "en--x"))

#guard !roundTripSafe .rdf12 dsIriSpace
#guard !roundTripSafe .rdf12 dsLabelDot
#guard !roundTripSafe .rdf12 dsControl
#guard !roundTripSafe .rdf12 dsBadTag
#guard ((datasetForOps .rdf12 dsIriSpace).toOption) == viaText .rdf12 dsIriSpace
#guard ((datasetForOps .rdf12 dsLabelDot).toOption) == viaText .rdf12 dsLabelDot
#guard ((datasetForOps .rdf12 dsControl).toOption) == viaText .rdf12 dsControl
#guard ((datasetForOps .rdf12 dsBadTag).toOption) == viaText .rdf12 dsBadTag
#guard ((datasetForOps .rdf11 ds12).toOption) == viaText .rdf11 ds12
-- The fallback is reached: the IRI with a space does not survive the text.
#guard viaText .rdf12 dsIriSpace == none
#guard (datasetForOps .rdf12 dsIriSpace).toOption == none
-- And on the accepted shapes `datasetForOps` is the normalisation.
#guard (datasetForOps .rdf12 dsRepeat).toOption == some (normalizeDataset dsRepeat)

/-! ### `datasetForOps12Or11` and `parseNQuadsFast12Or11`
(https://github.com/danbri/factoidal/issues/870)

The operations that take N-Quads text read it as RDF 1.2 and, when that reader
refuses it, as RDF 1.1. -/

-- Triple terms and a base direction: the RDF 1.1 text round trip fails, and the answer
-- is the normalisation (the RDF 1.2 check passes, so there is no text round trip).
#guard (viaText .rdf11 ds12).isNone
#guard (datasetForOps12Or11 ds12).toOption == some (normalizeDataset ds12)
#guard (datasetForOps12Or11 ds12).toOption == viaText .rdf12 ds12
-- A dataset that passes the RDF 1.1 check gets what `datasetForOps .rdf11` gave.
#guard (datasetForOps12Or11 dsRepeat).toOption == (datasetForOps .rdf11 dsRepeat).toOption
#guard (datasetForOps12Or11 dsMixed).toOption == (datasetForOps .rdf11 dsMixed).toOption
#guard (datasetForOps12Or11 dsGraphs).toOption == (datasetForOps .rdf11 dsGraphs).toOption
-- A language tag with a subtag of 11 characters: the RDF 1.2 reader refuses the
-- text, the RDF 1.1 reader reads it, and the second reader is reached.
private def dsLongTag : Dataset :=
  one (.iri (iriW "http://e/a")) "http://e/p" (.literal (Literal.langString "x" "abcdefghijk"))
#guard !roundTripSafe .rdf12 dsLongTag
#guard (datasetForOps .rdf12 dsLongTag).toOption.isNone
#guard (datasetForOps12Or11 dsLongTag).toOption.isSome
#guard (datasetForOps12Or11 dsLongTag).toOption == viaText .rdf11 dsLongTag
-- Both readers refuse an IRI with a space: the error is the RDF 1.1 reader's.
#guard (match datasetForOps12Or11 dsIriSpace, datasetForOps .rdf11 dsIriSpace with
        | .error a, .error b => a == b
        | _, _ => false)
-- The text readers: the same three cases.
#guard (parseNQuadsFast12Or11 (Dataset.toCanonicalNQuads ds12)).toOption == some (normalizeDataset ds12)
#guard (parseNQuadsFast12Or11 (Dataset.toCanonicalNQuads dsLongTag)).toOption ==
  (parseNQuadsFast (Dataset.toCanonicalNQuads dsLongTag) .rdf11).toOption
#guard (match parseNQuadsFast12Or11 "<http://e/a> <http://e/p> .\n",
              parseNQuadsFast "<http://e/a> <http://e/p> .\n" .rdf11 with
        | .error a, .error b => a == b
        | _, _ => false)

/-! ### `iriPrintSafe` through `String.all`

`DatasetNormalize.lean` registers `iriPrintSafe = iriPrintSafeFast` as
`csimp`; the list form below is not rewritten, so these guards compare two
programs. -/

private def iriSamples : List String :=
  [ "", "http://e/a", "http://e/a b", "http://e/<x>", "http://e/\\", "http://é/ü",
    "urn:x" ++ String.singleton (Char.ofNat 0x10000), "a" ++ String.singleton (Char.ofNat 0x1F),
    "x{y}", "x|y", "x^y", "x`y", "x\"y" ]

#guard iriSamples.all fun s => NTriplesRoundTrip.iriPrintSafe s == s.toList.all NTriplesRoundTrip.IriSafeChar
#guard (iriSamples.filter NTriplesRoundTrip.iriPrintSafe).length == 4
#guard (iriSamples.filter (fun s => !NTriplesRoundTrip.iriPrintSafe s)).length == 9

/-! ### Axiom audit -/

#print axioms parseNQuadsFast_toCanonicalNQuads
#print axioms datasetForOps_eq
#print axioms parseNQuadsFast12Or11_of_rdf12
#print axioms parseNQuadsFast12Or11_of_not_rdf12
#print axioms parseNQuadsFast12Or11_accepts_rdf11
#print axioms parseNQuadsFast12Or11_error
#print axioms datasetForOps12Or11_eq
#print axioms roundTripSafe_rdf11_rdf12
#print axioms datasetForOps12Or11_of_safe11

end L4Factoidal.RDF.DatasetNormalizeTests
