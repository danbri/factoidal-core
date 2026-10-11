/- l4termwire-page-decode — time the PTD2 page decoder on one synthetic page.

   Usage: l4termwire-page-decode N R

   Builds one page of N IRI terms in term codec v2 (`TermWireV2`), then decodes
   it R times through `PTD.decodeTerms` at `PagedTermDictionaryV2.v2Format`,
   the function the IBK5 reader calls per page. Each repetition prepends one
   further term, so no two decodes have the same input. Prints the number of
   terms decoded; exit 1 when a decode is refused.

   This is the input of the `termwire-page-decode` row of
   tests/stack/lean_scaling.py: the decode of a page of 4N terms must cost
   about 4 times the decode of N terms. Before
   https://github.com/danbri/factoidal/issues/783 was repaired,
   `TermWireV2.parseInline` took its fuel from `List.length` of the rest of
   the page for every term, so the page decode was quadratic. -/
import L4Factoidal.Storage.PagedTermDictionaryV2

namespace Harness.TermWirePageDecode

open L4Factoidal.RDF
open L4Factoidal.Storage
open L4Factoidal.Storage.TermWireV2

private def termBytes (i : Nat) : List UInt8 :=
  let s := s!"http://example.org/term/{i}"
  if h : isIri s then PagedTermDictionaryV2.totalEncode (.inline (.iri ⟨s, h⟩))
  else []

/-- The page: the encodings of terms 0 .. n-1, built back to front so that
    each step is one `++` of a short list onto the page built so far. -/
private def pageGo : Nat → List UInt8 → List UInt8
  | 0, acc => acc
  | k + 1, acc => pageGo k (termBytes k ++ acc)

private def decodeLoop (page : List UInt8) (n : Nat) : Nat → Nat → Option Nat
  | 0, decoded => some decoded
  | r + 1, decoded =>
      match PTD.decodeTerms PagedTermDictionaryV2.v2Format (n + 1)
          (termBytes (n + r) ++ page) with
      | some (terms, []) => decodeLoop page n r (decoded + terms.length)
      | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | [nText, rText] =>
      match nText.toNat?, rText.toNat? with
      | some n, some r =>
          let page := pageGo n []
          match decodeLoop page n r 0 with
          | some decoded =>
              IO.println s!"l4termwire-page-decode terms={n} page-bytes={page.length} repetitions={r} decoded={decoded}"
              return 0
          | none => IO.eprintln "l4termwire-page-decode: a decode was refused"; return 1
      | _, _ => IO.eprintln "usage: l4termwire-page-decode N R"; return 2
  | _ => IO.eprintln "usage: l4termwire-page-decode N R"; return 2

end Harness.TermWirePageDecode

def main (args : List String) : IO UInt32 := Harness.TermWirePageDecode.main args
