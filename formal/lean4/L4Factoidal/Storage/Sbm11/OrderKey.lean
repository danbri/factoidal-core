/-
L4Factoidal.Storage.Sbm11.OrderKey — ORDER BY on dictionary ids for blank
nodes, IRIs, `xsd:string` literals and language-tagged literals (stage 1l of
docs/designissues/2026-10-12-parallel-block-scans.md;
https://github.com/danbri/factoidal/issues/961).

SPARQL 1.1 section 15.1 and the engine's `sparqlOrderValue` put an unbound
variable first, then blank nodes, then IRIs, then literals. The engine orders
two literals by datatype IRI, then lexical form, then language tag
(`literalOrder`); `rdf:langString` is below `xsd:string` in code point order
of the datatype IRIs.

The dictionary is sorted by unsigned byte order of the keys
(`TermKey`): class 1 blank node label, class 2 IRI, class 3 `xsd:string`
lexical form, class 4 lexical form, `0x00`, language tag. `keyGroup?` gives
the ORDER BY group of a key:

| Group | Key |
|---:|---|
| 1 | class 1 (blank node) |
| 2 | class 2 (IRI) |
| 3 | class 4 (`rdf:langString`) whose body holds exactly one `0x00` |
| 4 | class 3 (`xsd:string`) |

and `none` for every other key: a class 4 key whose lexical form holds a
`0x00` (then `lexical form, 0x00, tag` is not ordered as the pair), and the
classes 5, 6 and 7, whose order goes through datatype values.

`OrderKeyTheorems.orderValue_keyOrder`: for two terms with keys in groups
`g₁` and `g₂`, `sparqlOrderValue` of their ORDER BY values is the order of
`g₁` and `g₂`, and for one group the unsigned byte order of the keys
(`bytesCmp`). Its premises are the keys and the groups; none states an order.
The byte order of UTF-8 is the code point order of `strCompare`
(`OrderKeyTheorems.bytesCmp_utf8`).

`keyGroupSlice?` is `keyGroup?` read from a range of a byte array
(`OrderKeyTheorems.keyGroupSlice?_eq`), a loop over the bytes of the key.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TermKeyFast

namespace L4Factoidal.Storage.Sbm11.OrderKey

open L4Factoidal.Storage.Sbm11

/-- Unsigned byte order of two byte lists, as `-1`, `0`, `1`; a proper prefix
    comes first. -/
def bytesCmp : List UInt8 → List UInt8 → Int
  | [], [] => 0
  | [], _ :: _ => -1
  | _ :: _, [] => 1
  | a :: as, b :: bs => if a < b then -1 else if b < a then 1 else bytesCmp as bs

/-- The number of `0x00` bytes of a list. -/
def zeros (bs : List UInt8) : Nat := bs.countP (· == 0)

/-- The ORDER BY group of a dictionary key (module header). -/
def keyGroup? : List UInt8 → Option Nat
  | c :: body =>
    if c == classBnode then some 1
    else if c == classIri then some 2
    else if c == classLang then (if zeros body == 1 then some 3 else none)
    else if c == classString then some 4
    else none
  | [] => none

/-- `acc` plus the number of `0x00` bytes of `buf[i, e)` (fuel `f`; a tail
    call per byte). -/
def zerosGo (buf : ByteArray) (e : Nat) : Nat → Nat → Nat → Nat
  | 0, _, acc => acc
  | f + 1, i, acc =>
    if e ≤ i then acc
    else zerosGo buf e f (i + 1) (if buf.get! i == 0 then acc + 1 else acc)

/-- `keyGroup?` of the key `buf[a, e)`, read in place. -/
def keyGroupSlice? (buf : ByteArray) (a e : Nat) : Option Nat :=
  if sliceOk buf a e then
    let c := buf.get! a
    if c == classBnode then some 1
    else if c == classIri then some 2
    else if c == classLang then
      (if zerosGo buf e (e - (a + 1)) (a + 1) 0 == 1 then some 3 else none)
    else if c == classString then some 4
    else none
  else keyGroup? (sliceList buf a e)

end L4Factoidal.Storage.Sbm11.OrderKey
