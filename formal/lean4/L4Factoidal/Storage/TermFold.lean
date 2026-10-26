/-
L4Factoidal.Storage.TermFold — one term equality for the term dictionaries
of every store (https://github.com/danbri/factoidal/issues/977; issue 975
phase B4).

RDF 1.2 Concepts section 3.4 says that language tags are compared "using
ASCII case-insensitive matching", and RDF 1.1 Concepts section 3.3 permits an
implementation to lower-case the tag. `Term.eqb` (the engine's term equality)
compares tags without case. A dictionary whose ids are per structural term
gives `"x"@en` and `"x"@EN` two ids, so a graph in that store can hold two
triples that `Triple.eqb` makes one.

The fold is the SBM11 normalisation `Sbm11.normalizeTerm` (every language
tag in lower case, inside triple terms too), reused here and not written a
second time. A dictionary holds only folded terms (`termFolded`); a builder
folds a term before it gives it an id; a lookup folds the wanted term first;
a decoder folds what it reads from a file written before the fold (or refuses
the file where the fold would merge two entries). On folded terms structural
equality is `Term.eqb` (`TermFoldTheorems.normalizeTerm_eq_iff_eqb`), so the
structural dictionaries then give one id per RDF term.

No `sorry`, no user `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Storage.Sbm11.TermKey

namespace L4Factoidal.Storage.TermFold

open L4Factoidal.RDF

/-- The fold of a term: `Sbm11.normalizeTerm`. -/
abbrev foldTerm (t : Term) : Term := Sbm11.normalizeTerm t

/-- `t` is its own fold: every language tag in it is in lower case. -/
def termFolded (t : Term) : Bool := foldTerm t == t

/-- Every term of a dictionary array is folded. -/
def dictFolded (dict : Array Term) : Bool := dict.all termFolded

/-- The fold of a triple. A subject and a predicate hold no literal, so only
    the object changes. -/
def foldTriple (t : Triple) : Triple := { t with o := foldTerm t.o }

/-- The fold of a quad. A graph name holds no literal. -/
def foldQuad (q : Option Subject × Triple) : Option Subject × Triple := (q.1, foldTriple q.2)

end L4Factoidal.Storage.TermFold
