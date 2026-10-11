import L4Factoidal.Storage.PageCache
import Std.Data.HashMap.Lemmas

namespace L4Factoidal.Storage.PageCache

theorem lookup_insert (cache : Cache α) (page wanted : Nat) (value : α) :
    lookup (insert cache page value) wanted =
      if page == wanted then some value else lookup cache wanted := by
  simp only [lookup, insert, Std.HashMap.getElem?_insert]

theorem lookup_ofList (pages : List (Nat × α)) (wanted : Nat) :
    lookup (ofList pages) wanted = reference pages wanted := by
  induction pages with
  | nil => simp [lookup, ofList, reference]
  | cons pair rest ih =>
      simp only [ofList, List.foldr_cons, lookup_insert, reference]
      exact congrArg (fun later => if pair.1 == wanted then some pair.2 else later) ih

theorem term_ofList (pages : List (Nat × Array α)) (pageTerms termId : Nat) :
    term? (ofList pages) pageTerms termId = termFromList? pages pageTerms termId := by
  simp only [term?, lookup_ofList]
  induction pages with
  | nil => rfl
  | cons pair rest ih =>
      simp only [reference, termFromList?]
      rw [BEq.comm (a := termId / pageTerms) (b := pair.1)]
      split <;> simp_all

#print axioms lookup_ofList
#print axioms term_ofList

end L4Factoidal.Storage.PageCache
