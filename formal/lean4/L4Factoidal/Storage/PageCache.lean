/- Pure decoded-page lookup. Page numbers belong to one admitted artifact;
   callers own the cache lifetime and validate pages before insertion. -/
import Std.Data.HashMap

namespace L4Factoidal.Storage.PageCache

abbrev Cache (α : Type) := Std.HashMap Nat α

def lookup (cache : Cache α) (page : Nat) : Option α := cache[page]?

def insert (cache : Cache α) (page : Nat) (value : α) : Cache α := cache.insert page value

/-- Preserve the first occurrence, including for malformed duplicate keys. -/
def ofList (pages : List (Nat × α)) : Cache α :=
  pages.foldr (fun pair cache => insert cache pair.1 pair.2) ∅

def reference : List (Nat × α) → Nat → Option α
  | [], _ => none
  | (page, value) :: rest, wanted =>
      if page == wanted then some value else reference rest wanted

def term? (cache : Cache (Array α)) (pageTerms termId : Nat) : Option α := do
  let terms ← lookup cache (termId / pageTerms)
  terms[termId % pageTerms]?

def termFromList? : List (Nat × Array α) → Nat → Nat → Option α
  | [], _, _ => none
  | (page, terms) :: rest, pageTerms, termId =>
      if termId / pageTerms == page then terms[termId % pageTerms]?
      else termFromList? rest pageTerms termId

end L4Factoidal.Storage.PageCache
