/-
Namespace update agreement between the production XDM builder and XML.
The lexical admission premise is explicit; full QName admission and the
stateful buildNode preservation theorem remain separate obligations.
-/
import L4Factoidal.XPath4.OptionalTheorems

namespace L4Factoidal.XPath4.OptionalTheorems

open L4Factoidal.XPath4 L4Factoidal.XML

/-- Declaration recognition by the namespace-aware XML layer, before its
    reserved-name and version checks. -/
def xmlBinding (a : Attribute) : Option (String × String) :=
  match splitQName a.name with
  | .simple "xmlns" => some ("", a.value)
  | .prefixed "xmlns" p => some (p, a.value)
  | _ => none

/-- A local lexical condition, independently checkable for each attribute.
    It does not assert agreement of either scope update. -/
def LexicallyAgrees (attrs : List Attribute) : Prop :=
  ∀ a ∈ attrs, namespaceBinding a = xmlBinding a

private theorem namespaceScope_cons (scope : List (String × String))
    (a : Attribute) (rest : List Attribute) :
    namespaceScope scope (a :: rest) = namespaceScope
      (match namespaceBinding a with | some b => b :: scope | none => scope) rest := by
  unfold namespaceScope
  rw [List.foldl_cons]
  congr 1
  unfold namespaceBinding
  split
  · rfl
  · split <;> rfl

theorem namespaceScope_entries (scope : List (String × String))
    (attrs : List Attribute) :
    namespaceScope scope attrs = (attrs.filterMap namespaceBinding).reverse ++ scope := by
  induction attrs generalizing scope with
  | nil => rfl
  | cons a rest ih =>
    rw [namespaceScope_cons, ih]
    cases hb : namespaceBinding a <;> simp [hb, List.reverse_cons, List.append_assoc]

private theorem lookup_reverse_unique (entries : List (String × String))
    (hu : (entries.map Prod.fst).Nodup) (p : String) :
    entries.reverse.lookup p = entries.lookup p := by
  revert hu
  induction entries with
  | nil => intro _; rfl
  | cons b rest ih =>
    intro hu
    obtain ⟨q, u⟩ := b
    simp only [List.map_cons, List.nodup_cons] at hu
    have hn : rest.lookup q = none := by
      rw [List.lookup_eq_none_iff]
      intro b hb
      have hneq : q ≠ b.1 := by
        intro he
        exact hu.1 (List.mem_map.mpr ⟨b, hb, he.symm⟩)
      simpa using hneq
    rw [List.reverse_cons, List.lookup_append, ih hu.2]
    by_cases hp : p = q
    · subst p
      simp [hn]
    · have hp' : (p == q) = false := by simpa using hp
      simp [List.lookup_cons, hp']

/-- Successful XML declaration processing retains exactly the recognised
    declarations in source order, followed by the inherited scope. -/
theorem applyDeclarations_entries (version : String) (base out : NsScope)
    (attrs : List Attribute)
    (h : applyDeclarations version base attrs = some out) :
    convScope out = attrs.filterMap xmlBinding ++ convScope base := by
  induction attrs generalizing out with
  | nil => simp [applyDeclarations] at h; subst out; rfl
  | cons a rest ih =>
    cases hs : splitQName a.name with
    | malformed =>
      simp [applyDeclarations, hs] at h
      simpa [xmlBinding, hs] using ih out h
    | simple n =>
      by_cases hn : n = "xmlns"
      · subst n
        simp only [applyDeclarations, hs] at h
        split at h
        · cases h
        · cases hr : applyDeclarations version base rest with
          | none => simp [hr] at h
          | some tail =>
            simp only [hr, Option.map_some, Option.some.injEq] at h
            subst out
            have ht := ih tail hr
            simp only [convScope] at ht
            by_cases hv : a.value = ""
            · simp [hv, convScope, xmlBinding, hs, ht]
            · simp [hv, convScope, xmlBinding, hs, ht]
      · simp [applyDeclarations, hs, hn] at h
        simpa [xmlBinding, hs, hn] using ih out h
    | prefixed p localPart =>
      by_cases hp : p = "xmlns"
      · subst p
        simp only [applyDeclarations, hs] at h
        split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · cases h
            · split at h
              · cases h
              · split at h
                · cases h
                · cases hr : applyDeclarations version base rest with
                  | none => simp [hr] at h
                  | some tail =>
                    simp only [hr, Option.map_some, Option.some.injEq] at h
                    subst out
                    have ht := ih tail hr
                    simp only [convScope] at ht
                    by_cases hv : a.value = ""
                    · simp [hv, convScope, xmlBinding, hs, ht]
                    · simp [hv, convScope, xmlBinding, hs, ht]
      · simp [applyDeclarations, hs, hp] at h
        simpa [xmlBinding, hs, hp] using ih out h

/-- The actual production namespace fold agrees with successful XML
    namespace processing on lookups. Duplicate declaration prefixes and
    differences in declaration recognition are excluded explicitly. -/
theorem namespaceScope_lookup (version : String) (base out : NsScope)
    (attrs : List Attribute) (hlex : LexicallyAgrees attrs)
    (hunique : ((attrs.filterMap namespaceBinding).map Prod.fst).Nodup)
    (happly : applyDeclarations version base attrs = some out) (p : String) :
    (namespaceScope (convScope base) attrs).lookup p = (convScope out).lookup p := by
  have he : attrs.filterMap namespaceBinding = attrs.filterMap xmlBinding := by
    clear hunique happly
    revert hlex
    induction attrs with
    | nil => intro _; rfl
    | cons a rest ih =>
      intro hlex
      have ha := hlex a (by simp)
      have ht : LexicallyAgrees rest := fun b hb => hlex b (by simp [hb])
      simp only [List.filterMap_cons, ha, ih ht]
  rw [namespaceScope_entries, applyDeclarations_entries version base out attrs happly,
    List.lookup_append, List.lookup_append, lookup_reverse_unique _ hunique, he]

/-- Lookup agreement composes across inherited scopes; their list orders
    and their shadowed entries need not be equal. -/
theorem namespaceScope_lookup_of_inherited (version : String) (base out : NsScope)
    (inherited : List (String × String)) (attrs : List Attribute)
    (hbase : ∀ p, inherited.lookup p = (convScope base).lookup p)
    (hlex : LexicallyAgrees attrs)
    (hunique : ((attrs.filterMap namespaceBinding).map Prod.fst).Nodup)
    (happly : applyDeclarations version base attrs = some out) (p : String) :
    (namespaceScope inherited attrs).lookup p = (convScope out).lookup p := by
  calc
    (namespaceScope inherited attrs).lookup p =
        (namespaceScope (convScope base) attrs).lookup p := by
      rw [namespaceScope_entries, namespaceScope_entries,
        List.lookup_append, List.lookup_append, hbase]
    _ = (convScope out).lookup p := namespaceScope_lookup version base out attrs hlex hunique happly p

private theorem find_eq_lookup (sc : List (String × String)) (p : String) :
    sc.find? (·.1 == p) = (sc.lookup p).map (fun u => (p, u)) := by
  induction sc with
  | nil => rfl
  | cons b rest ih =>
    obtain ⟨q, u⟩ := b
    by_cases h : q = p
    · subst q; simp
    · have h' : p ≠ q := Ne.symm h
      have hpq : (p == q) = false := by simpa using h'
      simp [List.lookup_cons, h, hpq, ih]

/-- Namespace-node soundness needs lookup agreement, so declaration order
    does not become an unnecessary representation hypothesis. -/
theorem nsNodesOf_sound_lookup (r : NRec) (xs : NsScope) (hk : r.kind = .element)
    (hs : ∀ p, r.inscope.lookup p = (convScope xs).lookup p)
    (p u : String) (h : (p, u) ∈ nsNodesOf r) :
    (lookupPrefix xs p = some u ∧ u ≠ "") ∨ (p = "xml" ∧ u = nsXML) := by
  have hf : r.inscope.find? (·.1 == p) = (convScope xs).find? (·.1 == p) := by
    rw [find_eq_lookup, find_eq_lookup, hs]
  rw [nsNodesOf_eq r hk] at h
  simp only at h
  have core : (p, u) ∈ (((firstBinds r.inscope).filter (fun (_, u) => u != "")).take (nsSlot - 2)) →
      lookupPrefix xs p = some u ∧ u ≠ "" := by
    intro hm
    have hm := List.mem_of_mem_take hm
    rw [List.mem_filter] at hm
    obtain ⟨hm, hne⟩ := hm
    rw [firstBinds_mem, hf, find_convScope] at hm
    simp only [Option.map_eq_some_iff] at hm
    obtain ⟨b, hb, hbe⟩ := hm
    have hkey := find_key hb
    obtain ⟨bp, bu⟩ := b
    simp at hbe hkey
    subst hkey
    refine ⟨?_, by simpa using hne⟩
    unfold lookupPrefix
    rw [hb]
    cases bu with
    | none => simp at hbe; subst hbe; simp at hne
    | some v => simp at hbe; simp [hbe]
  split at h
  · exact Or.inl (core h)
  · rw [List.mem_append] at h
    rcases h with h | h
    · exact Or.inl (core h)
    · simp at h; exact Or.inr h

/-- Namespace-node completeness under lookup agreement. The slot bound
    concerns the actual builder scope, including inherited entries. -/
theorem nsNodesOf_complete_lookup (r : NRec) (xs : NsScope) (hk : r.kind = .element)
    (hs : ∀ p, r.inscope.lookup p = (convScope xs).lookup p)
    (hlen : r.inscope.length ≤ nsSlot - 2)
    (p u : String) (hl : lookupPrefix xs p = some u) (hne : u ≠ "") :
    (p, u) ∈ nsNodesOf r := by
  have hf : r.inscope.find? (·.1 == p) = (convScope xs).find? (·.1 == p) := by
    rw [find_eq_lookup, find_eq_lookup, hs]
  rw [nsNodesOf_eq r hk]
  simp only
  have hmem : (p, u) ∈ ((firstBinds r.inscope).filter (fun (_, u) => u != "")).take (nsSlot - 2) := by
    rw [List.take_of_length_le]
    · rw [List.mem_filter, firstBinds_mem, hf, find_convScope]
      unfold lookupPrefix at hl
      cases hb : xs.find? (·.1 == p) with
      | none => rw [hb] at hl; simp at hl
      | some b =>
        rw [hb] at hl
        have hkey := find_key hb
        obtain ⟨bp, bu⟩ := b
        simp at hl hkey
        subst hkey hl
        simp [hne]
    · refine Nat.le_trans (List.length_filter_le _ _) ?_
      have h2 := firstStep_foldl_length r.inscope []
      unfold firstBinds
      simp at h2
      omega
  split
  · exact hmem
  · exact List.mem_append_left _ hmem

/-- The extracted helper preserves the former builder fold definition. -/
theorem namespaceScope_eq_original (scope : List (String × String))
    (attrs : List Attribute) :
    namespaceScope scope attrs = attrs.foldl (fun sc a =>
      if a.name == "xmlns" then ("", a.value) :: sc
      else if a.name.startsWith "xmlns:" then ((splitName a.name).2, a.value) :: sc
      else sc) scope := by
  rfl

-- These inputs distinguish lexical admission, duplicate declarations,
-- XML-version checks, undeclarations, and the implicit xml binding.
#guard namespaceScope [] [⟨"xmlns:p", "first"⟩, ⟨"xmlns:p", "last"⟩] =
  [("p", "last"), ("p", "first")]
#guard applyDeclarations "1.0" [] [⟨"xmlns:p", "first"⟩, ⟨"xmlns:p", "last"⟩] =
  some [("p", some "first"), ("p", some "last")]
#guard namespaceBinding ⟨"xmlns:p:q", "urn:bad"⟩ != xmlBinding ⟨"xmlns:p:q", "urn:bad"⟩
#guard applyDeclarations "1.0" initialScope [⟨"xmlns:p", ""⟩] = none
#guard applyDeclarations "1.1" initialScope [⟨"xmlns:p", ""⟩] =
  some [("p", none), ("xml", some xmlNsUri)]
#guard namespaceScope [("xml", nsXML)] [⟨"xmlns", ""⟩] = [("", ""), ("xml", nsXML)]
#guard applyDeclarations "1.0" initialScope [⟨"xmlns:xml", "urn:bad"⟩] = none

#print axioms nsNodesOf_sound_lookup
#print axioms nsNodesOf_complete_lookup
#print axioms namespaceScope_lookup
#print axioms namespaceScope_eq_original

end L4Factoidal.XPath4.OptionalTheorems
