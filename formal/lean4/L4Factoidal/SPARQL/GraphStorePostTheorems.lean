import L4Factoidal.SPARQL.GraphStoreService

namespace L4Factoidal.SPARQL.GraphStoreService

open L4Factoidal.RDF
open L4Factoidal.SPARQL.GraphStore

/-- Kind: payload parsing error propagation.
Says: sequencing part results can report only an error carried by a part, so a
lower bound on those part errors is inherited.
Does not say: which media types or parts the parser accepts. -/
private theorem mapM_error_ge {parts : List (Except Nat Graph)} {code : Nat}
    (h : parts.mapM id = .error code)
    (hpart : ∀ part ∈ parts, ∀ n, part = .error n → 400 ≤ n) :
    400 ≤ code := by
  induction parts with
  | nil => cases h
  | cons part rest ih =>
    rw [List.mapM_cons] at h
    cases part with
    | error why =>
      change Except.error why = Except.error code at h
      cases h
      exact hpart _ List.mem_cons_self _ rfl
    | ok graph =>
      change ((rest.mapM id).bind fun gs => .ok (graph :: gs)) = .error code at h
      cases hrest : rest.mapM id with
      | error why =>
        rw [hrest] at h
        cases h
        exact ih hrest (fun part hm => hpart part (List.mem_cons_of_mem _ hm))
      | ok graphs =>
        rw [hrest] at h
        cases h

/-- Kind: Graph Store payload status boundary.
Says: an error from the actual RDF payload parser, including a multipart
part error, cannot be returned as a success status.
Does not say: that an accepted RDF payload has any triples. -/
private theorem payloadGraph_error_ge {contentType base body : String} {code : Nat}
    (h : payloadGraph contentType base body = .error code) : 400 ≤ code := by
  simp only [payloadGraph] at h
  split at h
  · split at h
    · cases h
      decide
    · split at h
      · cases h
        decide
      · split at h
        · rename_i partCode hparts
          cases h
          apply mapM_error_ge hparts
          intro part hmem n herror
          obtain ⟨entry, _, rfl⟩ := List.mem_map.mp hmem
          rcases entry with ⟨part, ordinal⟩
          split at herror
          · cases herror
            decide
          · cases herror
            decide
          · cases herror
        · cases h
  · split at h
    · cases h
      decide
    · cases h
      decide
    · cases h

/-- Kind: named graph lookup invariant.
Says: replacing or inserting a named entry makes the target graph present,
even when the graph is empty.
Does not say: that the input list contained only one entry for the key. -/
private theorem lookupNamed_replaceNamed (key : GraphKey) (graph : Graph)
    (named : List (GraphKey × Graph)) :
    lookupNamed key (replaceNamed key graph named) = some graph := by
  induction named with
  | nil => simp [replaceNamed, lookupNamed]
  | cons entry rest ih =>
    rcases entry with ⟨k, prev⟩
    by_cases hk : k = key
    · simp [replaceNamed, lookupNamed, hk]
    · simp [replaceNamed, lookupNamed, hk, ih]

/-- Kind: named graph frame invariant.
Says: replacing or inserting a named entry preserves the exact subsequence of
entries with a different key.
Does not say: that those entries have unique names. -/
private theorem replaceNamed_filter_other (key : GraphKey) (graph : Graph)
    (named : List (GraphKey × Graph)) :
    (replaceNamed key graph named).filter (fun entry => entry.1 != key) =
      named.filter (fun entry => entry.1 != key) := by
  induction named with
  | nil => simp [replaceNamed]
  | cons entry rest ih =>
    rcases entry with ⟨k, prev⟩
    by_cases hk : k = key
    · simp [replaceNamed, hk]
    · simp [replaceNamed, hk, ih]

/-- Kind: HTTP handler and RDF graph membership correspondence (factoidal-core issue 631).
Says: a successful POST to a named graph uses the actual RDF payload parser,
preserves the default graph and the exact sequence of non-target entries,
and leaves the named graph present. Its RDF membership is the union of the
old graph and the payload renamed with the selected blank-node prefix.
Does not say: that this prefix is fresh across other graphs, that list
multiplicities are preserved in the target, or that the host persisted a write. -/
theorem serve_post_named_denotation (ep : Endpoint) (store : GraphStore)
    (method path qs : String) (headers : List (String × String)) (body : String)
    (key : GraphKey)
    (hm : Method.ofString method = some .post)
    (hr : resolve ep path qs = .ok (.graph (.named key)))
    (hs : (serve ep store method path qs headers body).2.status < 300) :
    let out := (serve ep store method path qs headers body).1
    let old := namedOrEmpty key store
    ∃ payload merged : Graph,
      payloadGraph ((headers.find? (fun kv => kv.1 == "content-type")).map (·.2) |>.getD "")
        (ep.iriOf path ++ (if qs.isEmpty then "" else "?" ++ qs)) body = .ok payload ∧
      out.default = store.default ∧
      out.named.filter (fun entry => entry.1 != key) =
        store.named.filter (fun entry => entry.1 != key) ∧
      get (.named key) out = some merged ∧
      ∀ t : Triple, Graph.mem t merged =
        (Graph.mem t old || Graph.mem t (prefixBnodes (freshPrefix "m" (Graph.bnodes old)) payload)) := by
  let contentType := ((headers.find? (fun kv => kv.1 == "content-type")).map (·.2)).getD ""
  let base := ep.iriOf path ++ (if qs.isEmpty then "" else "?" ++ qs)
  let parsed := payloadGraph contentType base body
  have hserve : serve ep store method path qs headers body =
      (match parsed with
      | .error code => (store, { status := code })
      | .ok payload =>
        ({ store with named := replaceNamed key (mergeInto (namedOrEmpty key store) payload) store.named },
          { status := if namedExists key store.named then 204 else 201 })) := by
    unfold parsed contentType base
    simp only [serve, hr, hm]
    rfl
  have hsuccess : ∃ payload : Graph, parsed = .ok payload := by
    cases hparse : parsed with
    | error code =>
      have hlarge :=
        payloadGraph_error_ge (contentType := contentType) (base := base) (body := body) hparse
      have hs' : code < 300 := by
        rw [hserve, hparse] at hs
        exact hs
      exact False.elim (Nat.not_lt_of_ge (Nat.le_trans (by decide : 300 ≤ 400) hlarge) hs')
    | ok payload => exact ⟨payload, rfl⟩
  obtain ⟨payload, hparse⟩ := hsuccess
  let merged := mergeInto (namedOrEmpty key store) payload
  have hout : (serve ep store method path qs headers body).1 =
      { store with named := replaceNamed key merged store.named } := by
    rw [hserve, hparse]
  dsimp only
  rw [hout]
  refine ⟨payload, merged, hparse, rfl, replaceNamed_filter_other _ _ _,
    lookupNamed_replaceNamed _ _ _, ?_⟩
  intro t
  exact mem_graph_union _ _ t

#print axioms serve_post_named_denotation

end L4Factoidal.SPARQL.GraphStoreService
