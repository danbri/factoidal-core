/-
L4Factoidal.JSONLD.Theorems — proved properties of the JSON-LD port.

Every theorem here is proved outright: no `sorry`, no user `axiom`, no
`native_decide`, no `partial`. `Tests.lean`'s companion audit lines and
the `#print axioms` block at the end of this file show the trusted base
is exactly Lean's own (`propext`, `Classical.choice`, `Quot.sound`).

Scope is deliberately the CHEAP end of the ladder: identities and
invariants of §5.2.2 IRI Expansion, §4.2 Create Term Definition, and the
blank-node issuer, plus the one property the `jsonld-context-cache`
skill singles out as a rule with teeth — that an unresolvable remote
context yields an ERROR, never an empty context. Nothing here claims
conformance; that is what the toRdf probe measures.
-/
import L4Factoidal.JSONLD.ToRdf
import L4Factoidal.RDF.CanonicalTheorems

namespace L4Factoidal.JSONLD

open L4Factoidal.JSON

/-! ## §5.2.2 IRI Expansion -/

/-- **A keyword expands to itself.** JSON-LD 1.1 API §5.2.2 step 2: "If
value is a keyword … return value as is". Holds in both `vocab` modes
and under both the expansion-time and context-processing entry points,
because the keyword test precedes every term and prefix lookup. -/
theorem expandIri_keyword (ac : ActiveContext) (v : String) (vocab inCtx : Bool)
    (hne : (slen v == 0) = false) (hkw : actualKeyword v = true) :
    expandIriGen ac v vocab inCtx = some v := by
  unfold expandIriGen
  simp [hne, hkw]

/-- **A term defined as a keyword alias expands to that keyword.**
JSON-LD 1.1 API §5.2.2 step 4 ("if active context has a term definition
for value, return the associated IRI mapping") composed with §4.2's
storage of an aliased keyword as the term's IRI mapping. Vocab-relative
only, which is exactly the spec's condition. -/
theorem expandIri_keyword_alias (ac : ActiveContext) (t kw : String) (inCtx : Bool)
    (td : TermDef)
    (hne : (slen t == 0) = false) (hkw : actualKeyword t = false)
    (hfind : findTerm ac.terms t = some td) (hiri : td.iri = kw) :
    expandIriGen ac t true inCtx = some kw := by
  unfold expandIriGen
  simp [hne, hkw, hfind, hiri]

/-- **An absolute IRI with an authority component is the identity.**
JSON-LD 1.1 API §5.2.2's compact-IRI step returns `value` unchanged once
the prefix is not a term ("if … the prefix is not a term in the active
context, return value as is"); the `//` after the scheme colon is what
makes it an ordinary absolute IRI rather than a compact one. Stated with
the guards the algorithm itself checks, in the order it checks them. -/
theorem expandIri_absolute_authority (ac : ActiveContext) (v : String)
    (vocab inCtx : Bool) (c : Nat)
    (hne : (slen v == 0) = false)
    (hkw : actualKeyword v = false)
    (hterm : (if vocab then findTerm ac.terms v else none) = none)
    (hform : keywordForm v = false)
    (hc : findColon v = some c) (hc0 : (c == 0) = false)
    (hpre : (substr v 0 c == "_") = false)
    (hsch : (v.toList.take c).all isSchemeChar = true)
    (hs1 : charAtD v (c + 1) = '/') (hs2 : charAtD v (c + 2) = '/') :
    expandIriGen ac v vocab inCtx = some v := by
  have hsub : (substr v 0 c).toList = v.toList.take c := by
    simp [substr]
  unfold expandIriGen
  simp only [hne, hkw, hform, hc, hc0, hpre, hs1, hs2]
  simp [hterm, hsub, hsch]

/-- **With no `@vocab` and no `@base`, nothing relative resolves.** The
fallback of §5.2.2 (steps 5 and 6) has nothing to concatenate onto or
resolve against. -/
theorem expandFallback_none (ac : ActiveContext) (value : String) (vocab : Bool)
    (hv : ac.vocab = none) (hb : ac.base = none) :
    expandFallback ac value vocab = none := by
  unfold expandFallback
  cases vocab <;> simp [hv, hb]

/-! ## §4.2 Create Term Definition -/

/-- **Definition compatibility is reflexive.** A term redefined by an
IDENTICAL definition is always the same definition, which is what makes
§4.2's protected-term rule admit a repeated declaration. -/
theorem termDefsCompatible_refl (a : TermDef) : termDefsCompatible a a = true := by
  simp [termDefsCompatible]

/-- **A protected term redefined identically keeps its OLD definition.**
JSON-LD 1.1 API §4.2: "Set definition to previous definition to retain
the value of protected". This is what stops a later, still-compatible
redefinition that omits `@protected` from silently unprotecting the
term. -/
theorem resolveRedefine_protected_identical (ac : ActiveContext) (key : String)
    (existing : TermDef) (hfind : findTerm ac.terms key = some existing)
    (hprot : existing.protected_ = true) :
    resolveRedefine ac key existing false = .ok existing := by
  simp [resolveRedefine, hfind, hprot, termDefsCompatible_refl]

/-- **A protected term redefined DIFFERENTLY is the named error.** Same
step of §4.2, the failing branch — and the error carries its code, which
the F* source's bare `option` cannot. -/
theorem resolveRedefine_protected_incompatible (ac : ActiveContext) (key : String)
    (existing newTd : TermDef) (hfind : findTerm ac.terms key = some existing)
    (hprot : existing.protected_ = true)
    (hincompat : termDefsCompatible existing newTd = false) :
    resolveRedefine ac key newTd false = .error .protectedTermRedefinition := by
  simp [resolveRedefine, hfind, hprot, hincompat]

/-- **An undefined term is defined by the new definition.** The ordinary
"later wins" rule of §4.2, with nothing to protect. -/
theorem resolveRedefine_fresh (ac : ActiveContext) (key : String) (newTd : TermDef)
    (over : Bool) (hfind : findTerm ac.terms key = none) :
    resolveRedefine ac key newTd over = .ok newTd := by
  simp [resolveRedefine, hfind]

/-- **`override protected` always admits the new definition.** The right
of a property-scoped context (§5.1) to replace a protected term. -/
theorem resolveRedefine_override (ac : ActiveContext) (key : String) (newTd : TermDef) :
    ∃ r, resolveRedefine ac key newTd true = .ok r := by
  unfold resolveRedefine
  cases h : findTerm ac.terms key with
  | none => exact ⟨newTd, rfl⟩
  | some existing => simp

/-- **Removing a term makes it unfindable.** The `defined[term] = false`
guard of §4.2 is implemented by stripping the entry before expanding the
term's own `@id`; this is what makes that strip effective. -/
theorem findTerm_removeTerm (terms : List (String × TermDef)) (name : String) :
    findTerm (removeTerm terms name) name = none := by
  unfold findTerm removeTerm
  cases h : (terms.filter (fun kv => kv.1 != name)).find? (fun kv => kv.1 == name) with
  | none => rfl
  | some kv =>
      exfalso
      -- The entry `find?` returned satisfies BOTH the `find?` predicate
      -- (its key IS `name`) and the `filter` predicate it survived (its
      -- key is NOT `name`).
      have hmem := List.find?_some h
      have hin := List.mem_of_find?_eq_some h
      rw [List.mem_filter] at hin
      have hne := hin.2
      simp only [beq_iff_eq] at hmem
      simp only [bne_iff_ne, ne_eq, hmem, not_true_eq_false] at hne

/-! ## The active context's pop chain

The F* source spells the pop target as a self-referential
`ac_previous : option active_context` field; this port uses an explicit
stack (Lean structures are not recursive). These three theorems are what
make the two representations agree. -/

/-- **A context with no pop target pops to itself** — the F* `None`
case of `match ac.ac_previous with Some prev -> prev | None -> ac`. -/
theorem pop_no_prev (ac : ActiveContext) (h : ac.prev = []) : ac.pop = ac := by
  unfold ActiveContext.pop
  rw [h]

/-- **Popping after `setPrev` lands exactly on the target.** The F*
`Some prev` case: `{ ac with ac_previous = Some target }` then popping
yields `target`. -/
theorem pop_setPrev (ac target : ActiveContext) : (ac.setPrev target).pop = target := by
  unfold ActiveContext.setPrev ActiveContext.pop
  rfl

/-- **`clearPrev` removes the pop target**, so the result pops to
itself — the F* `{ ac with ac_previous = None }`. -/
theorem pop_clearPrev (ac : ActiveContext) : ac.clearPrev.pop = ac.clearPrev := by
  unfold ActiveContext.clearPrev ActiveContext.pop
  rfl

/-! ## The blank-node issuer — §8.2 "generate blank node identifier" -/

/-- **The issuer's counter strictly increases.** -/
theorem freshBnode_counter (pfx : String) (ctr : Nat) : (freshBnode pfx ctr).2 = ctr + 1 := rfl

/-- **The issuer is injective.** Two different counter values never
produce the same blank node identifier under one prefix, so the labels §8.2
mints for distinct nodes of one document are distinct. Reuses
`RDF.Canonical.mkLabel_inj` — this port builds its labels with the very
function RDFC-1.0 canonicalization already proved injective, rather than a
parallel one. -/
theorem freshBnode_injective {pfx : String} {m n : Nat}
    (h : (freshBnode pfx m).1 = (freshBnode pfx n).1) : m = n :=
  L4Factoidal.RDF.Canonical.mkLabel_inj h

/-- Contrapositive, in the form a reader wants: distinct counters give
distinct labels. -/
theorem freshBnode_distinct {pfx : String} {m n : Nat} (h : m ≠ n) :
    (freshBnode pfx m).1 ≠ (freshBnode pfx n).1 :=
  fun heq => h (freshBnode_injective heq)

/-! ## A generated blank node label is never a label that the document writes

A document that writes the blank node identifier `_:_jld_anon0` and also holds
a node object with no `@id` used to get one node where it has two: the
conversion minted the label `_jld_anon0` for the second
(https://github.com/danbri/factoidal/issues/840). The conversion passes the
labels that a document writes through unchanged, so the labels it mints must
not be able to equal them. `generatedPrefix root` is `_jld_anon`, followed by
the fewest underscores for which no string of `root` is `_:` and a label that
begins with the prefix. The theorem below is the claim for every string of the
document, for every counter value.

The labels that the conversion reads from a document are the ones that the two
functions `idToSubject` (the `@id` of a node object and of a graph) and
`typeTerm` (a blank node identifier in `@type`) read; both give
`stripBnodePrefix s` for a string `s` with `isBnodeLabel s`
(`idToSubject_bnode`, `typeTerm_bnode`). Every other blank node of the
conversion comes from `freshBnode` (a node object with no `@id`, a list cell,
a compound literal). That the conversion calls no other function to make a
blank node is a fact about the source of `JSONLD/ToRdf.lean`, and the guards in
`JSONLD/Tests.lean` (five distinct nodes in `bnode_collide.jsonld`, a list cell,
a blank node type and a compound literal beside a label that a generated one
used to equal) check it. -/

mutual
/-- `s` is a key or a string value somewhere in the JSON tree. -/
def jsonHasString : Json → String → Prop
  | .string t, s => s = t
  | .array xs, s => jsonHasStringItems xs s
  | .object fs, s => jsonHasStringFields fs s
  | _, _ => False

def jsonHasStringItems : List Json → String → Prop
  | [], _ => False
  | x :: xs, s => jsonHasString x s ∨ jsonHasStringItems xs s

def jsonHasStringFields : List (String × Json) → String → Prop
  | [], _ => False
  | (k, v) :: fs, s => s = k ∨ jsonHasString v s ∨ jsonHasStringFields fs s
end

mutual
/-- The accumulator of `maxNeed` never goes down. -/
theorem le_maxNeed : ∀ (j : Json) (m : Nat), m ≤ maxNeed j m
  | .null, _ => Nat.le_refl _
  | .bool _, _ => Nat.le_refl _
  | .number _, _ => Nat.le_refl _
  | .string s, m => by
      show m ≤ max m (anonNeed s)
      exact Nat.le_max_left _ _
  | .array xs, m => by simpa [maxNeed] using le_maxNeedItems xs m
  | .object fs, m => by simpa [maxNeed] using le_maxNeedFields fs m

theorem le_maxNeedItems : ∀ (xs : List Json) (m : Nat), m ≤ maxNeedItems xs m
  | [], _ => Nat.le_refl _
  | x :: xs, m => Nat.le_trans (le_maxNeed x m) (le_maxNeedItems xs (maxNeed x m))

theorem le_maxNeedFields : ∀ (fs : List (String × Json)) (m : Nat), m ≤ maxNeedFields fs m
  | [], _ => Nat.le_refl _
  | (k, v) :: fs, m =>
    Nat.le_trans (Nat.le_max_left m (anonNeed k))
      (Nat.le_trans (le_maxNeed v (max m (anonNeed k)))
        (le_maxNeedFields fs (maxNeed v (max m (anonNeed k)))))
end

mutual
/-- **Every string of the tree is at most the maximum.** -/
theorem need_le_maxNeed : ∀ (j : Json) (m : Nat) (s : String),
    jsonHasString j s → anonNeed s ≤ maxNeed j m
  | .null, _, _, h => h.elim
  | .bool _, _, _, h => h.elim
  | .number _, _, _, h => h.elim
  | .string t, m, s, h => by
      simp only [jsonHasString] at h
      subst h
      show anonNeed s ≤ max m (anonNeed s)
      exact Nat.le_max_right _ _
  | .array xs, m, s, h => need_le_maxNeedItems xs m s h
  | .object fs, m, s, h => need_le_maxNeedFields fs m s h

theorem need_le_maxNeedItems : ∀ (xs : List Json) (m : Nat) (s : String),
    jsonHasStringItems xs s → anonNeed s ≤ maxNeedItems xs m
  | [], _, _, h => h.elim
  | x :: xs, m, s, h => by
      simp only [jsonHasStringItems] at h
      simp only [maxNeedItems]
      rcases h with hx | hr
      · exact Nat.le_trans (need_le_maxNeed x m s hx) (le_maxNeedItems xs (maxNeed x m))
      · exact need_le_maxNeedItems xs (maxNeed x m) s hr

theorem need_le_maxNeedFields : ∀ (fs : List (String × Json)) (m : Nat) (s : String),
    jsonHasStringFields fs s → anonNeed s ≤ maxNeedFields fs m
  | [], _, _, h => h.elim
  | (k, v) :: fs, m, s, h => by
      simp only [jsonHasStringFields] at h
      simp only [maxNeedFields]
      rcases h with hk | hv | hr
      · subst hk
        exact Nat.le_trans (Nat.le_max_right m (anonNeed s))
          (Nat.le_trans (le_maxNeed v (max m (anonNeed s)))
            (le_maxNeedFields fs (maxNeed v (max m (anonNeed s)))))
      · exact Nat.le_trans (need_le_maxNeed v (max m (anonNeed k)) s hv)
          (le_maxNeedFields fs (maxNeed v (max m (anonNeed k))))
      · exact need_le_maxNeedFields fs (maxNeed v (max m (anonNeed k))) s hr
end

/-- The characters of a decimal numeral are not underscores. -/
theorem digitChar_ne_underscore (d : Nat) : L4Factoidal.RDF.Canonical.digitChar d ≠ '_' := by
  match d with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => decide
  | (k + 10) => simp [L4Factoidal.RDF.Canonical.digitChar]

/-- A decimal numeral is not empty and holds no underscore. -/
theorem natToDigits_ne : ∀ (n : Nat), L4Factoidal.RDF.Canonical.natToDigits n ≠ [] ∧
    ∀ c ∈ L4Factoidal.RDF.Canonical.natToDigits n, c ≠ '_' := by
  intro n
  induction n using L4Factoidal.RDF.Canonical.natToDigits.induct with
  | case1 n h =>
      have hn : L4Factoidal.RDF.Canonical.natToDigits n =
          [L4Factoidal.RDF.Canonical.digitChar n] := by
        rw [L4Factoidal.RDF.Canonical.natToDigits]; simp [h]
      rw [hn]
      refine ⟨by simp, ?_⟩
      intro c hc
      simp at hc
      subst hc
      exact digitChar_ne_underscore n
  | case2 n h ih =>
      have hn : L4Factoidal.RDF.Canonical.natToDigits n =
          L4Factoidal.RDF.Canonical.natToDigits (n / 10) ++
            [L4Factoidal.RDF.Canonical.digitChar (n % 10)] := by
        rw [L4Factoidal.RDF.Canonical.natToDigits]; simp [h]
      rw [hn]
      refine ⟨by simp, ?_⟩
      intro c hc
      simp only [List.mem_append, List.mem_singleton] at hc
      rcases hc with hc | hc
      · exact ih.2 c hc
      · subst hc; exact digitChar_ne_underscore _

/-- The run of underscores at the start of `replicate k '_' ++ l` is `k` long
when `l` does not start with an underscore. -/
theorem underscoreRun_replicate_append (l : List Char) (hl : ∀ c ∈ l.head?, c ≠ '_') :
    ∀ (k n : Nat), underscoreRun (List.replicate k '_' ++ l) n = n + k := by
  intro k
  induction k with
  | zero =>
      intro n
      cases l with
      | nil => simp [underscoreRun]
      | cons c rest =>
          have hc : c ≠ '_' := hl c (by simp)
          simp only [List.replicate_zero, List.nil_append]
          unfold underscoreRun
          split
          · next heq => exact absurd (List.cons.inj heq).1 hc
          · rfl
  | succ k ih =>
      intro n
      rw [List.replicate_succ, List.cons_append]
      unfold underscoreRun
      simp only
      rw [ih]
      omega

/-- `isBnodeLabel s` says that the characters of `s` start with `_:`. -/
theorem isBnodeLabel_toList {s : String} (h : isBnodeLabel s = true) :
    ∃ rest, s.toList = '_' :: ':' :: rest := by
  unfold isBnodeLabel charAtD at h
  cases hl : s.toList with
  | nil => simp [hl] at h
  | cons a l =>
      cases l with
      | nil => simp [hl] at h
      | cons b rest =>
          simp [hl] at h
          obtain ⟨ha, hb⟩ := h
          subst ha; subst hb
          exact ⟨rest, rfl⟩

/-- The label that `idToSubject` and `typeTerm` read from `s` is the characters
after `_:`. -/
theorem stripBnodePrefix_toList {s : String} (h : isBnodeLabel s = true) :
    (stripBnodePrefix s).toList = s.toList.drop 2 := by
  obtain ⟨rest, hs⟩ := isBnodeLabel_toList h
  unfold stripBnodePrefix slen substr
  rw [hs]
  simp

/-- **A generated label is never a label that the document writes.** `s` is a
key or a string value of the document and a blank node identifier. The label
that the conversion reads from it (`stripBnodePrefix s`, in `idToSubject` and
`typeTerm`) is not the label of any blank node that the conversion generates,
for any counter value. -/
theorem generated_ne_written (root : Json) {s : String}
    (hs : jsonHasString root s) (hb : isBnodeLabel s = true) (n : Nat) :
    stripBnodePrefix s ≠ (freshBnode (generatedPrefix root) n).1 := by
  intro heq
  have hneed : anonNeed s ≤ maxNeed root 0 := need_le_maxNeed root 0 s hs
  obtain ⟨rest, hrest⟩ := isBnodeLabel_toList hb
  have hstrip := stripBnodePrefix_toList hb
  have hlab : (stripBnodePrefix s).toList =
      anonBase.toList ++ List.replicate (maxNeed root 0) '_' ++
        L4Factoidal.RDF.Canonical.natToDigits n := by
    rw [heq]
    simp [freshBnode, L4Factoidal.RDF.Canonical.mkLabel, generatedPrefix]
  rw [hstrip, hrest] at hlab
  simp only [List.drop_succ_cons, List.drop_zero] at hlab
  have hsl : s.toList = "_:_jld_anon".toList ++
      (List.replicate (maxNeed root 0) '_' ++ L4Factoidal.RDF.Canonical.natToDigits n) := by
    rw [hrest, hlab]
    have h1 : anonBase.toList = ['_', 'j', 'l', 'd', '_', 'a', 'n', 'o', 'n'] := by decide
    have h2 : "_:_jld_anon".toList =
        ['_', ':', '_', 'j', 'l', 'd', '_', 'a', 'n', 'o', 'n'] := by decide
    rw [h1, h2]
    simp
  have hstart : s.startsWith "_:_jld_anon" = true :=
    String.startsWith_string_iff.mpr ⟨_, hsl.symm⟩
  have hdrop : s.toList.drop 11 =
      List.replicate (maxNeed root 0) '_' ++ L4Factoidal.RDF.Canonical.natToDigits n := by
    rw [hsl]
    exact List.drop_left' (by decide)
  have hnd := natToDigits_ne n
  have hrun := underscoreRun_replicate_append (L4Factoidal.RDF.Canonical.natToDigits n)
    (by
      intro c hc
      cases hd : L4Factoidal.RDF.Canonical.natToDigits n with
      | nil => simp [hd] at hc
      | cons d ds =>
          simp [hd] at hc
          subst hc
          exact hnd.2 d (by simp [hd])) (maxNeed root 0) 0
  have hneed' : anonNeed s = maxNeed root 0 + 1 := by
    unfold anonNeed
    rw [if_pos hstart, hdrop, hrun]
    omega
  omega

/-- A blank node that `idToSubject` makes has the label that `stripBnodePrefix`
reads from a blank node identifier. -/
theorem idToSubject_bnode {s : String} {l : String}
    (h : idToSubject s = some (.bnode l)) : isBnodeLabel s = true ∧ l = stripBnodePrefix s := by
  unfold idToSubject at h
  split at h
  · next hb =>
      cases h
      exact ⟨hb, rfl⟩
  · split at h
    · cases hm : mkWfIri? s <;> simp [hm] at h
    · cases h

/-- The same for the blank node identifiers in `@type`. -/
theorem typeTerm_bnode {s : String} {l : String}
    (h : typeTerm s = some (.bnode l)) : isBnodeLabel s = true ∧ l = stripBnodePrefix s := by
  unfold typeTerm at h
  split at h
  · next hb =>
      cases h
      exact ⟨hb, rfl⟩
  · split at h
    · cases hm : mkWfIri? s <;> simp [hm] at h
    · cases h

/-- **The labels that the conversion reads from the document, at `@id` and
`@type`, are never generated labels.** -/
theorem idToSubject_ne_generated (root : Json) {s l : String}
    (hs : jsonHasString root s) (h : idToSubject s = some (.bnode l)) (n : Nat) :
    l ≠ (freshBnode (generatedPrefix root) n).1 := by
  obtain ⟨hb, rfl⟩ := idToSubject_bnode h
  exact generated_ne_written root hs hb n

theorem typeTerm_ne_generated (root : Json) {s l : String}
    (hs : jsonHasString root s) (h : typeTerm s = some (.bnode l)) (n : Nat) :
    l ≠ (freshBnode (generatedPrefix root) n).1 := by
  obtain ⟨hb, rfl⟩ := typeTerm_bnode h
  exact generated_ne_written root hs hb n

/-! ## The banned empty-context fallback

`skills/jsonld-context-cache/SKILL.md` states the rule; this is the
rule as a theorem. A silently-empty context expands a document with
every term unmapped — a wrong answer that looks like a right one — so
the failure has to be a failure. -/

/-- **A loader that resolves nothing yields the spec's error, never an
empty context.** JSON-LD 1.1 API §4.1's `loading remote context failed`. -/
theorem fetchRemoteContext_none (url : String) :
    fetchRemoteContext Loader.none url = .error .loadingRemoteContextFailed := by
  unfold fetchRemoteContext Loader.none
  rfl

/-- **And so does the whole context-processing algorithm**, for a
context given as a string reference, whatever the fuel and however the
IRI resolves. Nothing downstream can turn the failure into an empty
active context. -/
theorem contextProcess_string_none_loader (ac : ActiveContext) (s : String)
    (over : Bool) (fuel rfuel : Nat) (visited : List String) :
    ∃ e, contextProcess Loader.none ac (.string s) over fuel rfuel visited = .error e := by
  unfold contextProcess
  cases fuel with
  | zero => exact ⟨.contextOverflow, rfl⟩
  | succ f =>
      simp only
      by_cases hr : rfuel == 0
      · exact ⟨.contextOverflow, by simp [hr]⟩
      · cases hres : resolveContextIri ac s with
        | none => exact ⟨.loadingRemoteContextFailed, by simp [hr]⟩
        | some resolved =>
            by_cases hv : resolved ∈ visited
            · exact ⟨.recursiveContextInclusion, by simp [hr, hv]⟩
            · exact ⟨.loadingRemoteContextFailed, by
                simp [hr, hv, fetchRemoteContext, Loader.none]⟩

/-! ## Small structural facts used by the expansion side -/

/-- **`asArray` is the identity on arrays** — expanded form's
array-wrapping is idempotent. -/
theorem asArray_array (items : List Json) : asArray (.array items) = items := rfl

/-- **A `@list` container may not be combined.** JSON-LD 1.1 API §4.2's
`@container` validation, in the shape `containerKindOfFlags` decides
it. -/
theorem containerKindOfFlags_list_alone :
    containerKindOfFlags false false false false false true = some ContainerKind.list := rfl

theorem containerKindOfFlags_list_combined (g i ix lg ty : Bool)
    (h : (g || i || ix || lg || ty) = true) :
    containerKindOfFlags g i ix lg ty true = none := by
  unfold containerKindOfFlags
  simp [h]

/-- **`@import` merging keeps the CONTAINING context's entry on a key
collision.** JSON-LD 1.1 API §4.1: "merging context into import context,
replacing common entries with those from context". -/
theorem mergeImport_local_suffix (imported local_ : List (String × Json)) :
    ∃ pre, mergeImport imported local_ = pre ++ local_ :=
  ⟨imported.filter (fun kv => !local_.any (fun lv => lv.1 == kv.1)), rfl⟩

/-- **Sorting type names preserves how many there are**, so
`applyTypeScopedContexts` visits every named type exactly once. -/
theorem sortStrings_length : ∀ xs : List String, (sortStrings xs).length = xs.length
  | [] => rfl
  | x :: rest => by
      have hins : ∀ (y : String) (ys : List String),
          (insertSorted y ys).length = ys.length + 1 := by
        intro y ys
        induction ys with
        | nil => rfl
        | cons z zs ih =>
            unfold insertSorted
            by_cases h : strLt y z
            · simp [h]
            · simp [h, ih]
      rw [sortStrings, hins, sortStrings_length rest]
      simp

/-! ## Axiom audit

The trusted base must be exactly Lean's own three. Anything else
appearing below is a regression. -/

#print axioms expandIri_keyword
#print axioms expandIri_keyword_alias
#print axioms expandIri_absolute_authority
#print axioms resolveRedefine_protected_identical
#print axioms findTerm_removeTerm
#print axioms pop_setPrev
#print axioms freshBnode_injective
#print axioms need_le_maxNeed
#print axioms generated_ne_written
#print axioms idToSubject_ne_generated
#print axioms typeTerm_ne_generated
#print axioms fetchRemoteContext_none
#print axioms contextProcess_string_none_loader
#print axioms sortStrings_length

end L4Factoidal.JSONLD
