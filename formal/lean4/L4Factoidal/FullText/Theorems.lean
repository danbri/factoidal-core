/-
L4Factoidal.FullText.Theorems — theorems that bind the full-text
implementation (XQuery and XPath Full Text 3.0) to its specification and
to other parts of Factoidal.

1. AllMatches (§4.2.6.1, §4.2.6.2): `succeeds_applyOr` and
   `succeeds_applyAnd` — FTOr is the disjunction and FTAnd the
   conjunction of the match sets: the result of `ftor` has a successful
   Match exactly when one operand has, the result of `ftand` exactly when
   both have; `mem_applyAnd` — the Matches of `ftand` are the joins of a
   Match of each operand; `evalSel_or`, `evalSel_and` — `fts:evaluate`
   uses them; `unaryNot_fails` — `ftnot` of a successful operand fails.
2. `fn:contains-token` (F&O 4.0 §5.5.6): `contains_spaced` — on a text of
   words separated by spaces, `contains text "w"` with no stop words,
   wildcards or thesaurus is "some word has the comparison key of w";
   `contains_eq_containsToken` — with `case sensitive` and
   `diacritics sensitive` it is "some word equals w", which is
   `fn:contains-token` with the codepoint collation on that text
   (`tokenize(normalize-space($s), ' ')` gives the words). The tokenizer
   lemmas (`foldl_spaced`, `words_spaced`) are proved on the fold that
   the tokenizer runs.
3. Wildcards (§3.4.6) use the shared regular-expression engine:
   `wildcardMatch_eq_regex`, `prepTok_wild`, `qtokMatch_wild` — a
   wildcard query token is the XPath 4.0 regular expression of
   `wildcardRegex`, compiled by `Regex.XPath40.compile` and matched by
   `Regex.isMatch`, the functions of `fn:matches`.
-/
import L4Factoidal.FullText.Select

namespace L4Factoidal.FullText

theorem succeeds_applyOr (a b : AllMatches) :
    (applyOr a b).succeeds = (a.succeeds || b.succeeds) := by
  simp [applyOr, AllMatches.succeeds, List.any_append]

theorem mem_applyAnd (a b : AllMatches) (m : Match) :
    m ∈ (applyAnd a b).ms ↔ ∃ m1 ∈ a.ms, ∃ m2 ∈ b.ms, m = m1.join m2 := by
  simp [applyAnd, List.mem_flatMap, List.mem_map, eq_comm]

theorem join_excl_nil (m1 m2 : Match) :
    (m1.join m2).excl.isEmpty = (m1.excl.isEmpty && m2.excl.isEmpty) := by
  simp only [Match.join]
  cases m1.excl <;> cases m2.excl <;> rfl

theorem succeeds_applyAnd (a b : AllMatches) :
    (applyAnd a b).succeeds = (a.succeeds && b.succeeds) := by
  apply Bool.eq_iff_iff.mpr
  simp only [AllMatches.succeeds, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨m, hm, he⟩
    obtain ⟨m1, h1, m2, h2, rfl⟩ := (mem_applyAnd a b m).mp hm
    rw [join_excl_nil, Bool.and_eq_true] at he
    exact ⟨⟨m1, h1, he.1⟩, ⟨m2, h2, he.2⟩⟩
  · rintro ⟨⟨m1, h1, e1⟩, ⟨m2, h2, e2⟩⟩
    refine ⟨m1.join m2, (mem_applyAnd a b _).mpr ⟨m1, h1, m2, h2, rfl⟩, ?_⟩
    rw [join_excl_nil, e1, e2]; rfl

/-- A plain word: non-empty, word characters only, no ideograph. -/
def PlainWord (w : String) : Prop :=
  w.toList ≠ [] ∧ ∀ c ∈ w.toList, isWordChar c = true ∧ isIdeo c = false

def outWords (s : TokState) : List String := s.out.toList.map (·.word)

theorem step_word (s : TokState) (c : Char) (h1 : isWordChar c = true) (h2 : isIdeo c = false) :
    s.step c = { s with cur := s.cur.push c } := by
  simp [TokState.step, h1, h2]

theorem foldl_word (cs : List Char) (h : ∀ c ∈ cs, isWordChar c = true ∧ isIdeo c = false) :
    ∀ s : TokState, cs.foldl TokState.step s = { s with cur := s.cur ++ cs.toArray } := by
  induction cs with
  | nil => intro s; simp
  | cons c cs ih =>
    intro s
    have hc := h c (by simp)
    have hcs : ∀ x ∈ cs, isWordChar x = true ∧ isIdeo x = false := fun x hx => h x (by simp [hx])
    simp only [List.foldl_cons]
    rw [step_word s c hc.1 hc.2, ih hcs]
    simp [Array.push, List.toArray]

theorem step_space (s : TokState) : s.step ' ' = s.flush := by
  have h1 : isIdeo ' ' = false := by decide
  have h2 : isWordChar ' ' = false := by decide
  have h3 : isSentenceEnd ' ' = false := by decide
  simp [TokState.step, h1, h2, h3]

theorem flush_cur (s : TokState) : s.flush.cur = #[] := by
  unfold TokState.flush; split <;> simp_all

theorem flush_out (s : TokState) (h : s.cur ≠ #[]) :
    outWords s.flush = outWords s ++ [String.ofList s.cur.toList] := by
  unfold TokState.flush outWords
  have : s.cur.isEmpty = false := by simpa [Array.isEmpty_iff] using h
  simp [this]


/-- The text of words separated by single spaces. -/
def spaced (ws : List String) : List Char := List.intercalate [' '] (ws.map String.toList)

theorem foldl_spaced : ∀ (ws : List String), ws ≠ [] → (∀ w ∈ ws, PlainWord w) →
    ∀ s : TokState, s.cur = #[] →
    outWords ((spaced ws).foldl TokState.step s).flush = outWords s ++ ws
  | [], h, _, _, _ => absurd rfl h
  | [w], _, hw, s, hs => by
    have pw := hw w (by simp)
    simp only [spaced, List.map_cons, List.map_nil, List.intercalate_singleton]
    rw [foldl_word w.toList pw.2 s]
    rw [flush_out]
    · simp [outWords, hs, String.ofList_toList]
    · simp [hs]; intro h; exact pw.1 (by simp [h])
  | w :: w' :: ws, _, hw, s, hs => by
    have pw := hw w (by simp)
    have hrest : ∀ x ∈ w' :: ws, PlainWord x := fun x hx => hw x (by simp_all)
    have hsp : spaced (w :: w' :: ws) = w.toList ++ [' '] ++ spaced (w' :: ws) := by
      simp [spaced, List.intercalate_cons_cons]
    rw [hsp, List.foldl_append, List.foldl_append, foldl_word w.toList pw.2 s]
    simp only [List.foldl_cons, List.foldl_nil]
    rw [step_space]
    have ih := foldl_spaced (w' :: ws) (by simp) hrest
      ({ s with cur := s.cur ++ w.toList.toArray } : TokState).flush (flush_cur _)
    rw [ih, flush_out]
    · simp [outWords, hs, String.ofList_toList]
    · simp [hs]; intro h; exact pw.1 (by simp [h])


theorem words_spaced (ws : List String) (hne : ws ≠ []) (hw : ∀ w ∈ ws, PlainWord w) :
    words (String.ofList (spaced ws)) = ws := by
  have := foldl_spaced ws hne hw {} rfl
  simp only [outWords] at this
  simpa [words, tokenizeString, String.toList_ofList] using this

theorem queryTokens_plain (w : String) (hw : PlainWord w) : queryTokens w = [w] := by
  have h := words_spaced [w] (by simp) (by simpa using hw)
  simpa [queryTokens, spaced, String.ofList_toList] using h

/-- The options of the bridge: no stop words, no wildcards, no thesaurus,
    and no `lowercase` / `uppercase`. -/
structure PlainOpts (o : EOpts) : Prop where
  stop : o.stop = []
  wild : o.wild = false
  thes : o.thes = []
  caseO : o.caseO = .insensitive ∨ o.caseO = .sensitive

theorem prepTok_plain (o : EOpts) (h : PlainOpts o) (w : String) :
    prepTok o w = .ok (.key (tokKey o w)) := by
  simp [prepTok, isStop, h.stop, h.wild]

theorem qtokMatch_plain (o : EOpts) (h : PlainOpts o) (k w : String) :
    qtokMatch o (.key k) w = (tokKey o w == k) := by
  rcases h.caseO with hc | hc <;> simp [qtokMatch, docKey, hc]

theorem containsCtx_word (c : Ctx) (o : EOpts) (h : PlainOpts o) (w : String) (hw : PlainWord w) :
    containsCtx c o (.words [w] .any) =
      .ok ((List.range c.toks.size).any (fun i => tokKey o (c.toks.getD i default).word == tokKey o w)) := by
  have ht : tokensOf o w = [w] := by simp [tokensOf, h.wild, queryTokens_plain w hw]
  simp [containsCtx, evalSel, applyWords, ht, wordsItems, wordsFold, phrase, h.thes, phraseNoThes,
    matchTokenInfos, prepTok_plain o h, qtokMatch_plain o h, AllMatches.succeeds, List.foldlM_cons,
    List.foldlM_nil, bind, Except.bind, pure, Except.pure]
  congr 1
  funext i
  split <;> rename_i heq <;> split at heq <;> simp_all


theorem range_any_getD {α} [Inhabited α] (a : Array α) (f : α → Bool) :
    (List.range a.size).any (fun i => f (a.getD i default)) = a.toList.any f := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨i, hi, hf⟩
    refine ⟨a[i], ?_, ?_⟩
    · simp
    · simpa [Array.getD, hi] using hf
  · rintro ⟨x, hx, hf⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
    refine ⟨i, by simpa using hi, ?_⟩
    simpa [Array.getD, show i < a.size by simpa using hi] using hf

/-- `contains text` with one word and the plain options, on a text of
    words separated by spaces: some word of the text has the comparison
    key of the query word. -/
theorem contains_spaced (ws : List String) (hne : ws ≠ []) (hws : ∀ x ∈ ws, PlainWord x)
    (o : EOpts) (h : PlainOpts o) (w : String) (hw : PlainWord w) :
    containsCtx (Ctx.ofToks (tokenizeString (String.ofList (spaced ws)))) o (.words [w] .any) =
      .ok (ws.any (fun x => tokKey o x == tokKey o w)) := by
  rw [containsCtx_word _ o h w hw]
  have hw' := words_spaced ws hne hws
  simp only [words] at hw'
  simp only [Ctx.ofToks]
  rw [range_any_getD (tokenizeString (String.ofList (spaced ws))) (fun t => tokKey o t.word == tokKey o w)]
  conv => rhs; arg 1; rw [← hw']
  simp [List.any_map, Function.comp_def]

/-- The comparison key is the token itself when case and diacritics are
    significant and stemming is off. -/
theorem tokKey_exact (o : EOpts) (hc : o.caseO = .sensitive) (hd : o.diacriticsSensitive = true)
    (hs : o.stem = false) (x : String) : tokKey o x = x := by
  simp [tokKey, hc, hd, hs]

/-- Bridge to `fn:contains-token` (F&O 4.0 §5.5.6): on a text of words
    separated by single spaces, `tokenize(normalize-space($s), ' ')` is the
    list of the words, and with the codepoint collation `contains-token`
    is true when one of them equals the token. `contains text` with that
    word, `using case sensitive using diacritics sensitive` and no
    stemming, has the same value. -/
theorem contains_eq_containsToken (ws : List String) (hne : ws ≠ []) (hws : ∀ x ∈ ws, PlainWord x)
    (o : EOpts) (h : PlainOpts o) (hc : o.caseO = .sensitive) (hd : o.diacriticsSensitive = true)
    (hs : o.stem = false) (w : String) (hw : PlainWord w) :
    containsCtx (Ctx.ofToks (tokenizeString (String.ofList (spaced ws)))) o (.words [w] .any) =
      .ok (ws.any (fun t => t == w)) := by
  rw [contains_spaced ws hne hws o h w hw]
  simp [tokKey_exact o hc hd hs]

theorem wildcardMatch_eq_regex (q t : String) (b : Bool) :
    wildcardMatch q t = some b ↔
      ∃ p r, wildcardRegex q = some p ∧ Regex.XPath40.compile p "" = .ok r ∧ Regex.isMatch r t = b := by
  unfold wildcardMatch
  constructor
  · intro h
    split at h
    · simp at h
    · rename_i p hp
      split at h
      · rename_i r hr
        exact ⟨p, r, hp, hr, by simpa using h⟩
      · simp at h
  · rintro ⟨p, r, hp, hr, hb⟩
    simp [hp, hr, hb]

theorem prepTok_wild (o : EOpts) (hw : o.wild = true) (q : String) (hs : isStop o q = false)
    (r : Regex.Compiled) :
    prepTok o q = .ok (.wild r) ↔
      ∃ p, wildcardRegex (wildKey o q) = some p ∧ Regex.XPath40.compile p "" = .ok r := by
  unfold prepTok prepWild wildKey
  simp only [hs, hw, Bool.false_eq_true, if_false, if_true]
  constructor
  · intro h
    split at h
    · simp [Except.map] at h
    · rename_i p hp
      split at h
      · rename_i r' hr
        simp [Except.map] at h
        exact ⟨p, hp, h ▸ hr⟩
      · simp [Except.map] at h
  · rintro ⟨p, hp, hr⟩
    simp only [beq_iff_eq] at hp
    simp [hp, hr, Except.map]

theorem qtokMatch_wild (o : EOpts) (r : Regex.Compiled) (w : String)
    (hc : o.caseO = .insensitive ∨ o.caseO = .sensitive) :
    qtokMatch o (.wild r) w = Regex.isMatch r (wildKey o w) := by
  rcases hc with hc | hc <;> simp [qtokMatch, hc]

theorem evalSel_or (c : Ctx) (o : EOpts) (x y : RSel) (n : Nat) (a b : AllMatches)
    (hx : evalSel c o x n = .ok a) (hy : evalSel c o y a.stokenNum = .ok b) :
    evalSel c o (.or x y) n = .ok (applyOr a b) := by
  simp [evalSel, hx, hy, bind, Except.bind, pure, Except.pure]

theorem evalSel_and (c : Ctx) (o : EOpts) (x y : RSel) (n : Nat) (a b : AllMatches)
    (hx : evalSel c o x n = .ok a) (hy : evalSel c o y a.stokenNum = .ok b) :
    evalSel c o (.and x y) n = .ok (applyAnd a b) := by
  simp [evalSel, hx, hy, bind, Except.bind, pure, Except.pure]

theorem applyUnaryNot_nil (k : Nat) :
    (applyUnaryNot { stokenNum := k, ms := [] }).succeeds = true := by
  rfl

theorem addInverted_excl_ne (c : Bool × StringMatch) (x : Match) (h : x.excl ≠ []) :
    (x.addInverted c).excl ≠ [] := by
  unfold Match.addInverted; split <;> simp_all

theorem unaryNotHelper_excl (ms : List Match) (m : Match) (hm : m ∈ ms) (he : m.excl = []) :
    ∀ r ∈ unaryNotHelper ms, r.excl ≠ [] := by
  induction ms with
  | nil => simp at hm
  | cons m0 rest ih =>
    intro r hr
    simp only [unaryNotHelper, List.mem_flatMap, List.mem_map] at hr
    obtain ⟨c, hc, x, hx, rfl⟩ := hr
    rcases List.mem_cons.mp hm with h0 | h1
    · subst h0
      simp [Match.children, he] at hc
      obtain ⟨s, _, rfl⟩ := hc
      simp [Match.addInverted]
    · exact addInverted_excl_ne c x (ih h1 x hx)

/-- FTUnaryNot (§4.2.6.3): when the operand has a successful Match (no
    StringExclude), the negation has none. -/
theorem unaryNot_fails (a : AllMatches) (m : Match) (hm : m ∈ a.ms) (he : m.excl = []) :
    (applyUnaryNot a).succeeds = false := by
  simp only [AllMatches.succeeds, applyUnaryNot]
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨r, hr, hre⟩ := List.any_eq_true.mp h
  exact unaryNotHelper_excl a.ms m hm he r hr (by simpa using hre)

/-! ## Checks -/

#guard words "One two. Three four." == ["One", "two", "Three", "four"]
#guard (tokenizeString "One two. Three four.").toList.map (·.sent) == [1, 1, 2, 2]
#guard (tokenizeSegments ["simple ", "complex"]).toList.map (·.para) == [1, 2]
#guard (tokenizeSegments ["p", "rototypes"]).toList.map (·.word) == ["prototypes"]
#guard words "网站建置" == ["网", "站", "建", "置"]
#guard queryTokensWild "nex.\\? task? .uniq?e" == ["nex.", "task", ".uniq", "e"]
#guard wildcardMatch "un.{2,3}e" "unique" == some true
#guard wildcardMatch "un.{2,3}e" "une" == some false
#guard (wildcardRegex "un.{3-4}e").isNone

end L4Factoidal.FullText
