/-
L4Factoidal.Syntax.NQuadsDocRoundTrip — the N-Quads document round trip:
`parseNQuads` reads back the quads that `Dataset.toNQuads` wrote
(https://github.com/danbri/factoidal/issues/975, phase C).

The writer writes the default graph as N-Triples lines and each triple of a
named graph as a line with the graph label (`namedLine`). The lines are
`quadsOf ds`, in order (`toNQuads_lines`). The parser reads each line back
(`readNQuad11_line`, `readNQuad12_line`, on the term lemmas of
`Syntax/NTriplesDocRoundTrip.lean`) and adds each quad with `addQuad`
(`parseNQuads_toNQuads`). The dataset it gives has the quads of `quadsOf ds`
under RDF term equality, and the names of the graphs that have a quad
(`foldl_addQuad_memQuad`, `foldl_addQuad_names`).

The domain is `Quad.ntLex` on each written quad: the triple as for
N-Triples, and the graph label, RDF 1.1 N-Quads production [6] graphLabel
(IRIREF or BLANK_NODE_LABEL), in the lexical space of its production. The
writer domain of `RDF/Sink.lean`, `Quad.ntSafe`, has no condition on
blank-node labels; `Quad.ntLex_renameBnodes` takes it to `Quad.ntLex` after
the relabelling of `Dataset.relabelForWrite`.

No `sorry`, no `axiom`, no `native_decide`, no `partial`.
-/
import L4Factoidal.Syntax.NTriplesDocRoundTrip
import L4Factoidal.Syntax.NQuads
import L4Factoidal.RDF.DatasetSet

namespace L4Factoidal.Syntax.NQuadsRoundTrip

open L4Factoidal.RDF
open L4Factoidal.Syntax
open L4Factoidal.Syntax.NTriplesRoundTrip

/-! ## The quads the writer writes, and the domain -/

/-- The quads of a dataset in the order `Dataset.toNQuads` writes them: the
default graph, then each named graph. An empty named graph has no quad. The
same list as `Dataset.quadList` of `RDF/DatasetNormalize.lean` (the canonical
N-Quads round trip), which this module does not import: its lemma names
(`readNQuad11_line`, `readGraphLabel_safe`, ...) are the names of its own
canonical-form lemmas. -/
def quadsOf (ds : Dataset) : List (Triple × Option Subject) :=
  ds.default.map (fun t => (t, none)) ++
    ds.named.flatMap (fun ng => ng.graph.map (fun t => (t, some ng.name)))

/-- A quad that the N-Quads grammar can state: the triple, and the graph
label (IRIREF or BLANK_NODE_LABEL, RDF 1.1 N-Quads [6]). -/
def Quad.ntLex (q : Triple × Option Subject) : Bool :=
  Triple.ntLex q.1 && q.2.all Subject.ntLex

/-- A quad in the writer domain of N-Quads: `Quad.ntLex` with no condition on
blank-node labels (the writers of `RDF/Sink.lean` relabel first,
`Dataset.relabelForWrite`). -/
def Quad.ntSafe (q : Triple × Option Subject) : Bool :=
  Triple.ntSafe q.1 && q.2.all Subject.ntSafe

/-- The quads of the relabelled dataset are the relabelled quads. -/
theorem quadsOf_renameBnodes (f : BNodeId → BNodeId) (ds : Dataset) :
    quadsOf (ds.renameBnodes f) =
      (quadsOf ds).map (fun q => (q.1.renameBnodes f, q.2.map (Subject.renameBnodes f))) := by
  simp [quadsOf, Dataset.renameBnodes, Graph.renameBnodes, List.map_append, List.flatMap_map,
    List.map_flatMap, Function.comp_def]

/-- **A relabelled quad of the writer domain**, with a map whose labels are
BLANK_NODE_LABELs, is in the domain of the round trip. -/
theorem Quad.ntLex_renameBnodes {f : BNodeId → BNodeId} (hf : ∀ b, isBlankNodeLabel (f b) = true)
    {q : Triple × Option Subject} (h : Quad.ntSafe q = true) :
    Quad.ntLex (q.1.renameBnodes f, q.2.map (Subject.renameBnodes f)) = true := by
  obtain ⟨t, g⟩ := q
  simp only [Quad.ntSafe, Bool.and_eq_true] at h
  simp only [Quad.ntLex, Bool.and_eq_true]
  refine ⟨Triple.ntLex_renameBnodes hf h.1, ?_⟩
  cases g with
  | none => rfl
  | some g =>
    simp only [Option.map_some, Option.all_some] at h ⊢
    apply Subject.ntLex_of_ntSafe
    · rw [Subject.ntSafe_renameBnodes]; exact h.2
    · intro b hb
      rw [Subject.bnodes_renameBnodes, List.mem_map] at hb
      obtain ⟨a, -, rfl⟩ := hb
      exact hf a

/-- The line of one quad. -/
def quadLine (mode : Mode) : Triple × Option Subject → Except String String
  | (t, none) => Triple.toNTriples mode t
  | (t, some g) => namedLine mode g t

/-! ## The text: the lines of the quads, in order -/

/-- `ls` are the lines `f` gives for `xs`, one for each. -/
def Lines {α : Type} (f : α → Except String String) : List α → List String → Prop
  | [], [] => True
  | x :: xs, l :: ls => f x = .ok l ∧ Lines f xs ls
  | _, _ => False

theorem Lines.append {α : Type} {f : α → Except String String} :
    ∀ {xs ys : List α} {ls ms : List String}, Lines f xs ls → Lines f ys ms → Lines f (xs ++ ys) (ls ++ ms)
  | [], _, [], _, _, h => h
  | _ :: _, _, _ :: _, _, ⟨h1, h2⟩, h => ⟨h1, Lines.append h2 h⟩
  | [], _, _ :: _, _, h, _ => h.elim
  | _ :: _, _, [], _, h, _ => h.elim

/-- One step of the writer's fold. -/
def lineStep {α : Type} (f : α → Except String String) (acc : Except String String) (x : α) :
    Except String String :=
  match acc with
  | .error e => .error e
  | .ok s =>
      match f x with
      | .error e => .error e
      | .ok line => .ok (s ++ line)

theorem foldl_lineStep_error {α : Type} (f : α → Except String String) :
    ∀ (xs : List α) (e : String), xs.foldl (lineStep f) (.error e) = .error e
  | [], _ => rfl
  | _ :: xs, e => foldl_lineStep_error f xs e

/-- A successful fold is the lines of the elements, in order. -/
theorem foldl_lineStep_ok {α : Type} (f : α → Except String String) :
    ∀ (xs : List α) (s r : String), xs.foldl (lineStep f) (.ok s) = .ok r →
      ∃ ls, Lines f xs ls ∧ r = s ++ String.join ls
  | [], s, r, h => by
    simp only [List.foldl_nil, Except.ok.injEq] at h
    exact ⟨[], trivial, by simp [h]⟩
  | x :: xs, s, r, h => by
    simp only [List.foldl_cons] at h
    cases hx : f x with
    | error e =>
      simp only [lineStep, hx] at h
      rw [foldl_lineStep_error] at h
      cases h
    | ok line =>
      simp only [lineStep, hx] at h
      obtain ⟨ls, hl, hr⟩ := foldl_lineStep_ok f xs (s ++ line) r h
      exact ⟨line :: ls, ⟨hx, hl⟩, by rw [hr]; simp [String.append_assoc]⟩

theorem Lines.map {α β : Type} {f : β → Except String String} (g : α → β) :
    ∀ {xs : List α} {ls : List String}, Lines (fun x => f (g x)) xs ls → Lines f (xs.map g) ls
  | [], [], _ => trivial
  | _ :: _, _ :: _, ⟨h1, h2⟩ => ⟨h1, Lines.map g h2⟩
  | [], _ :: _, h => h.elim
  | _ :: _, [], h => h.elim

/-- One step of the writer's fold over the named graphs. -/
def namedStep (mode : Mode) (acc : Except String String) (ng : NamedGraph) : Except String String :=
  match acc with
  | .error e => .error e
  | .ok s => ng.graph.foldl (lineStep (namedLine mode ng.name)) (.ok s)

theorem foldl_namedStep_error (mode : Mode) :
    ∀ (ngs : List NamedGraph) (e : String), ngs.foldl (namedStep mode) (.error e) = .error e
  | [], _ => rfl
  | _ :: ngs, e => foldl_namedStep_error mode ngs e

theorem foldl_namedStep_ok (mode : Mode) :
    ∀ (ngs : List NamedGraph) (s r : String), ngs.foldl (namedStep mode) (.ok s) = .ok r →
      ∃ ls, Lines (quadLine mode) (ngs.flatMap (fun ng => ng.graph.map (fun t => (t, some ng.name)))) ls ∧
        r = s ++ String.join ls
  | [], s, r, h => by
    simp only [List.foldl_nil, Except.ok.injEq] at h
    exact ⟨[], trivial, by simp [h]⟩
  | ng :: ngs, s, r, h => by
    simp only [List.foldl_cons] at h
    cases hg : ng.graph.foldl (lineStep (namedLine mode ng.name)) (.ok s) with
    | error e =>
      simp only [namedStep, hg] at h
      rw [foldl_namedStep_error] at h
      cases h
    | ok s' =>
      simp only [namedStep, hg] at h
      obtain ⟨l1, hl1, hr1⟩ := foldl_lineStep_ok (namedLine mode ng.name) ng.graph s s' hg
      obtain ⟨l2, hl2, hr2⟩ := foldl_namedStep_ok mode ngs s' r h
      refine ⟨l1 ++ l2, ?_, ?_⟩
      · rw [List.flatMap_cons]
        exact Lines.append (Lines.map (f := quadLine mode) (fun t => (t, some ng.name)) hl1) hl2
      · rw [hr2, hr1]; simp [String.append_assoc]

/-- **The text of the N-Quads writer** is the lines of `quadsOf ds`, in order. -/
theorem toNQuads_lines (mode : Mode) (ds : Dataset) (text : String)
    (h : Dataset.toNQuads ds mode = .ok text) :
    ∃ ls, Lines (quadLine mode) (quadsOf ds) ls ∧ text = String.join ls := by
  have hdef : Dataset.toNQuads ds mode =
      match ds.default.foldl (lineStep (Triple.toNTriples mode)) (.ok "") with
      | .error e => .error e
      | .ok d => ds.named.foldl (namedStep mode) (.ok d) := rfl
  rw [hdef] at h
  cases hd : ds.default.foldl (lineStep (Triple.toNTriples mode)) (.ok "") with
  | error e => rw [hd] at h; cases h
  | ok d =>
    rw [hd] at h
    obtain ⟨ld, hld, hdr⟩ := foldl_lineStep_ok (Triple.toNTriples mode) ds.default "" d hd
    have hld' : Lines (quadLine mode) (ds.default.map (fun t => (t, none))) ld :=
      Lines.map (f := quadLine mode) (fun t => (t, (none : Option Subject))) hld
    obtain ⟨ln, hln, hnr⟩ := foldl_namedStep_ok mode ds.named d text h
    refine ⟨ld ++ ln, Lines.append hld' hln, ?_⟩
    rw [hnr, hdr]; simp

/-! ## One line -/

/-- **A graph label in the domain reads back**, followed by a space. -/
theorem readGraphLabel_safe (pos : Nat) (g : Subject) (tail : List Char)
    (h : Subject.ntLex g = true) :
    ∃ p, readGraphLabel pos ((Subject.toNTriples g).toList ++ ' ' :: tail) = .ok (g, p, ' ' :: tail) := by
  cases g with
  | iri i =>
    have hc : (Subject.toNTriples (.iri i)).toList ++ ' ' :: tail
        = '<' :: (i.val.toList ++ '>' :: ' ' :: tail) := by simp [Subject.toNTriples]
    rw [hc]
    simp only [readGraphLabel, ← hc]
    rw [hc, readIriRef_printSafe pos i _ h]
    simp only [mkIri_val]
    exact ⟨_, rfl⟩
  | bnode b =>
    have hc : (Subject.toNTriples (.bnode b)).toList ++ ' ' :: tail
        = '_' :: ':' :: (b.toList ++ ' ' :: tail) := by simp [Subject.toNTriples]
    obtain ⟨p, hp⟩ := readBlankNodeLabel_safe pos b tail h
    rw [hc]
    simp only [readGraphLabel, ← hc]
    rw [hc, hp]
    exact ⟨p, rfl⟩

/-- **One N-Quads line in the domain reads back** (RDF 1.1 reader): the triple,
the graph label, and the line break after the `.`. -/
theorem readNQuad11_line (pos : Nat) (q : Triple × Option Subject) (line : String) (tail : List Char)
    (hs : Quad.ntLex q = true) (h : quadLine .rdf11 q = .ok line) :
    ∃ p, readNQuad11 pos (line.toList ++ tail) = .ok (q.1, q.2, p, '\n' :: tail) := by
  obtain ⟨⟨s, pr, o⟩, g⟩ := q
  simp only [Quad.ntLex, Triple.ntLex, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨hss, hps⟩, hos⟩, hgs⟩ := hs
  cases ho : Term.toNTriples .rdf11 o with
  | error e => cases g <;> simp [quadLine, Triple.toNTriples, namedLine, ho] at h
  | ok oStr =>
    obtain ⟨c, ctail, hafter, hcafter, hopt⟩ : ∃ c ctail,
        line.toList ++ tail = (Subject.toNTriples s).toList ++ ' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
          (oStr.toList ++ ' ' :: c :: ctail))) ∧
        (c = '.' ∨ c = ')' ∨ c = '<' ∨ c = '_') ∧
        ∀ p6, ∃ p7, readOptGraphLabel p6 (' ' :: c :: ctail) = .ok (g, p7, ' ' :: '.' :: '\n' :: tail) ∨
          readOptGraphLabel p6 (' ' :: c :: ctail) = .ok (g, p7, '.' :: '\n' :: tail) := by
      cases g with
      | none =>
        simp only [quadLine, Triple.toNTriples, ho, Except.ok.injEq] at h
        subst h
        refine ⟨'.', '\n' :: tail, by simp, Or.inl rfl, fun p6 => ⟨p6 + 1, Or.inr ?_⟩⟩
        simp [readOptGraphLabel, skipWs, List.span, List.span.loop, isNtWs]
      | some gn =>
        simp only [quadLine, namedLine, ho, Except.ok.injEq] at h
        subst h
        simp only [Option.all_some] at hgs
        have hl : (Subject.toNTriples s ++ " <" ++ pr.val ++ "> " ++ oStr ++ " " ++ Subject.toNTriples gn
            ++ " .\n").toList ++ tail
            = (Subject.toNTriples s).toList ++ ' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
              (oStr.toList ++ ' ' :: ((Subject.toNTriples gn).toList ++ ' ' :: '.' :: '\n' :: tail)))) := by
          simp
        obtain ⟨r0, hr0⟩ := subject_toNTriples_head gn (' ' :: '.' :: '\n' :: tail)
        rcases hr0 with hr0 | hr0
        · refine ⟨'<', r0, by rw [hl, hr0], Or.inr (Or.inr (Or.inl rfl)), fun p6 => ?_⟩
          obtain ⟨p7, hp7⟩ := readGraphLabel_safe (p6 + 1) gn ('.' :: '\n' :: tail) hgs
          refine ⟨p7, Or.inl ?_⟩
          rw [hr0] at hp7
          simp only [readOptGraphLabel, skipWs_space _ (by decide : isNtWs '<' = false), hp7]
        · refine ⟨'_', r0, by rw [hl, hr0], Or.inr (Or.inr (Or.inr rfl)), fun p6 => ?_⟩
          obtain ⟨p7, hp7⟩ := readGraphLabel_safe (p6 + 1) gn ('.' :: '\n' :: tail) hgs
          refine ⟨p7, Or.inl ?_⟩
          have hb : ∃ r1, r0 = ':' :: r1 := by
            cases gn with
            | iri i => simp [Subject.toNTriples] at hr0
            | bnode b => simp [Subject.toNTriples] at hr0; exact ⟨_, hr0.symm⟩
          obtain ⟨r1, rfl⟩ := hb
          rw [hr0] at hp7
          simp only [readOptGraphLabel, skipWs_space _ (by decide : isNtWs '_' = false), hp7]
    rw [hafter]
    obtain ⟨r0, hr0⟩ := subject_toNTriples_head s (' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: c :: ctail))))
    have hws0 : skipWs pos ((Subject.toNTriples s).toList ++ ' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: c :: ctail))))
        = (pos, (Subject.toNTriples s).toList ++ ' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: c :: ctail)))) := by
      rcases hr0 with hr0 | hr0 <;> rw [hr0] <;> exact skipWs_stop pos (by decide)
    obtain ⟨p2, hp2⟩ := readSubject_safe pos s ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: c :: ctail))) hss
    obtain ⟨c5, r5, hcr, hc5⟩ := term_toNTriples_head .rdf11 o oStr (' ' :: c :: ctail) ho
    have hcws : isNtWs c5 = false := by rcases hc5 with rfl | rfl | rfl <;> decide
    obtain ⟨p6, hp6⟩ := readObject11_safe (p2 + 1 + pr.val.length + 2 + 1) o oStr (c :: ctail) hos ho
    unfold readNQuad11
    rw [hws0]
    dsimp only
    rw [hp2]
    dsimp only
    rw [skipWs_space _ (by decide : isNtWs '<' = false)]
    dsimp only
    rw [readPredicate_printSafe _ pr _ hps]
    dsimp only
    rw [hcr, skipWs_space _ hcws, ← hcr, hp6]
    dsimp only
    obtain ⟨p7, hp7⟩ := hopt p6
    rcases hp7 with hp7 | hp7
    · rw [hp7]
      dsimp only
      rw [skipWs_space _ (by decide : isNtWs '.' = false)]
      exact ⟨_, rfl⟩
    · rw [hp7]
      dsimp only
      rw [skipWs_stop _ (by decide : isNtWs '.' = false)]
      exact ⟨_, rfl⟩

/-- **One N-Quads line in the domain reads back** (RDF 1.2 reader): the triple,
the graph label, and the line break after the `.`. -/
theorem readNQuad12_line (pos : Nat) (q : Triple × Option Subject) (line : String) (tail : List Char)
    (hs : Quad.ntLex q = true) (h : quadLine .rdf12 q = .ok line) :
    ∃ p, readNQuad12 pos (line.toList ++ tail) = .ok (q.1, q.2, p, '\n' :: tail) := by
  obtain ⟨⟨s, pr, o⟩, g⟩ := q
  simp only [Quad.ntLex, Triple.ntLex, Bool.and_eq_true] at hs
  obtain ⟨⟨⟨hss, hps⟩, hos⟩, hgs⟩ := hs
  cases ho : Term.toNTriples .rdf12 o with
  | error e => cases g <;> simp [quadLine, Triple.toNTriples, namedLine, ho] at h
  | ok oStr =>
    obtain ⟨c, ctail, hafter, hcafter, hopt⟩ : ∃ c ctail,
        line.toList ++ tail = (Subject.toNTriples s).toList ++ ' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
          (oStr.toList ++ ' ' :: c :: ctail))) ∧
        (c = '.' ∨ c = ')' ∨ c = '<' ∨ c = '_') ∧
        ∀ p6, ∃ p7, readOptGraphLabel p6 (' ' :: c :: ctail) = .ok (g, p7, ' ' :: '.' :: '\n' :: tail) ∨
          readOptGraphLabel p6 (' ' :: c :: ctail) = .ok (g, p7, '.' :: '\n' :: tail) := by
      cases g with
      | none =>
        simp only [quadLine, Triple.toNTriples, ho, Except.ok.injEq] at h
        subst h
        refine ⟨'.', '\n' :: tail, by simp, Or.inl rfl, fun p6 => ⟨p6 + 1, Or.inr ?_⟩⟩
        simp [readOptGraphLabel, skipWs, List.span, List.span.loop, isNtWs]
      | some gn =>
        simp only [quadLine, namedLine, ho, Except.ok.injEq] at h
        subst h
        simp only [Option.all_some] at hgs
        have hl : (Subject.toNTriples s ++ " <" ++ pr.val ++ "> " ++ oStr ++ " " ++ Subject.toNTriples gn
            ++ " .\n").toList ++ tail
            = (Subject.toNTriples s).toList ++ ' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
              (oStr.toList ++ ' ' :: ((Subject.toNTriples gn).toList ++ ' ' :: '.' :: '\n' :: tail)))) := by
          simp
        obtain ⟨r0, hr0⟩ := subject_toNTriples_head gn (' ' :: '.' :: '\n' :: tail)
        rcases hr0 with hr0 | hr0
        · refine ⟨'<', r0, by rw [hl, hr0], Or.inr (Or.inr (Or.inl rfl)), fun p6 => ?_⟩
          obtain ⟨p7, hp7⟩ := readGraphLabel_safe (p6 + 1) gn ('.' :: '\n' :: tail) hgs
          refine ⟨p7, Or.inl ?_⟩
          rw [hr0] at hp7
          simp only [readOptGraphLabel, skipWs_space _ (by decide : isNtWs '<' = false), hp7]
        · refine ⟨'_', r0, by rw [hl, hr0], Or.inr (Or.inr (Or.inr rfl)), fun p6 => ?_⟩
          obtain ⟨p7, hp7⟩ := readGraphLabel_safe (p6 + 1) gn ('.' :: '\n' :: tail) hgs
          refine ⟨p7, Or.inl ?_⟩
          have hb : ∃ r1, r0 = ':' :: r1 := by
            cases gn with
            | iri i => simp [Subject.toNTriples] at hr0
            | bnode b => simp [Subject.toNTriples] at hr0; exact ⟨_, hr0.symm⟩
          obtain ⟨r1, rfl⟩ := hb
          rw [hr0] at hp7
          simp only [readOptGraphLabel, skipWs_space _ (by decide : isNtWs '_' = false), hp7]
    rw [hafter]
    obtain ⟨r0, hr0⟩ := subject_toNTriples_head s (' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: c :: ctail))))
    have hws0 : skipWs pos ((Subject.toNTriples s).toList ++ ' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: c :: ctail))))
        = (pos, (Subject.toNTriples s).toList ++ ' ' :: ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: c :: ctail)))) := by
      rcases hr0 with hr0 | hr0 <;> rw [hr0] <;> exact skipWs_stop pos (by decide)
    obtain ⟨p2, hp2⟩ := readSubject_safe pos s ('<' :: (pr.val.toList ++ '>' :: ' ' ::
            (oStr.toList ++ ' ' :: c :: ctail))) hss
    obtain ⟨c5, r5, hcr, hc5⟩ := term_toNTriples_head .rdf12 o oStr (' ' :: c :: ctail) ho
    have hcws : isNtWs c5 = false := by rcases hc5 with rfl | rfl | rfl <;> decide
    have hfuel : oStr.toList.length < lineFuel (oStr.toList ++ ' ' :: c :: ctail) := by
      have := lineFuelGo_ge oStr.toList (' ' :: c :: ctail) 1 (nl_not_mem_term .rdf12 o oStr hos ho)
      unfold lineFuel
      omega
    obtain ⟨p6, hp6⟩ := readObject12_safe o _ (p2 + 1 + pr.val.length + 2 + 1) oStr c ctail
      hos ho hfuel hcafter
    unfold readNQuad12
    rw [hws0]
    dsimp only
    rw [hp2]
    dsimp only
    rw [skipWs_space _ (by decide : isNtWs '<' = false)]
    dsimp only
    rw [readPredicate_printSafe _ pr _ hps]
    dsimp only
    rw [hcr, skipWs_space _ hcws, ← hcr, hp6]
    dsimp only
    obtain ⟨p7, hp7⟩ := hopt p6
    rcases hp7 with hp7 | hp7
    · rw [hp7]
      dsimp only
      rw [skipWs_space _ (by decide : isNtWs '.' = false)]
      exact ⟨_, rfl⟩
    · rw [hp7]
      dsimp only
      rw [skipWs_stop _ (by decide : isNtWs '.' = false)]
      exact ⟨_, rfl⟩

/-- The line reader of `mode`. -/
def readNQuadOf : Mode → Nat → List Char → Except ParseError (Triple × Option Subject × Nat × List Char)
  | .rdf11 => readNQuad11
  | .rdf12 => readNQuad12

theorem readNQuadOf_line (mode : Mode) (pos : Nat) (q : Triple × Option Subject) (line : String)
    (tail : List Char) (hs : Quad.ntLex q = true) (h : quadLine mode q = .ok line) :
    ∃ p, readNQuadOf mode pos (line.toList ++ tail) = .ok (q.1, q.2, p, '\n' :: tail) := by
  cases mode
  · exact readNQuad11_line pos q line tail hs h
  · exact readNQuad12_line pos q line tail hs h

/-- The text of a line starts with `<` or `_`. -/
theorem quadLine_head (mode : Mode) (q : Triple × Option Subject) (line : String) (tail : List Char)
    (h : quadLine mode q = .ok line) :
    ∃ r, line.toList ++ tail = '<' :: r ∨ line.toList ++ tail = '_' :: r := by
  obtain ⟨t, g⟩ := q
  cases g with
  | none => exact triple_toNTriples_head mode t line tail h
  | some gn =>
    simp only [quadLine, namedLine] at h
    cases ho : Term.toNTriples mode t.o with
    | error e => rw [ho] at h; cases h
    | ok oStr =>
      rw [ho] at h
      simp only [Except.ok.injEq] at h
      subst h
      obtain ⟨r, hr⟩ := subject_toNTriples_head t.s
        ((" <" ++ t.p.val ++ "> " ++ oStr ++ " " ++ Subject.toNTriples gn ++ " .\n").toList ++ tail)
      refine ⟨r, ?_⟩
      simpa [String.append_assoc] using hr

theorem quadLine_ne_nil (mode : Mode) (q : Triple × Option Subject) (line : String)
    (h : quadLine mode q = .ok line) : line.toList ≠ [] := by
  obtain ⟨r, hr⟩ := quadLine_head mode q line [] h
  rw [List.append_nil] at hr
  rcases hr with hr | hr <;> rw [hr] <;> simp

/-! ## The document -/

/-- The parser adds each quad with `addQuad`. -/
def addAll (acc : Dataset) (qs : List (Triple × Option Subject)) : Dataset :=
  qs.foldl (fun d q => addQuad d q.1 q.2) acc

/-- The lines of the quads, read in order. -/
theorem parseQuadLinesAcc_lines (mode : Mode) :
    ∀ (qs : List (Triple × Option Subject)) (ls : List String) (fuel pos : Nat) (acc : Dataset),
      qs.all Quad.ntLex = true → Lines (quadLine mode) qs ls →
      (String.join ls).toList.length < fuel →
      parseQuadLinesAcc mode fuel pos (String.join ls).toList acc = .ok (addAll acc qs)
  | [], [], fuel, pos, acc, _, _, hf => by
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hf; omega⟩
    simp [parseQuadLinesAcc, skipWs, List.span, List.span.loop, addAll]
  | [], _ :: _, _, _, _, _, h, _ => h.elim
  | _ :: _, [], _, _, _, _, h, _ => h.elim
  | q :: qs, line :: ls, fuel, pos, acc, hs, ⟨hline, hls⟩, hf => by
    simp only [List.all_cons, Bool.and_eq_true] at hs
    simp only [String.join_cons, String.toList_append] at hf ⊢
    generalize hR : (String.join ls).toList = R at hf
    have hne := quadLine_ne_nil mode q line hline
    have hlen : line.toList.length ≥ 1 := by
      cases hh : line.toList with
      | nil => exact absurd hh hne
      | cons _ _ => simp
    rw [List.length_append] at hf
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
    have hfR : R.length < f := by omega
    obtain ⟨p, hp⟩ := readNQuadOf_line mode pos q line R hs.1 hline
    obtain ⟨r0, hr0⟩ := quadLine_head mode q line R hline
    have ih := parseQuadLinesAcc_lines mode qs ls f (p + 1) (addQuad acc q.1 q.2) hs.2 hls
      (by rw [hR]; exact hfR)
    rw [hR] at ih
    rw [parseQuadLinesAcc]
    rcases hr0 with hr0 | hr0 <;>
    · rw [hr0] at hp
      rw [hr0, skipWs_stop pos (by decide)]
      dsimp only
      split
      · next h => cases h
      · next h => simp at h
      · next h => simp at h
      · next h => simp at h
      · cases mode <;>
        · simp only [readNQuadOf] at hp
          simp only [hp]
          simp only [skipWs_stop _ (by decide : isNtWs '\n' = false), skipComment_nl, skipEol_nl]
          rw [ih]
          rfl

/-- **The N-Quads document round trip**, in both modes: the parser gives the
dataset that `addQuad` builds from the written quads, in order. -/
theorem parseNQuads_toNQuads (mode : Mode) (ds : Dataset) (hs : (quadsOf ds).all Quad.ntLex = true)
    (text : String) (h : Dataset.toNQuads ds mode = .ok text) :
    parseNQuads text mode = .ok (addAll Dataset.empty (quadsOf ds)) := by
  obtain ⟨ls, hls, rfl⟩ := toNQuads_lines mode ds text h
  unfold parseNQuads
  exact parseQuadLinesAcc_lines mode (quadsOf ds) ls _ 0 Dataset.empty hs hls (by omega)

/-! ## The quads of the dataset the parser gives -/

theorem addAll_isSet : ∀ (qs : List (Triple × Option Subject)) (acc : Dataset), acc.IsSet →
    (addAll acc qs).IsSet
  | [], _, h => h
  | q :: qs, acc, h => addAll_isSet qs (addQuad acc q.1 q.2) (addQuad_isSet q.1 q.2 h)

/-- RDF term membership in the result: a quad added, up to `Triple.key`. -/
theorem addAll_memQuad : ∀ (qs : List (Triple × Option Subject)) (acc : Dataset), acc.IsSet →
    ∀ u g, (addAll acc qs).memQuad u g ↔ acc.memQuad u g ∨ ∃ q ∈ qs, g = q.2 ∧ u.key = q.1.key
  | [], acc, _, u, g => by simp [addAll]
  | q :: qs, acc, h, u, g => by
    have ih := addAll_memQuad qs (addQuad acc q.1 q.2) (addQuad_isSet q.1 q.2 h) u g
    show (addAll (addQuad acc q.1 q.2) qs).memQuad u g ↔ _
    rw [ih, addQuad_memQuad q.1 q.2 h u g]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h1 | h1) | h1)
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    · rintro (h1 | h1 | h1)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h1

/-- The graph names of the result: those of the quads added. -/
theorem addAll_names : ∀ (qs : List (Triple × Option Subject)) (acc : Dataset) (m : Subject),
    m ∈ (addAll acc qs).names ↔ m ∈ acc.names ∨ ∃ q ∈ qs, q.2 = some m
  | [], acc, m => by simp [addAll]
  | q :: qs, acc, m => by
    show m ∈ (addAll (addQuad acc q.1 q.2) qs).names ↔ _
    rw [addAll_names qs _ m, addQuad_names]
    simp only [List.mem_cons, exists_eq_or_imp]
    constructor
    · rintro ((h1 | h1) | h1)
      · exact Or.inl h1
      · exact Or.inr (Or.inl h1)
      · exact Or.inr (Or.inr h1)
    · rintro (h1 | h1 | h1)
      · exact Or.inl (Or.inl h1)
      · exact Or.inl (Or.inr h1)
      · exact Or.inr h1

theorem mem_quadsOf (ds : Dataset) (q : Triple × Option Subject) :
    q ∈ quadsOf ds ↔ (q.2 = none ∧ q.1 ∈ ds.default) ∨
      ∃ ng ∈ ds.named, q.2 = some ng.name ∧ q.1 ∈ ng.graph := by
  obtain ⟨t, g⟩ := q
  simp only [quadsOf, List.mem_append, List.mem_map, List.mem_flatMap, Prod.mk.injEq]
  constructor
  · rintro (⟨u, hu, rfl, rfl⟩ | ⟨ng, hng, u, hu, rfl, rfl⟩)
    · exact Or.inl ⟨rfl, hu⟩
    · exact Or.inr ⟨ng, hng, rfl, hu⟩
  · rintro (⟨rfl, hu⟩ | ⟨ng, hng, rfl, hu⟩)
    · exact Or.inl ⟨t, hu, rfl, rfl⟩
    · exact Or.inr ⟨ng, hng, t, hu, rfl, rfl⟩

/-- **The quads of the parsed dataset are the quads of the written one**, up
to RDF term equality. -/
theorem addAll_quadsOf_memQuad (ds : Dataset) (u : Triple) (g : Option Subject) :
    (addAll Dataset.empty (quadsOf ds)).memQuad u g ↔ ds.memQuad u g := by
  rw [addAll_memQuad _ _ Dataset.isSet_empty]
  have he : ¬ Dataset.empty.memQuad u g := by
    cases g <;> simp [Dataset.empty, Dataset.memQuad, Graph.mem_iff_key]
  constructor
  · rintro (h | ⟨q, hq, hg, hk⟩)
    · exact absurd h he
    · rcases (mem_quadsOf ds q).mp hq with ⟨hq2, hq1⟩ | ⟨ng, hng, hq2, hq1⟩
      · rw [hq2] at hg; subst hg
        exact (Graph.mem_iff_key u ds.default).mpr ⟨q.1, hq1, hk.symm⟩
      · rw [hq2] at hg; subst hg
        exact ⟨ng, hng, rfl, (Graph.mem_iff_key u ng.graph).mpr ⟨q.1, hq1, hk.symm⟩⟩
  · intro h
    refine Or.inr ?_
    cases g with
    | none =>
      obtain ⟨v, hv, hk⟩ := (Graph.mem_iff_key u ds.default).mp h
      exact ⟨(v, none), (mem_quadsOf ds _).mpr (Or.inl ⟨rfl, hv⟩), rfl, hk.symm⟩
    | some n =>
      obtain ⟨ng, hng, hn, hm⟩ := h
      obtain ⟨v, hv, hk⟩ := (Graph.mem_iff_key u ng.graph).mp hm
      exact ⟨(v, some ng.name), (mem_quadsOf ds _).mpr (Or.inr ⟨ng, hng, rfl, hv⟩), by rw [hn], hk.symm⟩

/-- **The graph names of the parsed dataset** are the names of the graphs that
have a triple: an empty named graph has no line. -/
theorem addAll_quadsOf_names (ds : Dataset) (m : Subject) :
    m ∈ (addAll Dataset.empty (quadsOf ds)).names ↔ ∃ u, ds.memQuad u (some m) := by
  rw [addAll_names]
  constructor
  · rintro (h | ⟨q, hq, hg⟩)
    · simp [Dataset.empty, Dataset.names] at h
    · rcases (mem_quadsOf ds q).mp hq with ⟨hq2, -⟩ | ⟨ng, hng, hq2, hq1⟩
      · rw [hq2] at hg; cases hg
      · rw [hq2] at hg
        cases hg
        exact ⟨q.1, ng, hng, rfl, (Graph.mem_iff_key q.1 ng.graph).mpr ⟨q.1, hq1, rfl⟩⟩
  · rintro ⟨u, ng, hng, hn, hm⟩
    obtain ⟨v, hv, -⟩ := (Graph.mem_iff_key u ng.graph).mp hm
    exact Or.inr ⟨(v, some ng.name), (mem_quadsOf ds _).mpr (Or.inr ⟨ng, hng, rfl, hv⟩), by rw [hn]⟩

/-! ## Outside the domain: a graph label

A blank-node graph label outside BLANK_NODE_LABEL [141s]: `Dataset.toNQuads`
writes it as it is and the parser refuses the line. The quad is in the writer
domain `Quad.ntSafe`: the writers of `RDF/Sink.lean` relabel it first
(https://github.com/danbri/factoidal/issues/986). -/

private def cxP : WfIri := ⟨"http://example.org/p", by decide⟩
private def cxO : WfIri := ⟨"http://example.org/o", by decide⟩

private def cxDataset (g : Subject) : Dataset :=
  { default := [], named := [{ name := g, graph := [{ s := .iri cxO, p := cxP, o := .iri cxO }] }] }

private def cxParses (mode : Mode) (ds : Dataset) : Option Bool :=
  match Dataset.toNQuads ds mode with
  | .error _ => none
  | .ok text => some (parseNQuads text mode).toOption.isSome

#guard (quadsOf (cxDataset (.bnode "g 1"))).all Quad.ntLex == false
#guard (quadsOf (cxDataset (.bnode "g 1"))).all Quad.ntSafe
#guard cxParses .rdf11 (cxDataset (.bnode "g 1")) == some false
#guard (quadsOf (cxDataset (.bnode "g1"))).all Quad.ntLex
#guard cxParses .rdf11 (cxDataset (.bnode "g1")) == some true
#guard cxParses .rdf12 (cxDataset (.bnode "g1")) == some true

#print axioms quadsOf_renameBnodes
#print axioms Quad.ntLex_renameBnodes
#print axioms readGraphLabel_safe
#print axioms readNQuad11_line
#print axioms readNQuad12_line
#print axioms toNQuads_lines
#print axioms parseNQuads_toNQuads
#print axioms addAll_memQuad
#print axioms addAll_names
#print axioms addAll_quadsOf_memQuad
#print axioms addAll_quadsOf_names

end L4Factoidal.Syntax.NQuadsRoundTrip
