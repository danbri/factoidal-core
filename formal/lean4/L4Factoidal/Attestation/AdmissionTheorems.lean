/- Admission discharges the positive-rule semantic hypotheses, issue #745. -/
import L4Factoidal.Attestation.Policy
import L4Factoidal.SPARQLRL.SemiNaiveTheorems

namespace L4Factoidal.Attestation

open SPARQL SPARQLRL

/-- Name separation theorem.
Says: for the plain terms used by this profile, a successful collision
check separates rewritten blank-node names from explicit user variables.
Does not say: the rewrite is fresh for arbitrary unrestricted queries. -/
theorem bnodeRewriteSafe_disjoint {patterns : Bgp} (h : bnodeRewriteSafe patterns = true)
    {name : String} (hb : name ∈ patterns.flatMap triplePatternBnodeVariables) :
    name ∉ patterns.flatMap triplePatternVariables := by
  simp only [bnodeRewriteSafe, Bool.not_eq_true', List.any_eq_false] at h
  have separate := h name hb
  simpa using separate

/-- Concrete ASK admission theorem.
Says: the actual admitted pattern has passed the blank-node/user-variable
collision check on every triple in its admitted basic pattern joins.
Does not say: the general query engine admits this safety condition. -/
theorem AdmittedPolicy.bnodeRewriteSafe (p : AdmittedPolicy) :
    ∃ patterns, basicPatterns 64 p.query.pattern = some patterns ∧
      bnodeRewriteSafe patterns = true := by
  have h := p.askAccepted
  simp only [admittedAsk, Bool.and_eq_true] at h
  have hp := h.2
  cases hb : basicPatterns 64 p.query.pattern with
  | none => simp [hb] at hp
  | some patterns =>
      simp only [hb, Bool.and_eq_true] at hp
      exact ⟨patterns,rfl,hp.2⟩

/-- Admission provenance theorem.
Says: successful admission retains the exact supplied source policy,
including text, entailment regime and every resource bound.
Does not say: two textually different policies have different hashes. -/
theorem admitPolicy_source {source : Policy} {admitted : AdmittedPolicy}
    (h : admitPolicy source = .ok admitted) : admitted.source = source := by
  by_cases hl : (!source.limits.valid) = true
  · simp [admitPolicy,hl,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at h
  · by_cases hb : source.query.utf8ByteSize + source.rules.utf8ByteSize > source.limits.maxPolicyBytes
    · simp [admitPolicy,hl,hb,bind,Except.bind,throw,throwThe,MonadExceptOf.throw] at h
    · cases hparse : SPARQL.parseSparqlWith 256 source.query none .v11 with
      | error err => simp [admitPolicy,hl,hb,hparse,bind,Except.bind,Except.mapError] at h
      | ok q =>
        by_cases hq : admittedAsk source.limits q = true
        · cases hrparse : parseRuleSet source.rules with
          | error err =>
              simp [admitPolicy,hl,hb,hparse,hq,hrparse,bind,Except.bind,Except.mapError] at h
          | ok rs =>
              by_cases hr : admittedRules source.limits rs = true
              · simp [admitPolicy,hl,hb,hparse,hq,hrparse,hr,bind,Except.bind,
                  Except.mapError,pure,Except.pure] at h
                cases h
                rfl
              · simp [admitPolicy,hl,hb,hparse,hq,hrparse,hr,bind,Except.bind,
                  Except.mapError,throw,throwThe,MonadExceptOf.throw] at h
        · simp [admitPolicy,hl,hb,hparse,hq,bind,Except.bind,Except.mapError,
            throw,throwThe,MonadExceptOf.throw] at h

/-- Structural admission lemma.
Says: plain terms contain no head blank nodes or variable triple terms.
Does not say: every position of a generalised triple is an RDF position. -/
private theorem plainTerm_properties {t : STerm} (h : plainRuleTerm t = true) :
    t.bnodes = [] ∧ t.hasVarTripleTerm = false := by
  cases t <;> simp_all [plainRuleTerm, STerm.bnodes, STerm.hasVarTripleTerm]

/-- Structural admission lemma.
Says: a plain head triple has neither of the run-once head features.
Does not say: its instantiated predicate is always an IRI. -/
private theorem plainTriple_properties {t : STriple} (h : plainRuleTriple t = true) :
    t.bnodes = [] ∧ t.hasVarTripleTerm = false := by
  simp only [plainRuleTriple, Bool.and_eq_true] at h
  obtain ⟨hs, hs'⟩ := plainTerm_properties h.1.1
  obtain ⟨hp, hp'⟩ := plainTerm_properties h.1.2
  obtain ⟨ho, ho'⟩ := plainTerm_properties h.2
  simp [STriple.bnodes, STriple.hasVarTripleTerm, hs,hp,ho,hs',hp',ho']

/-- Structural admission lemma.
Says: a triple-only body has no nested run-once feature.
Does not say: its fixed point has already been reached. -/
private theorem positiveBody_not_once {body : List Elt}
    (h : body.all (fun e => match e with
      | .triple t => plainRuleTriple t | _ => false) = true) :
    Elt.listMakesRunOnce body = false := by
  induction body with
  | nil => rfl
  | cons e es ih =>
      simp only [List.all_cons, Bool.and_eq_true] at h
      have htail := ih h.2
      cases e <;> simp_all [Elt.listMakesRunOnce, Elt.makesRunOnce]

/-- Semantic admission theorem.
Says: the admitted positive finite-term shape has no run-once rule. The
existing engine's general-rule saturation theorems therefore apply to
this part of admission without an additional caller assertion.
Does not say: every SPARQL-RL rule is in this restricted profile. -/
theorem positiveRule_general {l : Limits} {r : Rule} (h : positiveRule l r = true) :
    r.runOnce = false := by
  simp only [positiveRule, Bool.and_eq_true] at h
  have hbody := positiveBody_not_once h.2
  have hhead : r.head.any (fun t => !t.bnodes.isEmpty || t.hasVarTripleTerm) = false := by
    apply List.any_eq_false.mpr
    intro t ht
    obtain ⟨hb, hv⟩ := plainTriple_properties (List.all_eq_true.mp h.1.2 t ht)
    simp [hb,hv]
  simp [Rule.runOnce,hbody,hhead]

/-- Admission projection lemma.
Says: every concrete rule in an admitted policy passes positiveRule.
Does not say: the admitted policy is authorised by a verifier. -/
private theorem admittedRules_positive (p : AdmittedPolicy) :
    ∀ r ∈ p.rules.rules, positiveRule p.source.limits r = true := by
  have h := p.rulesAccepted
  simp only [admittedRules, Bool.and_eq_true] at h
  exact List.all_eq_true.mp h.1.1.1.2

/-- Concrete policy admission theorem.
Says: each actual rule in an admitted policy is a general rule under the
existing SPARQL-RL classifier, including the nested body/head checks.
Does not say: the caller selected an authorised eligibility rule set. -/
theorem AdmittedPolicy.rules_general (p : AdmittedPolicy) :
    ∀ r ∈ p.rules.rules, r.runOnce = false := by
  intro r hr
  exact positiveRule_general (admittedRules_positive p r hr)

/-- Concrete policy admission theorem.
Says: the admitted rule set has no open negation, which discharges the
existing general-loop least-fixed-point theorem's NegBlind hypothesis.
Does not say: the RDFS-then-rules composition is one combined closure. -/
theorem AdmittedPolicy.rules_negBlind (p : AdmittedPolicy) :
    SPARQLRL.NegBlind p.rules.rules := by
  intro r hr inner hneg
  have h := admittedRules_positive p r hr
  simp only [positiveRule, Bool.and_eq_true] at h
  have impossible := List.all_eq_true.mp h.2 (.neg true inner) hneg
  simp at impossible

/-- Concrete policy validation theorem.
Says: admitted rules pass the engine's actual well-formedness and
stratifiability validators before evaluation.
Does not say: arbitrary rule sources are accepted or an invalid policy
is a successful false result. -/
theorem AdmittedPolicy.rules_validated (p : AdmittedPolicy) :
    p.rules.wellFormed = true ∧ p.rules.stratifiable = true := by
  have h := p.rulesAccepted
  simp only [admittedRules, Bool.and_eq_true] at h
  exact ⟨h.1.1.2,h.1.2⟩

#print axioms positiveRule_general
#print axioms bnodeRewriteSafe_disjoint
#print axioms AdmittedPolicy.bnodeRewriteSafe
#print axioms admitPolicy_source
#print axioms AdmittedPolicy.rules_general
#print axioms AdmittedPolicy.rules_negBlind
#print axioms AdmittedPolicy.rules_validated

end L4Factoidal.Attestation
