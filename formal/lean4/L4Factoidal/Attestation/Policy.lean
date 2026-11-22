/-
Admission of the first deterministic ASK attestation profile.
Tracking: https://github.com/danbri/factoidal-core/issues/745.

The profile is RDF 1.1 N-Triples, SPARQL 1.1 basic-pattern ASK, and
positive, finite-term SPARQL-RL rules. RDFS means the existing Factoidal
`FullClosure` rule/axiom table with an empty optional datatype map and a
finite container-membership vocabulary selected from all input/policy
constants. Its current table includes RDF 1.2 axioms; this profile does
not relabel that table as a complete RDF 1.1 model-theoretic procedure.
The composition is RDFS first, rules second, rather than their combined
least fixpoint. The source text and all limits are part of the policy hash.
-/
import L4Factoidal.Attestation.Encoding
import L4Factoidal.SPARQL.Parser
import L4Factoidal.SPARQL.Query
import L4Factoidal.SPARQLRL.Parser
import L4Factoidal.RDFS.FullClosure

namespace L4Factoidal.Attestation

open RDF SPARQL SPARQLRL

inductive Entailment where
  | simple
  | rdfsFull
  deriving Repr, DecidableEq

/-- All limits are authenticated policy fields. Join work is checked
conservatively before calling the existing unbounded join evaluators. -/
structure Limits where
  maxInputBytes : Nat := 65536
  maxPolicyBytes : Nat := 16384
  maxContextBytes : Nat := 4096
  maxTriples : Nat := 256
  maxPatterns : Nat := 4
  maxRules : Nat := 16
  maxRdfsRounds : Nat := 32
  maxRuleRounds : Nat := 32
  maxIntermediate : Nat := 1000000
  deriving Repr, DecidableEq

def Limits.valid (l : Limits) : Bool :=
  l.maxInputBytes ≤ 1048576 && l.maxPolicyBytes ≤ 65536 &&
  l.maxContextBytes ≤ 65536 && 0 < l.maxTriples && l.maxTriples ≤ 4096 &&
  l.maxPatterns ≤ 8 && l.maxRules ≤ 32 && l.maxRdfsRounds ≤ 128 &&
  l.maxRuleRounds ≤ 128 && 0 < l.maxIntermediate && l.maxIntermediate ≤ 1000000

structure Policy where
  entailment : Entailment := .simple
  query : String
  rules : String := ""
  limits : Limits := {}
  deriving Repr, DecidableEq

/-- Every encoded integer is admitted below 2^31. Strings are UTF-8 with
8-byte lengths. Textually different but equivalent policies have different
messages. The constant identifies syntax, seed, vocabulary and evaluation
order; a semantics change requires a new version. -/
def Policy.encode (p : Policy) : ByteArray :=
  let l := p.limits
  let tag : UInt8 := match p.entailment with | .simple => 0 | .rdfsFull => 1
  let header := domain "factoidal.ask.ordered-nt11-bgp11-positive-rl-fullseed-v1"
  let limits := [l.maxInputBytes,l.maxPolicyBytes,l.maxContextBytes,l.maxTriples,
    l.maxPatterns,l.maxRules,l.maxRdfsRounds,l.maxRuleRounds,l.maxIntermediate]
  let encodedLimits := limits.foldl (fun out n => out ++ u64be n) (header.push tag)
  encodedLimits ++ lengthPrefixed p.query.toUTF8 ++ lengthPrefixed p.rules.toUTF8

def plainPatternTerm : PatternTerm → Bool
  | .tripleTerm _ _ _ => false
  | _ => true

def plainPatternSubject : PatternSubject → Bool
  | .tripleTerm _ _ _ => false
  | _ => true

def plainTriplePattern (t : TriplePattern) : Bool :=
  plainPatternSubject t.s && plainPatternTerm t.p && plainPatternTerm t.o

def patternTermVariables : PatternTerm → List String
  | .var name => [name]
  | _ => []

def patternSubjectVariables : PatternSubject → List String
  | .var name => [name]
  | _ => []

def triplePatternVariables (t : TriplePattern) : List String :=
  patternSubjectVariables t.s ++ patternTermVariables t.p ++ patternTermVariables t.o

/-- Names introduced by the actual ASK evaluator's blank-node rewrite.
Do not reproduce its naming convention in a second evaluator. -/
def patternTermBnodeVariables (t : PatternTerm) : List String :=
  match t with
  | .bnode _ => patternTermVariables (rewriteBnodeTerm t)
  | _ => []

def patternSubjectBnodeVariables (t : PatternSubject) : List String :=
  match t with
  | .bnode _ => patternSubjectVariables (rewriteBnodeSubject t)
  | _ => []

def triplePatternBnodeVariables (t : TriplePattern) : List String :=
  patternSubjectBnodeVariables t.s ++ patternTermBnodeVariables t.p ++ patternTermBnodeVariables t.o

/-- The existing rewrite uses variable names that a user can also write.
Refuse collisions until the general query engine uses fresh names. Normal
blank-node patterns and normal user variables remain admitted. The parser
separately checks user blank-node label scope across nested groups. -/
def bnodeRewriteSafe (patterns : Bgp) : Bool :=
  let userVariables := patterns.flatMap triplePatternVariables
  !(patterns.flatMap triplePatternBnodeVariables).any userVariables.contains

/-- At most 64 nested pattern constructors, already below the parser's
fuel bound. Expressions, paths, subqueries, graph clauses and services
are refused instead of being silently evaluated in an empty environment. -/
def basicPatterns : Nat → QueryPattern → Option Bgp
  | 0, _ => none
  | _ + 1, .empty => some []
  | _ + 1, .bgp ts => if ts.all plainTriplePattern then some ts else none
  | n + 1, .join left right => do
      let a ← basicPatterns n left
      let b ← basicPatterns n right
      pure (a ++ b)
  | _, _ => none

def queryIsAsk : Query → Bool
  | .mk .ask _ _ _ _ _ _ _ => true
  | _ => false

def modifiersEmpty (m : SolutionModifier) : Bool :=
  m.orderBy.isNone && !m.distinct && !m.reduced && m.offset.isNone && m.limit.isNone

def admittedAsk (l : Limits) (q : Query) : Bool :=
  queryIsAsk q && q.dataset.isEmpty && q.groupBy.isNone && q.having.isEmpty &&
  modifiersEmpty q.modifier && q.postValues.isNone &&
  match basicPatterns 64 q.pattern with
  | none => false
  | some ts => ts.length ≤ l.maxPatterns && bnodeRewriteSafe ts

def plainRuleTerm : STerm → Bool
  | .var _ | .iri _ | .lit _ => true
  | _ => false

def plainRuleTriple (t : STriple) : Bool :=
  plainRuleTerm t.s && plainRuleTerm t.p && plainRuleTerm t.o

def positiveRule (l : Limits) (r : Rule) : Bool :=
  r.head.length ≤ l.maxPatterns && r.body.length ≤ l.maxPatterns &&
  r.head.all plainRuleTriple && r.body.all (fun e =>
    match e with | .triple t => plainRuleTriple t | _ => false)

/-- A conservative bound on one round's candidate bindings and emitted
heads. This protects the current joins before they allocate intermediate
solutions; it is intentionally stricter than an indexed-data estimate. -/
def ruleRoundBound (l : Limits) (rs : RuleSet) : Nat :=
  rs.rules.foldl (fun work r =>
    work + (l.maxTriples ^ r.body.length) * (r.head.length + 1) * (r.body.length + 1)) 0

def admittedRules (l : Limits) (rs : RuleSet) : Bool :=
  rs.imports.isEmpty && rs.data.isEmpty && rs.rules.length ≤ l.maxRules &&
  rs.rules.all (positiveRule l) && rs.wellFormed && rs.stratifiable &&
  ruleRoundBound l rs ≤ l.maxIntermediate

structure AdmittedPolicy where
  source : Policy
  query : Query
  rules : RuleSet
  askAccepted : admittedAsk source.limits query = true
  rulesAccepted : admittedRules source.limits rules = true

def admitPolicy (p : Policy) : Except Error AdmittedPolicy := do
  if !p.limits.valid then throw (.invalidPolicy "invalid resource limits")
  if p.query.utf8ByteSize + p.rules.utf8ByteSize > p.limits.maxPolicyBytes then
    throw (.resourceLimit "policy bytes")
  let q ← (parseSparqlWith 256 p.query none .v11).mapError
    (fun _ => Error.invalidPolicy "SPARQL 1.1 query syntax")
  if hq : admittedAsk p.limits q = true then
    let rs ← (parseRuleSet p.rules).mapError
      (fun _ => Error.invalidPolicy "SPARQL-RL syntax")
    if hr : admittedRules p.limits rs = true then
      return ⟨p, q, rs, hq, hr⟩
    else throw (.invalidPolicy "rules outside positive finite-term profile or work bound")
  else throw (.invalidPolicy "query outside basic-pattern ASK profile")

/-- Admission theorem.
Says: the concrete admitted query is an ASK query; a SELECT cannot produce
a normal false by reaching evalAsk's fallback branch.
Does not say: the ASK policy is authorised by a relying application. -/
theorem AdmittedPolicy.isAsk (p : AdmittedPolicy) : queryIsAsk p.query = true := by
  have h := p.askAccepted
  simp only [admittedAsk, Bool.and_eq_true] at h
  exact h.1.1.1.1.1.1

def patternTermIris : PatternTerm → List WfIri
  | .iri i => [i]
  | _ => []

def patternSubjectIris : PatternSubject → List WfIri
  | .iri i => [i]
  | _ => []

def ruleTermIris : STerm → List WfIri
  | .iri i => [i]
  | _ => []

/-- Input and policy IRIs determine the finite rdf:_n slice. No outside
vocabulary, network import or hidden default graph participates. -/
def containerVocabulary (p : AdmittedPolicy) (g : Graph) : List WfIri :=
  let patterns := (basicPatterns 64 p.query.pattern).getD []
  let qi := patterns.flatMap (fun t =>
    patternSubjectIris t.s ++ patternTermIris t.p ++ patternTermIris t.o)
  let ruleIris := p.rules.rules.flatMap (fun r =>
    let ts := r.head ++ r.body.filterMap (fun e => match e with | .triple t => some t | _ => none)
    ts.flatMap (fun t => ruleTermIris t.s ++ ruleTermIris t.p ++ ruleTermIris t.o))
  let all := RDFS.containerMembershipIn g ++ (qi ++ ruleIris).flatMap RDFS.cmpOfIri
  all.foldl (fun out i => if out.contains i then out else out ++ [i]) []

#print axioms AdmittedPolicy.isAsk

end L4Factoidal.Attestation
