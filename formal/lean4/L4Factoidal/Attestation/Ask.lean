/-
The actual checked ASK attestation computation.
Tracking: https://github.com/danbri/factoidal-core/issues/745.

No proof system is implemented here. This is the deterministic computation
that a pinned proof guest must execute. Its result contains only three
commitments and the successful Boolean; every failure has no journal.
-/
import L4Factoidal.Attestation.Policy
import L4Factoidal.Syntax.NTriples
import L4Factoidal.RDF.GraphSet
import L4Factoidal.RDFS.Checked
import L4Factoidal.SPARQLRL.Checked

namespace L4Factoidal.Attestation

open RDF SPARQL

def rdfsError : RDFS.Checked.Error → Error
  | .exhausted => .exhausted "RDFS"
  | .tripleLimit => .resourceLimit "RDFS triples"

def rulesError : SPARQLRL.Checked.Error → Error
  | .infer _ => .invalidPolicy "SPARQL-RL validation"
  | .exhausted => .exhausted "SPARQL-RL"
  | .tripleLimit => .resourceLimit "SPARQL-RL triples"

/-- Ordered RDFS-then-rules. This is not a combined closure: assertions
introduced by a rule are not subsequently fed back through RDFS. -/
def checkedPhases (p : AdmittedPolicy) (input : Graph) : Except Error Graph := do
  let l := p.source.limits
  let closed ← match p.source.entailment with
    | .simple => pure input
    | .rdfsFull => (RDFS.Checked.fullClosure
        ⟨l.maxRdfsRounds,l.maxTriples⟩ [] (containerVocabulary p input) input).mapError rdfsError
  let full ← (SPARQLRL.Checked.evalGraph
    ⟨l.maxRuleRounds,l.maxTriples⟩ p.rules closed {}).mapError rulesError
  pure full.toSet

/-- Private intermediate result. Only its Boolean reaches the public
journal; the graph and parsed policy do not leave the prover. -/
structure Evaluation where
  policy : AdmittedPolicy
  graph : Graph
  satisfied : Bool
  answer_eq : satisfied = evalAsk {} ⟨graph,[]⟩ policy.query

def evaluate (p : Policy) (originalBytes : ByteArray) : Except Error Evaluation := do
  let admitted ← admitPolicy p
  if originalBytes.size > p.limits.maxInputBytes then
    throw (.resourceLimit "input bytes")
  let text ← match String.fromUTF8? originalBytes with
    | some s => pure s
    | none => throw (.invalidInput "invalid UTF-8")
  let parsed ← (Syntax.parseNTriples text .rdf11).mapError
    (fun _ => Error.invalidInput "N-Triples syntax")
  let input := parsed.toSet
  if input.length > p.limits.maxTriples then throw (.resourceLimit "input triples")
  let result ← checkedPhases admitted input
  let patterns := (basicPatterns 64 admitted.query.pattern).getD []
  let queryWork := result.length ^ patterns.length * (patterns.length + 1)
  if queryWork > p.limits.maxIntermediate then throw (.resourceLimit "ASK intermediate bindings")
  pure ⟨admitted, result, evalAsk {} ⟨result,[]⟩ admitted.query, rfl⟩

/-- Hash a completed result. Reject failed/wrong-length digests instead of
creating stale or zero output. The policy bytes come from the exact
admitted source, including evaluation order and every resource limit. -/
def makeJournal (hash : ByteArray → ByteArray) (e : Evaluation)
    (salt originalBytes context : ByteArray) : Except Error Journal := do
  let graphCommitment ← hash32 hash (graphMessage salt originalBytes)
  let policyHash ← hash32 hash (policyMessage e.policy.source.encode)
  let contextHash ← hash32 hash (contextMessage context)
  pure ⟨graphCommitment,policyHash,contextHash,e.satisfied⟩

/-- Single checked entry point. Salt entropy and application authorization
are external obligations. The host supplies a fresh CSPRNG salt; a proof
cannot establish where it was generated or that the data is authentic. -/
def attest (hash : ByteArray → ByteArray) (p : Policy)
    (salt originalBytes context : ByteArray) : Except Error Journal := do
  if salt.size != 32 then throw (.invalidInput "salt must have 32 bytes")
  if context.size > p.limits.maxContextBytes then throw (.resourceLimit "context bytes")
  let result ← evaluate p originalBytes
  makeJournal hash result salt originalBytes context

/-- The portable v1 request ABI. Regime 0 is simple, regime 1 is ordered
full-RDFS-then-rules. Other codes are errors. Policy strings must be strict
UTF-8; all default v1 limits are included in the policy hash. Byte and
policy bounds are checked before decoding, parsing or hashing. -/
def attestRequest (hash : ByteArray → ByteArray)
    (originalBytes salt query rules context : ByteArray) (regime : UInt8) : Except Error Journal := do
  let limits : Limits := {}
  if query.size + rules.size > limits.maxPolicyBytes then
    throw (.resourceLimit "policy bytes")
  let entailment ← match regime with
    | 0 => pure Entailment.simple
    | 1 => pure Entailment.rdfsFull
    | _ => throw (.invalidPolicy "unknown entailment regime")
  let queryText ← match String.fromUTF8? query with
    | some text => pure text
    | none => throw (.invalidPolicy "query UTF-8")
  let rulesText ← match String.fromUTF8? rules with
    | some text => pure text
    | none => throw (.invalidPolicy "rules UTF-8")
  attest hash { query := queryText, rules := rulesText, entailment, limits }
    salt originalBytes context

/-- Semantic connection theorem.
Says: every completed evaluation answers the existing engine's ASK query
on its complete checked output graph, with the empty host environment.
Does not say: the parser, closure implementation or compiler has universal
standards conformance, or that a device has proved this execution. -/
theorem Evaluation.answer (e : Evaluation) :
    e.satisfied = evalAsk {} ⟨e.graph,[]⟩ e.policy.query := e.answer_eq

/-- Publication isolation theorem.
Says: an evaluator failure cannot yield a public journal from attest.
Does not say: a caller has used the intended policy or an authorised context. -/
theorem attest_of_evaluate_error (hash : ByteArray → ByteArray) (p : Policy)
    (salt originalBytes context : ByteArray) (e : Error)
    (hs : salt.size = 32) (hc : context.size ≤ p.limits.maxContextBytes)
    (he : evaluate p originalBytes = .error e) :
    attest hash p salt originalBytes context = .error e := by
  simp [attest, hs, Nat.not_lt_of_ge hc, he, bind, Except.bind]

/-- Result preservation theorem.
Says: successful sealing carries exactly the computed Boolean, including
successful false. It cannot replace a failure with false.
Does not say: hashes are collision resistant or the FFI implements SHA-256. -/
theorem makeJournal_satisfied (hash : ByteArray → ByteArray) (e : Evaluation)
    (salt originalBytes context : ByteArray) (j : Journal)
    (h : makeJournal hash e salt originalBytes context = .ok j) :
    j.satisfied = e.satisfied := by
  unfold makeJournal at h
  cases hg : hash32 hash (graphMessage salt originalBytes) with
  | error err => simp [hg, bind, Except.bind] at h
  | ok g =>
    cases hp : hash32 hash (policyMessage e.policy.source.encode) with
    | error err => simp [hg,hp, bind, Except.bind] at h
    | ok p =>
      cases hc : hash32 hash (contextMessage context) with
      | error err => simp [hg,hp,hc, bind, Except.bind] at h
      | ok c =>
        simp [hg,hp,hc, bind, Except.bind, pure, Except.pure] at h
        subst j
        rfl

#print axioms Evaluation.answer
#print axioms attest_of_evaluate_error
#print axioms makeJournal_satisfied

end L4Factoidal.Attestation
