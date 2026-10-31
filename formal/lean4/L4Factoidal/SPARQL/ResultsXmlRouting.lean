/-
Checked SRX admission at the XQuery XML parser boundary. The evidence concerns
acceptance of these exact serialized characters by this parser, without assuming namespace well-formedness. It does not establish SRX schema validity, RDF round trips,
XML character preservation through parsing, or acceptance by another processor.
The serializer is unchanged: refusal never sanitizes RDF lexical data.
-/
import L4Factoidal.SPARQL.ResultsXml
import L4Factoidal.XPath4.Doc
import L4Factoidal.Dataflow.Conditional

namespace L4Factoidal.SPARQL

/-- The actual public XPath/XQuery context-document admission boundary.
`Doc.ofString` uses XML.parseXML and constructs the XDM document. It does not
check namespace well-formedness; this certificate does not add that claim. -/
def parseSrxDocument (text : String) : Except String XPath4.Doc :=
  XPath4.Doc.ofString text

/-- An accepted exact serialization with parser evidence, or its parser refusal.
The public diagnostic code is XML_ADMISSION_REFUSED; the original parser diagnostic
remains available in `error`. -/
inductive SrxReport where
  | xml (text : String) (doc : XPath4.Doc)
      (accepted : parseSrxDocument text = .ok doc)
  | diagnostic (error : String)

/-- Accepted text only; diagnostics never carry a substitute serialization. -/
def SrxReport.xml? : SrxReport → Option String
  | .xml text _ _ => some text
  | .diagnostic _ => none

/-- Successful reports retain the original text; refusal is the actual parser error. -/
def SrxReport.agrees (text : String) : SrxReport → Prop
  | .xml emitted _ _ => emitted = text
  | .diagnostic error => parseSrxDocument text = .error error

/-- A cached parse is tied to its exact input, even when constructed externally. -/
structure SrxAdmissionInput where
  text : String
  parsed : Except String XPath4.Doc
  parsed_eq : parseSrxDocument text = parsed

namespace SrxAdmissionInput

def accepted (input : SrxAdmissionInput) : Prop := input.parsed.isOk = true
instance : DecidablePred accepted := fun input =>
  inferInstanceAs (Decidable (input.parsed.isOk = true))

/-- No parser is invoked here: the cached success supplies both document and proof. -/
def admit (input : { i : SrxAdmissionInput // i.accepted }) : SrxReport :=
  match outcome : input.val.parsed with
  | .ok doc => .xml input.val.text doc (input.val.parsed_eq.trans outcome)
  | .error _ => False.elim (by simpa [accepted, outcome, Except.isOk, Except.toBool] using input.property)

/-- The cached failure is returned without rewriting the original RDF value. -/
def refuse (input : { i : SrxAdmissionInput // ¬ i.accepted }) : SrxReport :=
  match outcome : input.val.parsed with
  | .error error => .diagnostic error
  | .ok _ => False.elim (input.property (by simp [accepted, outcome, Except.isOk, Except.toBool]))

private def admitStage : Dataflow.Stage Empty { i : SrxAdmissionInput // i.accepted } SrxReport :=
  Dataflow.Stage.ofFun admit (fun input report => report.agrees input.val.text) (by
    intro input
    unfold admit
    split
    · rfl
    · rename_i error outcome
      exact False.elim (by simpa [accepted, outcome, Except.isOk, Except.toBool] using input.property))

private def refuseStage : Dataflow.Stage Empty { i : SrxAdmissionInput // ¬ i.accepted } SrxReport :=
  Dataflow.Stage.ofFun refuse (fun input report => report.agrees input.val.text) (by
    intro input
    unfold refuse
    split
    · rename_i error outcome
      exact input.val.parsed_eq.trans outcome
    · rename_i doc outcome
      exact False.elim (input.property (by simp [accepted, outcome, Except.isOk, Except.toBool])))

/-- The production branch selection is the shared conditional Stage operation. -/
def stage : Dataflow.Stage Empty SrxAdmissionInput SrxReport :=
  Dataflow.Stage.choose accepted admitStage refuseStage

end SrxAdmissionInput

/-- Serialize once, parse once, then route that exact cached outcome. -/
def QueryResult.toSrxReport (result : QueryResult) : SrxReport :=
  let text := result.toSrx
  let input : SrxAdmissionInput := ⟨text, parseSrxDocument text, rfl⟩
  match SrxAdmissionInput.stage.run input with
  | .ok report => report
  | .error impossible => nomatch impossible

/-- The selected production branch preserves exact serialization or its real refusal. -/
theorem QueryResult.toSrxReport_agrees (result : QueryResult) :
    result.toSrxReport.agrees result.toSrx := by
  unfold QueryResult.toSrxReport
  dsimp only
  generalize input_eq : (SrxAdmissionInput.mk result.toSrx
    (parseSrxDocument result.toSrx) rfl) = input
  cases run_eq : SrxAdmissionInput.stage.run input with
  | error impossible => exact Empty.elim impossible
  | ok report =>
    have contract := SrxAdmissionInput.stage.sound input report run_eq
    obtain ⟨admission, contract⟩ := contract
    have same : input.text = result.toSrx := by subst input; rfl
    cases admission <;>
      simpa [Dataflow.Stage.Routed.contract, SrxAdmissionInput.admitStage,
        SrxAdmissionInput.refuseStage, Dataflow.Stage.ofFun, same] using contract

/-- An admitted result is exactly the original serialization. -/
theorem QueryResult.toSrxReport_exact (result : QueryResult) (text : String)
    (doc : XPath4.Doc) (accepted : parseSrxDocument text = .ok doc)
    (reported : result.toSrxReport = .xml text doc accepted) : text = result.toSrx := by
  have contract := result.toSrxReport_agrees
  rw [reported] at contract
  exact contract

/-- Observing accepted public text yields parser evidence and original-text identity. -/
theorem QueryResult.toSrxReport_accepted (result : QueryResult) (text : String)
    (reported : result.toSrxReport.xml? = some text) :
    ∃ doc, XPath4.Doc.ofString text = .ok doc ∧ text = result.toSrx := by
  cases report_eq : result.toSrxReport with
  | diagnostic error => simp [report_eq, SrxReport.xml?] at reported
  | xml emitted doc accepted =>
    have same : emitted = text := by simpa [report_eq, SrxReport.xml?] using reported
    subst text
    exact ⟨doc, accepted, result.toSrxReport_exact emitted doc accepted report_eq⟩

/-- A refusal carries the actual context parser's failure on the original text. -/
theorem QueryResult.toSrxReport_refused (result : QueryResult) (error : String)
    (reported : result.toSrxReport = .diagnostic error) :
    parseSrxDocument result.toSrx = .error error := by
  have contract := result.toSrxReport_agrees
  rw [reported] at contract
  exact contract

end L4Factoidal.SPARQL
