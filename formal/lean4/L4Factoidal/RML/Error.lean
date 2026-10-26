/-
L4Factoidal.RML.Error — why a mapping run is rejected.

Spec: RML-Core, "Generated RDF Term of a Term Map" (a term map evaluates
to nothing, a term, or a DATA ERROR) and the MUST clauses of "Mapping to
RDF with Triples Maps", "Term Maps", "Generating values with
expressions" and "Joins".

Three kinds of rejection, kept apart because they are found at different
times and a caller treats them differently:

* `mapping` — the mapping graph breaks a MUST clause. Found without
  reading any source, by `RML.Validate`.
* `source`  — a logical source cannot be opened or is not well formed
  (a missing file, a CSV row of the wrong width, an invalid iterator).
* `data`    — evaluation reached a value from which no valid RDF term can
  be built (a string that is not an IRI where an IRI is required, an
  ill-formed language tag, an ill-typed literal, a reference that selects
  a whole array).

An RML-Core conformance test with `error=true` expects the processor to
reject the mapping; it does not say which of the three, so the runner
counts any of them as a rejection.
-/

namespace L4Factoidal.RML

inductive ErrorKind where
  | mapping | source | data
  /-- Not a rejection of the mapping: the mapping needs something this
      port does not have (a database, a compression codec, a function).
      The run is not scored, and `bucket` says what is missing. -/
  | unsupported
deriving Repr, DecidableEq, Inhabited

structure RmlError where
  kind    : ErrorKind
  /-- The triples map (or other node) the rejection is about. -/
  site    : String
  /-- The specification clause the rejection enforces, quoted briefly. -/
  clause  : String
  message : String
  /-- For an `unsupported` error, the name of what is missing; the
      runner groups unattempted cases by it. -/
  bucket  : String := ""
deriving Repr, Inhabited

def RmlError.mapping (site clause message : String) : RmlError :=
  { kind := .mapping, site := site, clause := clause, message := message }

def RmlError.source (site clause message : String) : RmlError :=
  { kind := .source, site := site, clause := clause, message := message }

def RmlError.data (site clause message : String) : RmlError :=
  { kind := .data, site := site, clause := clause, message := message }

def RmlError.unsupported (site clause bucket message : String) : RmlError :=
  { kind := .unsupported, site := site, clause := clause, message := message, bucket := bucket }

def ErrorKind.label : ErrorKind → String
  | .mapping => "mapping"
  | .source  => "source"
  | .data    => "data"
  | .unsupported => "unsupported"

/-- One line a human can read: kind, site, message, clause. -/
def RmlError.render (e : RmlError) : String :=
  s!"{e.kind.label} error at {e.site}: {e.message} [{e.clause}]"

end L4Factoidal.RML
