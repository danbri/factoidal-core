import L4Factoidal.CSVW.Conversion
import L4Factoidal.CSVW.JsonDoc
import L4Factoidal.CSVW.Validate

namespace L4Factoidal.CSVW.RegexFormatTests

private def runFormat (base pat text : String) :=
  formatConvert base (some pat) none none none text

#guard runFormat "string" "^a$" "a" == .valid "a"
#guard runFormat "string" "^a$" "b" == .invalid
#guard runFormat "string" "a" "cat" == .valid "cat"
#guard runFormat "string" "^\\s$" (String.singleton (Char.ofNat 0xA0)) ==
  .valid (String.singleton (Char.ofNat 0xA0))
#guard runFormat "string" "^.$" (String.singleton (Char.ofNat 0x2028)) == .invalid
#guard runFormat "html" "^<p>" "<p>text" == .valid "<p>text"
#guard runFormat "json" "^x$" "{}" == .invalid
#guard runFormat "duration" "^P" "P1D" == .valid "P1D"
#guard runFormat "duration" "[" "P1D" == .valid "P1D"
#guard runFormat "duration" "[" "bad" == .invalid
#guard runFormat "dayTimeDuration" ".*" "P1Y" == .invalid
#guard runFormat "yearMonthDuration" ".*" "P1D" == .invalid

private def datatype (base pat : String) : Datatype :=
  .object (some base) (some pat) none none none none
    none none none none none none none none none

private def prepared (base pat text : String) :=
  prepareLexical (some (datatype base pat)) text

#guard (prepared "string" "[" "x").value == ("x", true)
#guard (prepared "string" "[" "x").issues.map (·.kind) == [.warning]
#guard (prepared "duration" "[" "bad").issues.map (·.kind) == [.warning, .invalidValue]
#guard (prepared "string" "(?=a)a" "a").issues.map (·.kind) == [.unsupported]
#guard (prepared "string" "." "😀").issues.map (·.kind) == [.unsupported]
#guard (prepared "string" "^a$" "b").issues.map (·.kind) == [.invalidValue]
#guard (regexFormatWarning "string" (some "\\(")).isNone
#guard (regexFormatWarning "string" (some "[(]")).isNone
#guard (regexFormatWarning "string" (some "\\")).isSome
#guard (regexFormatWarning "string" (some "(a")).isSome
#guard (prepared "string" "+" "AaAaA").value == ("AaAaA", true)
#guard (prepared "string" "+" "AaAaA").issues.map (·.kind) == [.warning]
#guard (regexFormatWarning "string" (some "*")).isSome
#guard (regexFormatWarning "string" (some "?")).isSome
#guard (regexFormatWarning "string" (some "\\+")).isNone

private def table (pat : String) : TableDesc :=
  { url := "data.csv", schema := some { columns :=
    [{ name := some "value", inherited := { datatype := some (datatype "string" pat) } }] } }
private def data : Table :=
  { header := [], rows := [{ num := 2, cells := ["a"] }] }
private def rdfResult (pat : String) :=
  let t := table pat
  convert "https://example.org/" {} { tables := [t] } true [(t, data)]
private def jsonResult (pat : String) :=
  let t := table pat
  convertJson "https://example.org/" {} { tables := [t] } true [(t, data)]

#guard (rdfResult "(?=a)a").value?.isNone
#guard (jsonResult "(?=a)a").value?.isNone
#guard (rdfResult "[").value?.isSome
#guard (jsonResult "[").value?.isSome
#guard (rdfResult "^b$").value?.isSome
#guard (jsonResult "^b$").value?.isSome
#guard (rdfResult "(?=a)a").issues.map (fun i => (i.kind, i.table, i.row, i.column)) ==
  [(.unsupported, "https://example.org/data.csv", 2, "value")]
#guard (jsonResult "[").issues.map (·.kind) == [.warning]

-- Metadata warnings do not depend on the existence of cell values.
private def metadata := JSON.Json.object [("url", .string "data.csv"),
  ("datatype", .object [("base", .string "string"), ("format", .string "[")])]
#guard (validate metadata).map (·.severity) == [.warning]
#guard passes (validate metadata)
#guard (convert "https://example.org/" {} {} true
  [(table "[", { header := [], rows := [] })]).issues.map (·.kind) == [.warning]
#guard (convertJson "https://example.org/" {} {} true
  [(table "[", { header := [], rows := [{ num := 2, cells := [""] }] })]).issues.map (·.kind) == [.warning]

end L4Factoidal.CSVW.RegexFormatTests
