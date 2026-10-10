/-
L4Factoidal.RML.FunctionTests — build-time checks for RML-FNML at the
level of a whole mapping: a function in every term-map position, inputs of
every kind, nested functions, NULL and the empty string, conditions,
multi-valued inputs, and the mapping errors.

Each rule has a twin that differs by one property, so an implementation
that ignores the property fails.
-/
import L4Factoidal.RML.Run
import L4Factoidal.Syntax.Turtle

namespace L4Factoidal.RML

open L4Factoidal.RDF
open L4Factoidal.Syntax

private def graphOf (ttl : String) : Graph :=
  match parseTurtle ttl none with
  | .ok g    => g
  | .error _ => []

private def prefixes : String :=
  "@prefix rml: <http://w3id.org/rml/> .\n@prefix ex: <http://example.com/> .\n" ++
  "@prefix foaf: <http://xmlns.com/foaf/0.1/> .\n" ++
  "@prefix grel: <http://users.ugent.be/~bjdmeest/function/grel.ttl#> .\n" ++
  "@prefix idlab-fn: <https://w3id.org/imec/idlab/function#> .\n"

private def files (entries : List (String × String)) : FileAccess :=
  { read := fun _ p => (entries.find? (fun e => e.1 == p)).map (fun e => e.2.toUTF8) }

private def run (ttl : String) (csv : String) : EvalResult :=
  runMappingGraphFiles (graphOf (prefixes ++ ttl)) none (files [("d.csv", csv)])

private def valid (ttl : String) : Bool :=
  (validateMapping (graphOf (prefixes ++ ttl))).isEmpty

private def src : String :=
  "rml:logicalSource [ rml:source [ a rml:FilePath ; rml:path \"d.csv\" ] ; " ++
  "rml:referenceFormulation rml:CSV ] ; "

private def students : String := "Id,Name,Url\n1,Venus,http://example.com/venus\n"

/-- A triples map whose subject map is `subject` and whose only
    predicate-object map is `pom`, with the execution `ex:e`. -/
private def mapping (subject pom exec : String) : String :=
  "ex:tm a rml:TriplesMap ; " ++ src ++ "rml:subjectMap [ " ++ subject ++ " ] ; " ++
  "rml:predicateObjectMap [ " ++ pom ++ " ] .\n" ++ exec

private def tpl : String := "rml:template \"http://example.com/{Name}\""

private def upperOf (ref : String) : String :=
  "ex:e rml:function grel:toUpperCase ; rml:input [ rml:parameter grel:valueParam ; " ++
  "rml:inputValueMap [ rml:reference \"" ++ ref ++ "\" ] ] ."

private def objectUpper (more : String) : String :=
  mapping tpl ("rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; " ++
    "rml:return grel:stringOut " ++ more ++ " ]") (upperOf "Name")

private def lits (r : EvalResult) : List String :=
  r.quads.filterMap (fun q => match q.o with
    | .literal l => some l.val.lexicalForm
    | _ => none)

private def iris (r : EvalResult) : List String :=
  r.quads.filterMap (fun q => match q.o with
    | .iri i => some i.val
    | _ => none)

-- The fixtures parse and validate: a mapping that does not would make the
-- checks below vacuous.
#guard !(graphOf (prefixes ++ objectUpper "")).isEmpty
#guard valid (objectUpper "")

/-! ## A function in object position -/

private def o1 := run (objectUpper "") students
#guard !o1.rejected
#guard lits o1 == ["VENUS"]
-- the result is a literal by default, an IRI when the map says so
#guard (iris o1).isEmpty
private def o2 := run (mapping tpl
  ("rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; " ++
   "rml:return idlab-fn:_stringOut ; rml:termType rml:IRI ]")
  ("ex:e rml:function idlab-fn:toUpperCaseURL ; rml:input [ rml:parameter idlab-fn:str ; " ++
   "rml:inputValueMap [ rml:reference \"Url\" ] ] .")) students
#guard !o2.rejected
#guard iris o2 == ["HTTP://EXAMPLE.COM/VENUS"]
-- a function with no parameters
private def o3 := run (mapping tpl
  "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; rml:return idlab-fn:_stringOut ]"
  "ex:e rml:function idlab-fn:alwaysReturnsABC .") students
#guard lits o3 == ["ABC"]
-- the first return is the default
#guard lits (run (mapping tpl
  "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ]"
  "ex:e rml:function idlab-fn:alwaysReturnsABC .") students) == ["ABC"]
-- the map form of return, function and parameter
#guard lits (run (mapping tpl
  ("rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; " ++
   "rml:returnMap [ rml:constant grel:stringOut ] ]")
  ("ex:e rml:functionMap [ rml:constant grel:toUpperCase ] ; rml:input [ " ++
   "rml:parameterMap [ rml:constant grel:valueParam ] ; " ++
   "rml:inputValueMap [ rml:reference \"Name\" ] ] .")) students) == ["VENUS"]

/-! ## Inputs -/

-- a template input is the text it expands to, spaces and colons included
#guard lits (run (mapping tpl
  "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; rml:return grel:stringOut ]"
  ("ex:e rml:function grel:toUpperCase ; rml:input [ rml:parameter grel:valueParam ; " ++
   "rml:inputValueMap [ rml:template \"Name: {Name}\" ] ] .")) students) == ["NAME: VENUS"]
-- a constant input, two inputs
#guard lits (run (mapping tpl
  "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; rml:return grel:stringOut ]"
  ("ex:e rml:function grel:escape ; rml:input [ rml:parameter grel:valueParam ; " ++
   "rml:inputValueMap [ rml:constant \"A&B\" ] ] , [ rml:parameter grel:modeParam ; " ++
   "rml:inputValue \"html\" ] .")) students) == ["A&amp;B"]

/-! ## Return types -/

-- string_length returns an xsd:integer
private def len := run (mapping tpl
  "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; rml:return grel:output_number ]"
  ("ex:e rml:function grel:string_length ; rml:input [ rml:parameter grel:valueParam ; " ++
   "rml:inputValueMap [ rml:reference \"Name\" ] ] .")) students
#guard lits len == ["5"]
#guard len.quads.any (fun q => match q.o with
  | .literal l => l.val.datatype.val == "http://www.w3.org/2001/XMLSchema#integer"
  | _ => false)
-- ...unless the map states another datatype
#guard (run (mapping tpl
  ("rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; " ++
   "rml:return grel:output_number ; rml:datatype <http://www.w3.org/2001/XMLSchema#string> ]")
  ("ex:e rml:function grel:string_length ; rml:input [ rml:parameter grel:valueParam ; " ++
   "rml:inputValueMap [ rml:reference \"Name\" ] ] .")) students).quads.any (fun q => match q.o with
  | .literal l => l.val.datatype.val == "http://www.w3.org/2001/XMLSchema#string"
  | _ => false)

/-! ## NULL and the empty string -/

private def substr (from' : String) : String :=
  mapping tpl
    "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; rml:return grel:stringOut ]"
    ("ex:e rml:function grel:string_substring ; rml:input [ rml:parameter grel:valueParam ; " ++
     "rml:inputValueMap [ rml:reference \"Name\" ] ] , [ rml:parameter grel:p_int_i_from ; " ++
     "rml:inputValue \"" ++ from' ++ "\" ] .")

-- from the end: the empty string is a value, and a triple is generated
#guard lits (run (substr "5") students) == [""]
#guard (run (substr "5") students).quads.length == 1
-- beyond the end: NULL, no triple, no error
#guard !(run (substr "1000") students).rejected
#guard (run (substr "1000") students).quads.isEmpty
-- an index that is not a number is an error
#guard (run (substr "x") students).rejected

/-! ## Other positions -/

-- predicate
#guard iris (run (mapping tpl
  "rml:predicateMap [ rml:functionExecution ex:e ; rml:return idlab-fn:_stringOut ] ; rml:object foaf:name"
  ("ex:e rml:function idlab-fn:toUpperCaseURL ; rml:input [ rml:parameter idlab-fn:str ; " ++
   "rml:inputValueMap [ rml:reference \"Url\" ] ] .")) students) == ["http://xmlns.com/foaf/0.1/name"]
#guard (run (mapping tpl
  "rml:predicateMap [ rml:functionExecution ex:e ; rml:return idlab-fn:_stringOut ] ; rml:object foaf:name"
  ("ex:e rml:function idlab-fn:toUpperCaseURL ; rml:input [ rml:parameter idlab-fn:str ; " ++
   "rml:inputValueMap [ rml:reference \"Url\" ] ] .")) students).quads.any
  (fun q => q.p.val == "HTTP://EXAMPLE.COM/VENUS")
-- subject
#guard (run (mapping "rml:functionExecution ex:e ; rml:return idlab-fn:_stringOut"
  "rml:predicate foaf:name ; rml:objectMap [ rml:reference \"Name\" ]"
  ("ex:e rml:function idlab-fn:toUpperCaseURL ; rml:input [ rml:parameter idlab-fn:str ; " ++
   "rml:inputValueMap [ rml:reference \"Url\" ] ] .")) students).quads.any
  (fun q => q.s == Subject.iri ⟨"HTTP://EXAMPLE.COM/VENUS", rfl⟩)
-- graph
#guard (run (mapping (tpl ++ " ; rml:graphMap [ rml:functionExecution ex:e ; rml:return idlab-fn:_stringOut ]")
  "rml:predicate foaf:name ; rml:objectMap [ rml:reference \"Name\" ]"
  ("ex:e rml:function idlab-fn:toUpperCaseURL ; rml:input [ rml:parameter idlab-fn:str ; " ++
   "rml:inputValueMap [ rml:reference \"Url\" ] ] .")) students).quads.any
  (fun q => q.g == some (Term.iri ⟨"HTTP://EXAMPLE.COM/VENUS", rfl⟩))
-- datatype map and language map
private def tagged (mapProp fnIri param value : String) : EvalResult :=
  run (mapping tpl
    ("rml:predicate foaf:name ; rml:objectMap [ rml:reference \"Name\" ; rml:" ++ mapProp ++
     " [ rml:functionExecution ex:e ; rml:return grel:stringOut ] ]")
    ("ex:e rml:function " ++ fnIri ++ " ; rml:input [ rml:parameter " ++ param ++ " ; " ++
     "rml:inputValueMap [ rml:reference \"" ++ value ++ "\" ] ] , [ rml:parameter grel:p_int_i_from ; " ++
     "rml:inputValue \"0\" ] .")) "Id,Name,Dt,Lang\n1,Venus,http://www.w3.org/2001/XMLSchema#string,en\n"
#guard (tagged "datatypeMap" "grel:string_substring" "grel:valueParam" "Dt").quads.any (fun q => match q.o with
  | .literal l => l.val.datatype.val == "http://www.w3.org/2001/XMLSchema#string"
  | _ => false)
#guard (tagged "languageMap" "grel:string_substring" "grel:valueParam" "Lang").quads.any (fun q => match q.o with
  | .literal l => l.val.langTag == some "en"
  | _ => false)
-- a language tag that is not well formed is an error, as without a function
#guard (run (mapping tpl
  ("rml:predicate foaf:name ; rml:objectMap [ rml:reference \"Name\" ; rml:languageMap " ++
   "[ rml:functionExecution ex:e ; rml:return grel:stringOut ] ]")
  ("ex:e rml:function grel:toUpperCase ; rml:input [ rml:parameter grel:valueParam ; " ++
   "rml:inputValueMap [ rml:constant \"a-english\" ] ] .")) students).rejected

/-! ## Nested functions -/

private def nested : String :=
  mapping tpl
    "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; rml:return grel:stringOut ]"
    ("ex:e rml:function grel:toUpperCase ; rml:input [ rml:parameter grel:valueParam ; " ++
     "rml:inputValueMap [ rml:functionExecution ex:e2 ; rml:return grel:stringOut ] ] .\n" ++
     "ex:e2 rml:function grel:string_replace ; rml:input " ++
     "[ rml:parameter grel:valueParam ; rml:inputValueMap [ rml:reference \"Name\" ] ] , " ++
     "[ rml:parameter grel:param_find ; rml:inputValue \" \" ] , " ++
     "[ rml:parameter grel:param_replace ; rml:inputValue \"-\" ] .")
#guard valid nested
#guard lits (run nested "Id,Name\n1,M Venus\n") == ["M-VENUS"]

/-! ## Conditions -/

private def conditional (cls : String) : String :=
  mapping (tpl ++ " ; rml:condition [ rml:functionExecution [ rml:function idlab-fn:equal ; " ++
      "rml:input [ rml:parameter grel:valueParam ; rml:inputValueMap [ rml:reference \"Class\" ] ] , " ++
      "[ rml:parameter grel:valueParam2 ; rml:inputValue \"" ++ cls ++ "\" ] ] ; " ++
      "rml:return idlab-fn:_boolOut ]")
    "rml:predicate foaf:name ; rml:objectMap [ rml:reference \"Name\" ]" ""

private def classes : String := "Id,Name,Class\n1,Venus,A\n2,Serena,B\n"
#guard valid (conditional "A")
-- only the rows for which the condition holds generate triples
#guard lits (run (conditional "A") classes) == ["Venus"]
#guard lits (run (conditional "B") classes) == ["Serena"]
#guard (run (conditional "C") classes).quads.isEmpty
#guard !(run (conditional "C") classes).rejected

/-! ## Multi-valued inputs -/

private def jsonRun (ttl data : String) : EvalResult :=
  runMappingGraphFiles (graphOf (prefixes ++ ttl)) none (files [("d.json", data)])

-- every value of a multi-valued input is applied in turn
private def multi : String :=
  "ex:tm a rml:TriplesMap ; rml:logicalSource [ rml:source [ a rml:FilePath ; rml:path \"d.json\" ] ; " ++
  "rml:referenceFormulation rml:JSONPath ; rml:iterator \"$.*\" ] ; " ++
  "rml:subjectMap [ rml:template \"http://example.com/{$.id}\" ] ; " ++
  "rml:predicateObjectMap [ rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; " ++
  "rml:return grel:stringOut ] ] .\n" ++
  "ex:e rml:function grel:toUpperCase ; rml:input [ rml:parameter grel:valueParam ; " ++
  "rml:inputValueMap [ rml:reference \"$.names[*]\" ] ] ."
#guard lits (jsonRun multi "[{\"id\":\"a\",\"names\":[\"x\",\"y\"]}]") == ["X", "Y"]

/-! ## Mapping errors -/

-- a function the registry does not have
#guard !valid (mapping tpl
  "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ]"
  "ex:e rml:function grel:unknown_func .")
-- a parameter the function does not have
#guard !valid (mapping tpl
  "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; rml:return grel:stringOut ]"
  ("ex:e rml:function grel:toUpperCase ; rml:input [ rml:parameter grel:unknownParam ; " ++
   "rml:inputValueMap [ rml:reference \"Name\" ] ] ."))
-- a return the function does not have
#guard !valid (mapping tpl
  "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; rml:return grel:unknownOut ]"
  (upperOf "Name"))
-- a required parameter without an input
#guard !valid (mapping tpl
  "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; rml:return grel:stringOut ]"
  "ex:e rml:function grel:toUpperCase .")
-- an execution with two functions, an input with no value
#guard !valid (mapping tpl
  "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ]"
  "ex:e rml:function grel:toUpperCase , grel:toLowerCase .")
#guard !valid (mapping tpl
  "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ]"
  "ex:e rml:function grel:toUpperCase ; rml:input [ rml:parameter grel:valueParam ] .")
-- a reference to a column the source does not have: an error
#guard (run (mapping tpl
  "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; rml:return grel:stringOut ]"
  (upperOf "name")) students).rejected
#guard (run (mapping tpl "rml:predicate foaf:name ; rml:objectMap [ rml:reference \"name\" ]" "")
  students).rejected
-- ...and a NULL value in a column that exists is not
#guard !(runMappingGraphFiles
  (graphOf (prefixes ++ "ex:tm a rml:TriplesMap ; rml:logicalSource [ rml:source [ a rml:FilePath ; " ++
    "rml:path \"d.csv\" ; rml:null \"\" ] ; rml:referenceFormulation rml:CSV ] ; " ++
    "rml:subjectMap [ rml:template \"http://example.com/{Id}\" ] ; " ++
    "rml:predicateObjectMap [ rml:predicate foaf:name ; rml:objectMap [ rml:reference \"Name\" ] ] ."))
  none (files [("d.csv", "Id,Name\n1,\n")])).rejected

-- Valid and invalid twins differ by one property only
#guard valid (mapping tpl
  "rml:predicate foaf:name ; rml:objectMap [ rml:functionExecution ex:e ; rml:return grel:stringOut ]"
  (upperOf "Name"))

end L4Factoidal.RML
