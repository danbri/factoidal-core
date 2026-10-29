import L4Factoidal.XProc31.Atomic
import L4Factoidal.JSONSchema.Validate
import L4Factoidal.JSON.Parser

namespace L4Factoidal.XProc31
open XML

def supportsJsonSchema (name : String) : Bool := name == "validate-with-json-schema"

/-- Convert the actual XDM document value, preserving native JSON maps and arrays. -/
def jsonSchemaDocument (doc : Document) : Result JSON.Json := do
  let context := xpathEnv (some doc) [] []
  let text ← fromXPath (context.serializeWith {method := "json"} (context.ctx.getD []))
  match JSON.parseJson text with
  | .ok json => pure json
  | .error _ => error "XC0164" "document cannot be represented as JSON"

/-- Check keyword shapes independently of whether an instance exercises a branch.
    Unknown keywords remain the existing validator's explicit unsupported verdict. -/
def wellFormedJsonSchema : Nat → JSON.Json → Bool
  | 0, _ => false
  | _, .bool _ => true
  | fuel+1, .object fields => fields.all fun (key,value) =>
    if ["properties", "patternProperties", "definitions", "$defs"].contains key then
      match value with
      | .object members => members.all (fun (_,s) => wellFormedJsonSchema fuel s)
      | _ => false
    else if ["allOf", "anyOf", "oneOf"].contains key then
      match value with
      | .array schemas => !schemas.isEmpty && schemas.all (wellFormedJsonSchema fuel)
      | _ => false
    else if ["not", "if", "then", "else", "contains", "additionalProperties", "additionalItems", "propertyNames"].contains key then
      wellFormedJsonSchema fuel value
    else if key == "items" then
      match value with
      | .array schemas => schemas.all (wellFormedJsonSchema fuel)
      | _ => wellFormedJsonSchema fuel value
    else if key == "required" then
      match value with
      | .array names => names.all (fun n => match n with | .string _ => true | _ => false) && names.eraseDups.length == names.length
      | _ => false
    else if key == "type" then
      let validType := fun (j : JSON.Json) => match j with
        | .string s => ["null", "boolean", "object", "array", "number", "integer", "string"].contains s
        | _ => false
      match value with
      | .array names => !names.isEmpty && names.all validType && names.eraseDups.length == names.length
      | _ => validType value
    else if ["$schema", "$id", "id", "$ref", "pattern"].contains key then
      match value with | .string _ => true | _ => false
    else if ["minimum", "maximum", "exclusiveMinimum", "exclusiveMaximum", "multipleOf"].contains key then
      match value with
      | .number n => match JSONSchema.parseRat n with
        | some r => key != "multipleOf" || r.1 > 0
        | none => false
      | _ => false
    else if ["minLength", "maxLength", "minItems", "maxItems", "minProperties", "maxProperties"].contains key then
      match value with
      | .number n => match JSONSchema.parseRat n with
        | some r => JSONSchema.isIntegral r && r.1 >= 0
        | none => false
      | _ => false
    else if key == "uniqueItems" then
      match value with | .bool _ => true | _ => false
    else if key == "enum" then
      match value with | .array values => !values.isEmpty && values.eraseDups.length == values.length | _ => false
    else true
  | _, _ => false

def jsonSchemaPorts (step : Node) (ports : List (String × List Document))
    (env : XPath4.Env) : Result (List (String × List Document)) := do
  let source ← oneSource ((ports.lookup "source").getD [])
  let schemaDoc ← oneSource ((ports.lookup "schema").getD [])
  let reportFormat ← option step "report-format" env "xvrl"
  if reportFormat != "xvrl" then return ← error "XC0117" ("unsupported JSON schema report format " ++ reportFormat)
  let schema ← jsonSchemaDocument schemaDoc
  let version := match schema.field? "$schema" with | some (.string s) => s | _ => "http://json-schema.org/draft-07/schema#"
  if !["http://json-schema.org/draft-07/schema#", "http://json-schema.org/draft-07/schema", "https://json-schema.org/draft-07/schema#", "https://json-schema.org/draft-07/schema"].contains version then
    return ← error "XC0163" ("unsupported JSON Schema version " ++ version)
  if !wellFormedJsonSchema 4096 schema then return ← error "XC0164" "invalid JSON Schema keyword structure"
  let instanceValue ← jsonSchemaDocument source
  let valid ← match JSONSchema.validate schema instanceValue with
    | .pass => pure true
    | .fail => pure false
    | .unsupported => unsupported "JSON Schema keyword, reference, or expression outside implemented validator"
  let detections : List Node := if valid then [] else
    [.element "xvrl:detection" [⟨"severity","error"⟩,⟨"code","XC0165"⟩]
      [.element "xvrl:message" [] [.text "document is not valid against the supplied JSON Schema"]]]
  let report : Document := {node := .element "xvrl:report" [⟨"xmlns:xvrl","http://www.xproc.org/ns/xvrl"⟩] detections}
  if !valid && (← option step "assert-valid" env "true") != "false" then
    return ← .error {code := "XC0165", message := "document is not valid against the supplied JSON Schema", details := [report.node]}
  pure [("result",[source]),("report",[report])]

def jsonSchemaStep (step : Node) (ports : List (String × List Document))
    (env : XPath4.Env) : IO (Result (List Document)) :=
  pure ((jsonSchemaPorts step ports env).map (fun ports => (ports.lookup "result").getD []))

#guard wellFormedJsonSchema 100 (.object [("type",.string "object"),("required",.array [.string "missing"])])
#guard !wellFormedJsonSchema 100 (.object [("required",.string "wrong")])
#guard JSONSchema.validate (.object [("required",.array [.string "missing"])]) (.object []) == .fail
private def jsonSchemaRegressionSource : Document :=
  {node := .text "{}", contentType := "application/json"}
private def jsonSchemaRegressionSchema : Document :=
  {node := .text "{\"required\":[\"missing\"]}", contentType := "application/json"}
#guard match jsonSchemaPorts (.element "p:validate-with-json-schema" [] [])
    [("source",[jsonSchemaRegressionSource]),("schema",[jsonSchemaRegressionSchema])] {} with
  | .error e => e.code == "XC0165" | _ => false
#guard (jsonSchemaPorts (.element "p:validate-with-json-schema" [⟨"assert-valid","false"⟩] [])
    [("source",[jsonSchemaRegressionSource]),("schema",[jsonSchemaRegressionSchema])] {}).toOption.map
  (fun ports => ((ports.lookup "report").getD []).any (fun d => (named d.node "detection").length == 1)) == some true
end L4Factoidal.XProc31
