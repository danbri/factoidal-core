import EVMCleanroom.TransactionTransportProofs

/-!
# Transaction JSON transport guards

These executable guards witness the scanner's exact boundaries, string state,
and the shared codec continuation. They are tests, distinct from the theorem
claims and from the native adversarial corpus run against all three CLIs.
-/

namespace EVMCleanroom.TransactionTransport.Tests

private def repeated (byte : Char) (count : Nat) : String :=
  String.ofList (List.replicate count byte)

private def arrays (count : Nat) : String :=
  repeated '[' count ++ "0" ++ repeated ']' count

private def objects (count : Nat) : String :=
  String.join (List.replicate count "{\"a\":") ++ "0" ++ repeated '}' count

private def quoted (text : String) : String := "\"" ++ text ++ "\""

private def stepIs (state : ScanState) (byte : UInt8) (expected : ScanState) : Bool :=
  match TransactionTransport.step state byte with
  | .ok next => next == expected
  | .error _ => false

private def stepRefused (state : ScanState) (byte : UInt8) (expected : String) : Bool :=
  match TransactionTransport.step state byte with
  | .error reason => reason == expected
  | .ok _ => false

private def admitted (text : String) : Bool :=
  match TransactionTransport.check text with
  | .ok () => true
  | .error _ => false

private def parsed (text : String) : Bool :=
  match TransactionCodec.parseJSON text with
  | .ok _ => true
  | .error _ => false

private def refused (text reason : String) : Bool :=
  match TransactionCodec.parseJSON text with
  | .error actual => actual == reason
  | .ok _ => false

private def parserAgreement (text : String) : Bool :=
  match TransactionCodec.parseJSON text, Lean.Json.parse text with
  | .ok left, .ok right => left == right
  | .error left, .error right => left == right
  | _, _ => false

-- Step boundaries include both sides and numeric-limit error priority.
#guard stepIs { depth := 63 } 91 { depth := 64 }
#guard stepRefused { depth := 64 } 91 "json-nesting-limit"
#guard stepRefused { depth := 64 } 123 "json-nesting-limit"
#guard stepIs { numberBytes := 95 } 57 { numberBytes := 96 }
#guard stepRefused { numberBytes := 96 } 57 "json-number-token-limit"
#guard stepIs { numberBytes := 3, exponentMode := true, exponent := 7 } 56
  { numberBytes := 4, exponentMode := true, exponent := 78 }
#guard stepRefused { numberBytes := 3, exponentMode := true, exponent := 7 } 57
  "json-exponent-limit"
#guard stepRefused { numberBytes := 96, exponentMode := true, exponent := 7 } 57
  "json-number-token-limit"

-- Actual UTF-8 folds and the shared codec at structural and token boundaries.
#guard admitted (arrays 64) && parsed (arrays 64)
#guard refused (arrays 65) "json-nesting-limit"
#guard admitted (objects 64) && parsed (objects 64)
#guard refused (objects 65) "json-nesting-limit"
#guard admitted (repeated '9' 96) && parsed (repeated '9' 96)
#guard refused (repeated '9' 97) "json-number-token-limit"
#guard parsed ("-" ++ repeated '9' 95)
#guard refused ("-" ++ repeated '9' 96) "json-number-token-limit"
#guard parsed ("1." ++ repeated '9' 94)
#guard refused ("1." ++ repeated '9' 95) "json-number-token-limit"

-- The exponent bound is its magnitude, including signs and leading zeros.
#guard parsed "1e+78"
#guard parsed "1E-78"
#guard refused "1e79" "json-exponent-limit"
#guard refused "1E-79" "json-exponent-limit"
#guard parsed "1e+00078"
#guard refused "1e-00079" "json-exponent-limit"
#guard refused "0e999" "json-exponent-limit"

-- Quoted contents do not consume numeric or nesting allowances.
#guard parsed (quoted (repeated '9' 97))
#guard parsed (quoted (repeated '[' 1000 ++ "1e999"))
#guard stepIs { quoted := true, escaped := true } 34 { quoted := true }
#guard stepIs { quoted := true, escaped := true } 92 { quoted := true }
#guard stepIs { quoted := true } 92 { quoted := true, escaped := true }
#guard stepIs { quoted := true } 34 {}
#guard stepIs { depth := 64, quoted := true, numberBytes := 96, exponent := 78 } 91
  { depth := 64, quoted := true, numberBytes := 96, exponent := 78 }
#guard parsed (String.ofList ['"', '\\', '"', '[', '1', 'e', '9', '9', '9', '"'])
#guard parsed "\"\\u0022[1e999\""

-- Grammar decisions still belong to Lean.Json.parse after resource admission.
#guard admitted "\"unfinished" && !parsed "\"unfinished" && parserAgreement "\"unfinished"
#guard admitted "1e+" && !parsed "1e+" && parserAgreement "1e+"
#guard admitted "\"\\q\"" && !parsed "\"\\q\"" && parserAgreement "\"\\q\""
#guard admitted "]" && !parsed "]" && parserAgreement "]"
#guard parsed "1.25e+2" && parserAgreement "1.25e+2"
#guard parsed "1e0" && parserAgreement "1e0"
#guard parsed "1.0" && parserAgreement "1.0"

-- A prior refusal persists; the continuation is selected only on admission.
#guard match feed (.error "retained") 91 with
  | .error reason => reason == "retained"
  | .ok _ => false
#guard match parseWith (fun _ => Except.error (α := Nat) "parser-was-selected") (arrays 65) with
  | .error reason => reason == "json-nesting-limit"
  | .ok _ => false
#guard match parseWith (fun _ => Except.error (α := Nat) "parser-was-selected") "[]" with
  | .error reason => reason == "parser-was-selected"
  | .ok _ => false

end EVMCleanroom.TransactionTransport.Tests
