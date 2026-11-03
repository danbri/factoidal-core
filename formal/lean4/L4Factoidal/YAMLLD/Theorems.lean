/-
L4Factoidal.YAMLLD.Theorems — how YAML-LD 1.0 (Editor's Draft, json-ld/yaml-ld
commit `fafcf7ae`) relates to JSON-LD 1.1 (W3C Recommendation 2020-07-16) and
to YAML 1.2.2.

YAML-LD 1.0 §4.4: the native data structure of a YAML-LD document is the
JSON-LD 1.1 internal representation. The first two theorems state the
consequence for the API: a YAML-LD stream and a JSON text with the same
internal representation give the same expansion and the same RDF dataset.
They are proved over the JSON-LD 1.1 code as it stands (`expandDocument`,
`parseJsonLd`), so a change to the JSON-LD implementation keeps them true,
and a JSON-LD 1.2 or YAML-LD 1.1 relation is a new theorem with its own name.

That every JSON text loads through the YAML loader as the value
`parseJson` gives (YAML 1.2.2 §1.3: "YAML can therefore be viewed as a
natural superset of JSON") is not proved here; `l4yamlld --json-superset`
measures it over the JSON-LD 1.1 test suite's inputs.

The remaining theorems pin the scalar table of YAML-LD 1.0 §4.3.2 (the YAML
1.2.2 Core Schema, §10.3.2) and the stream rule of §4.4.2.
-/
import L4Factoidal.YAMLLD.Api

namespace L4Factoidal.YAMLLD

open L4Factoidal.JSON
open L4Factoidal.JSONLD
open L4Factoidal.YAML

/-! ## YAML-LD 1.0 and JSON-LD 1.1 -/

/-- YAML-LD 1.0 expansion equals JSON-LD 1.1 expansion of a JSON text with
the same internal representation. -/
theorem yamlld10_expand_eq_jsonld11_expand (loader : Loader) (y t : String) (opts : Options)
    (base expandContext processingMode : Option String) (j : Json)
    (hy : load y opts = .ok j) (ht : parseJson t = .ok j) :
    expandYamlLd loader y base expandContext processingMode opts =
      liftJsonLd (expandDocument loader t base expandContext processingMode) := by
  unfold expandYamlLd expandDocument
  rw [hy, ht]

/-- YAML-LD 1.0 toRdf equals JSON-LD 1.1 toRdf of a JSON text with the same
internal representation. -/
theorem yamlld10_toRdf_eq_jsonld11_toRdf (loader : Loader) (y t : String) (opts : Options)
    (base rdfDirection expandContext processingMode : Option String) (j : Json)
    (hy : load y opts = .ok j) (ht : parseJson t = .ok j) :
    toRdfYamlLd loader y base rdfDirection expandContext processingMode opts =
      liftJsonLd (parseJsonLd loader t base rdfDirection expandContext processingMode) := by
  unfold toRdfYamlLd parseJsonLd
  rw [hy, ht]

/-- A YAML-LD 1.0 stream that does not load gives its own error, never a
JSON-LD 1.1 result. -/
theorem yamlld10_expand_load_error (loader : Loader) (y : String) (opts : Options)
    (base expandContext processingMode : Option String) (e : YamlLdError)
    (hy : load y opts = .error e) :
    expandYamlLd loader y base expandContext processingMode opts = .error e := by
  unfold expandYamlLd
  rw [hy]

/-! ## YAML-LD 1.0 §4.4.2 stream processing -/

theorem yamlld10_stream_all (docs : List Json) :
    internalRepresentation docs true = .array docs := rfl

theorem yamlld10_stream_first (d : Json) (rest : List Json) :
    internalRepresentation (d :: rest) false = d := rfl

theorem yamlld10_stream_empty_first : internalRepresentation [] false = .null := rfl

theorem yamlld10_stream_empty_all : internalRepresentation [] true = .array [] := rfl

/-! ## YAML-LD 1.0 §4.3.2, the YAML 1.2.2 Core Schema table -/

theorem core_null_tilde (p : Nat) : resolvePlain "~" p = .ok .null := by rfl
theorem core_null_empty (p : Nat) : resolvePlain "" p = .ok .null := by rfl
theorem core_null_upper (p : Nat) : resolvePlain "NULL" p = .ok .null := by rfl
theorem core_bool_title (p : Nat) : resolvePlain "True" p = .ok (.bool true) := by rfl
theorem core_bool_upper (p : Nat) : resolvePlain "FALSE" p = .ok (.bool false) := by rfl
theorem core_int_octal (p : Nat) : resolvePlain "0o77" p = .ok (.number "63") := by rfl
theorem core_int_hex (p : Nat) : resolvePlain "0x3A" p = .ok (.number "58") := by rfl
theorem core_float_dot (p : Nat) : resolvePlain ".5" p = .ok (.number "0.5") := by rfl
theorem core_inf_refused (p : Nat) : resolvePlain "-.inf" p = .error (.notJsonNumber "-.inf" p) := by rfl
theorem core_nan_refused (p : Nat) : resolvePlain ".NaN" p = .error (.notJsonNumber ".NaN" p) := by rfl
/-- The YAML 1.1 booleans are strings in YAML 1.2 (YAML-LD 1.0 §8). -/
theorem core_yaml11_yes (p : Nat) : resolvePlain "yes" p = .ok (.string "yes") := by rfl
/-- No timestamp type: a date is a string (YAML-LD 1.0 §4.3.2). -/
theorem core_date_string (p : Nat) : resolvePlain "2018-04-01" p = .ok (.string "2018-04-01") := by rfl

end L4Factoidal.YAMLLD
