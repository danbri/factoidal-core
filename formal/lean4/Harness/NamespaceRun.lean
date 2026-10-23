/- Manifest-driven Namespaces in XML check. Run from the repository root:
   formal/lean4/.lake/build/bin/l4xml-namespaces [namespace-suite-directory]
   Scores required UTF-8 verdicts; optional errors and non-UTF8 are separate.
   This checks the vendored namespace suite, not all XML 1.1 productions. -/
import L4Factoidal.XML.NamespaceView

open L4Factoidal.XML

private def manifests : List String :=
  ["1.0/rmt-ns10.xml", "1.1/rmt-ns11.xml", "errata-1e/errata1e.xml"]

private def attr (n : Node) (key : String) : String :=
  (findAttr key n.elementAttrs).getD ""

def main (args : List String) : IO UInt32 := do
  let base := args.headD "third_party/testing/xml/xmlconf/eduni/namespaces"
  let mut passed := 0
  let mut failed := 0
  let mut optional := 0
  let mut encoding := 0
  let mut errors := 0
  for manifest in manifests do
    let file := base ++ "/" ++ manifest
    let content ← (IO.FS.readFile file).toBaseIO
    match content with
    | .error e =>
        errors := errors + 1
        IO.println s!"ERROR {file}: {e}"
    | .ok src =>
      match parseXML src with
      | .error e =>
          errors := errors + 1
          IO.println s!"ERROR {file}: {e.message}"
      | .ok doc =>
        let tests := doc.root.childElements "TEST"
        if tests.isEmpty then
          errors := errors + 1
          IO.println s!"ERROR {file}: empty manifest"
        for test in tests do
          let id := attr test "ID"
          let kind := attr test "TYPE"
          let uri := attr test "URI"
          let dir := (manifest.splitOn "/").headD ""
          if kind == "error" then
            optional := optional + 1
            IO.println s!"OPTIONAL {id}: no required verdict"
          else if !(["valid", "invalid", "not-wf"].contains kind) || uri == "" then
            errors := errors + 1
            IO.println s!"ERROR {id}: unknown verdict or missing URI"
          else
            let content ← (IO.FS.readBinFile (base ++ "/" ++ dir ++ "/" ++ uri)).toBaseIO
            match content with
            | .error e =>
                errors := errors + 1
                IO.println s!"ERROR {id}: {e}"
            | .ok bytes =>
              match String.fromUTF8? bytes with
              | none =>
                  encoding := encoding + 1
                  IO.println s!"EXCLUDED {id}: non-UTF8"
              | some input =>
                  let got := (parseNamespaceView input).isOk
                  let want := kind != "not-wf"
                  if got == want then passed := passed + 1
                  else
                    failed := failed + 1
                    IO.println s!"FAIL {id} ({dir}/{uri}): accepted={got}, expected={want}"
  IO.println s!"Namespaces: {passed} pass, {failed} fail / {passed + failed} scored; {optional} optional, {encoding} non-UTF8, {errors} errors"
  return if failed == 0 && errors == 0 then 0 else 1
