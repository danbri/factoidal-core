import SVGCurveTests

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: SVGCurveArtifact OUTPUT_DIRECTORY")
  NativeSVGCurveTests.writeControls directory
