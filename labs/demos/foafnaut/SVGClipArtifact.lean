import SVGClipTests

def main (args : List String) : IO Unit := do
  let [directory] := args | throw (IO.userError "usage: SVGClipArtifact OUTPUT_DIRECTORY")
  NativeSVGClipTests.writeControls directory
