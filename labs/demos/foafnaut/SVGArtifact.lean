import SVG

/-- Source-level diagnostic exporter. Uses the same producer as the WASM ABI.
    Output is a scene artifact, not an image or a rebuilt WASM engine. -/
def exportSVGArtifact : IO Unit := do
  let some input ← IO.getEnv "SVG_INPUT" | throw (IO.userError "Set SVG_INPUT")
  let some output ← IO.getEnv "SVG_OUTPUT" | throw (IO.userError "Set SVG_OUTPUT")
  let width := (← IO.getEnv "SVG_WIDTH").getD "800"
  let height := (← IO.getEnv "SVG_HEIGHT").getD "600"
  let some w := width.toNat? | throw (IO.userError "invalid width")
  let some h := height.toNat? | throw (IO.userError "invalid height")
  if (w == 0) != (h == 0) || w > 4096 || h > 4096 then
    throw (IO.userError "viewport dimensions must both be 0 (intrinsic) or 1..4096")
  let xml ← IO.FS.readFile input
  IO.FS.writeFile output (NativeSVG.compile xml w.toUInt32 h.toUInt32 ++ "\n")

#eval exportSVGArtifact
