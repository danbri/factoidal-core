import SolvingPolicy

def main (args : List String) : IO Unit := do
  let some output := args[0]? | throw (IO.userError "output path is required")
  let participants := [10,11,12,13,20]
  match Solving.certifyScene Solving.showcase
      L4Factoidal.UI.LayoutPolicy.defaultConfig participants with
  | none => throw (IO.userError "Solving showcase failed its bounded layout policy")
  | some certified =>
      match Solving.svgBackend.render certified with
      | .ok svg => IO.FS.writeFile (System.FilePath.mk output) svg
      | .error message => throw (IO.userError message)
