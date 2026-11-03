import L4Factoidal.Rendering.SfntCff
open L4Factoidal.Rendering
def main (args : List String) : IO Unit := do
  let [path, n] := args | throw (IO.userError "usage: FONT COUNT")
  let b ← IO.FS.readBinFile path
  let dir ← IO.ofExcept (FontPolicy.readDirectory b)
  let some t := dir.find? (·.tag == "CFF ") | throw (IO.userError "no CFF")
  let f ← IO.ofExcept (SfntCff.readFont b t.offset t.length)
  for g in [0:min n.toNat! f.charStrings.size] do
    match SfntCff.extents b f g with
    | .ok (some (xb, yb, w, h)) => IO.println s!"{g} {xb} {yb} {w} {h}"
    | .ok none => IO.println s!"{g} none"
    | .error e => IO.println s!"{g} error {e}"
