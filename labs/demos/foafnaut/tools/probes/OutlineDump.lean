import L4Factoidal.Rendering.SfntOutline
open L4Factoidal.Rendering
def cmd : FontData.OutlineCommand → String
  | .move x y => s!" M {x} {y}" | .line x y => s!" L {x} {y}"
  | .quadratic a b x y => s!" Q {a} {b} {x} {y}"
  | .cubic a b c d x y => s!" C {a} {b} {c} {d} {x} {y}"
  | .close => ""
def main (args : List String) : IO UInt32 := do
  let [path,a,z] := args | return 2
  let b ← IO.FS.readBinFile path
  let .ok dir := FontPolicy.readDirectory b 0 | return 3
  let .ok cff := SfntOutline.cffFont b dir | return 4
  let out ← IO.getStdout
  for g in [a.toNat!:z.toNat!] do
    match SfntOutline.outline b dir g cff with
    | .ok cs => out.putStrLn (s!"{g}" ++ String.join (cs.toList.map cmd))
    | .error e => out.putStrLn s!"{g} ERR {e}"
  return 0
