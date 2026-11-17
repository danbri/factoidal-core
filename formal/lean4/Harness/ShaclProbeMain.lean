/-
Harness.ShaclProbeMain — the `l4shacl` executable's entry point.

`Harness.ShaclProbe` holds the test collection and `runTest`, with no top-level `main`, so
other runners (`l4shacl-nodeexpr`, for the `sht:Validate` tests of the SHACL 1.2 node
expression suite) can import it. Usage is as before: `lake exe l4shacl [manifest]`.
-/
import Harness.ShaclProbe

def main (args : List String) : IO UInt32 := ShaclProbe.run args
