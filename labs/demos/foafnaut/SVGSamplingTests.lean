import SVG
namespace NativeSVGSamplingTests
private def doc (body : String) := "<svg xmlns='http://www.w3.org/2000/svg' width='20' height='20'>" ++ body ++ "</svg>"
private def shape := "<rect x='0.5' y='0.5' width='10' height='10'/>"
private def check (b : Bool) : IO Unit := unless b do throw (IO.userError "coverage regression")
def run : IO Unit := do
  check (NativeSVG.sample (doc shape) 0 0 0 0 == "{\"rgb\":[191,191,191]}")
  check (NativeSVG.sample (doc shape) 0 0 1 0 == "{\"rgb\":[128,128,128]}")
  check (NativeSVG.sample (doc shape) 0 0 1 1 == "{\"rgb\":[0,0,0]}")
  check (NativeSVG.sample (doc (shape ++ shape)) 0 0 1 0 == "{\"rgb\":[128,128,128]}")
  IO.println "PASS quarter/half/full coverage and sample-before-average compositing"
end NativeSVGSamplingTests
#eval NativeSVGSamplingTests.run
