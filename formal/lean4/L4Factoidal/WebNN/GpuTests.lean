/-
L4Factoidal.WebNN.GpuTests: `#guard` tests of WebNN on the GPU path through the API
(`WebNN.Api`, `WebNN.GpuRun`): which graphs get a plan on the page's GPU, what they emit, and
what stays on the CPU reference.
-/
import L4Factoidal.WebNN.Api
import L4Factoidal.PageGpu.Wire

namespace L4Factoidal.WebNN.GpuRun

namespace Tests
open L4Factoidal.WebNN

def call (s : State) (fs : List String) : State × String :=
  let (s, b) := api s (fs.map String.toUTF8).toArray
  (s, (String.fromUTF8? b).getD "")

def run (s : State) : List (List String) → State × List String
  | [] => (s, [])
  | f :: fs => let (s, a) := call s f; let (s, rest) := run s fs; (s, a :: rest)

def gpuPage : State := { page := L4Factoidal.PageGpu.State.empty 3 true, room := 65536 }

def graph (dev unary : String) (s : State := gpuPage) : State × List String := run s [
  ["context", dev], ["builder", "0"],
  ["input", "0", "a", "float32", "2,3"], ["input", "0", "b", "float32", "3"],
  ["op", "0", "add", "", "a", "0.0", "b", "0.1"], ["op", "0", unary, "", "input", "0.2"],
  ["build", "0", "out", "0.3"],
  ["tensor", "0", "float32", "2,3", "rw"], ["tensor", "0", "float32", "3", "rw"], ["tensor", "0", "float32", "2,3", "r"],
  ["dispatch", "0", "0", "2", "a", "0", "b", "1", "out", "2"]]

def kinds (s : State) : List String := s.out.toList.map fun c => ((L4Factoidal.PageGpu.Wire.HostCmd.json c).splitOn "\"k\":\"").getD 1 "" |>.takeWhile (· != '"') |>.toString

-- add then relu on a GPU context of an embedder that replays: a plan on the page's GPU
#guard ((graph "gpu" "relu").1.builders[0]?.bind (·.gpu)).isSome
#guard (graph "gpu" "relu").2.getLast? == some ""
#guard (kinds (graph "gpu" "relu").1).contains "cpass" && (kinds (graph "gpu" "relu").1).contains "cpipeline"
#guard ((graph "gpu" "relu").1.tensors[2]?.map (·.onGpu)) == some true
-- the output is read back through the page's GPU: byte 2, then a staging buffer and its readback
#guard (api (graph "gpu" "relu").1 #["read".toUTF8, "0".toUTF8, "2".toUTF8]).2 == ByteArray.mk #[2]
#guard let (s, _) := call (graph "gpu" "relu").1 ["readGpu", "0", "2", "77"]
  (kinds s).getLast? == some "read" && (s.page.pending.map (·.1)) == [77]
-- softmax and leakyRelu have kernels; elu is outside the tolerance (CPU reference)
#guard ((run gpuPage [["context", "gpu"], ["builder", "0"], ["input", "0", "a", "float32", "2,3"],
  ["op", "0", "softmax", "", "input", "0.0", "axis", "1"], ["op", "0", "leakyRelu", "", "input", "0.1"],
  ["build", "0", "out", "0.2"]]).1.builders[0]?.bind (·.gpu)).isSome
#guard ((run gpuPage [["context", "gpu"], ["builder", "0"], ["input", "0", "a", "float32", "2,3"],
  ["op", "0", "elu", "", "input", "0.0"], ["build", "0", "out", "0.1"]]).1.builders[0]?.bind (·.gpu)).isNone
-- tanh is outside the tolerance on the GPU: the graph runs on the CPU reference
#guard ((graph "gpu" "tanh").1.builders[0]?.bind (·.gpu)).isNone
#guard ((graph "gpu" "tanh").1.tensors[2]?.map (·.onGpu)) == some false
-- a context without deviceType "gpu", or an embedder without GPU replay: the CPU reference
#guard ((graph "" "relu").1.builders[0]?.bind (·.gpu)).isNone
#guard ((graph "gpu" "relu" { gpuPage with page := L4Factoidal.PageGpu.State.empty 3 false }).1.builders[0]?.bind (·.gpu)).isNone
#guard (graph "gpu" "relu" { gpuPage with page := L4Factoidal.PageGpu.State.empty 3 false }).2.getLast? == some ""
-- exportable tensors: only on a GPU context; exported, WebNN may not write or read it until
-- the page's GPUBuffer of it is destroyed (import)
def exported : State × List String := run gpuPage [["context", "gpu"], ["tensor", "0", "float32", "4", "xrw"],
  ["export", "0", "0"], ["write", "0", "0", "f32", "AAAAAAAAAAAAAAAAAAAAAA"], ["import", "0"]]
#guard (exported.2.getD 2 "").toNat? == some 1073741824
#guard (exported.2.getD 3 "").startsWith "!T"
#guard (exported.1.tensors[0]?.map (·.exported)) == some false
#guard ((run gpuPage [["context", ""], ["tensor", "0", "float32", "4", "xrw"]]).2.getD 1 "").startsWith "!DNotSupportedError"
-- the CPU reference answers readTensor with its bytes (byte 0)
#guard ((api (graph "gpu" "tanh").1 #["read".toUTF8, "0".toUTF8, "2".toUTF8]).2.get! 0) == 0
end Tests
#print axioms L4Factoidal.WebNN.Gpu.emitC_eval
#print axioms L4Factoidal.WebNN.GpuRun.emit_inv
#print axioms L4Factoidal.WebNN.Gpu.unravel_getD
#print axioms L4Factoidal.WebNN.Gpu.transpose_coords
#print axioms L4Factoidal.WebNN.Gpu.expandMap_fits
#print axioms L4Factoidal.WebNN.Gpu.tileMap_fits
#print axioms L4Factoidal.WebNN.transposeMap_eval
#print axioms L4Factoidal.WebNN.expandMap_eval

end L4Factoidal.WebNN.GpuRun
