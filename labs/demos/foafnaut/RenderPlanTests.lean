import RenderPlan

namespace NativeRenderPlan.Tests
open NativeRenderPlan

private def refused {α : Type} : Except String α → Bool
  | .error _ => true | .ok _ => false

-- Actual planning paths: invalid host inputs cannot produce a descriptor trace.
#guard refused (plan "other" "rgba8unorm" 64 64 16 65536 4096)
#guard refused (plan "window" "other" 64 64 16 65536 4096)
#guard refused (plan "window" "bgra8unorm" 0 64 16 65536 4096)
#guard refused (plan "window" "bgra8unorm" 64 4097 16 65536 4096)
#guard refused (plan "window" "bgra8unorm" 64 64 0 65536 4096)
#guard refused (plan "window" "bgra8unorm" 64 64 15 65536 4096)
#guard refused (plan "window" "bgra8unorm" 64 64 16 63 4096)

#guard match plan "window" "bgra8unorm" 64 64 16 64 64 with
  | .ok p => p.mode == .window && p.format == .bgra8unorm
  | .error _ => false
#guard match plan "offscreen" "bgra8unorm" 65 7 16 64 65 with
  | .ok p => p.mode == .offscreen && p.format == .rgba8unorm
  | .error _ => false

-- Copy boundaries catch the aligned-width over-allocation/off-by-one cases.
#guard bytesPerRow 1 == 256
#guard bytesPerRow 63 == 256
#guard bytesPerRow 64 == 256
#guard bytesPerRow 65 == 512
#guard readbackBytes 65 7 == 3584

-- These statements are checked by the kernel, not native_decide.
example (width : Nat) : bytesPerRow width % 256 = 0 := bytesPerRow_aligned width
example (width height : Nat) : (4*width)*height ≤ readbackBytes width height :=
  readbackBytes_covers width height
example : commands .window = [.beginPass,.setPipeline,.setBindGroup,.draw,.endPass,.submit,.present] :=
  window_submit_before_present
example : Command.present ∉ commands .offscreen := offscreen_no_present

end NativeRenderPlan.Tests

-- A small real serializer smoke stream for a standard JSON parser, not a GPU.
def main : IO Unit := do
  IO.println (NativeRenderPlan.request "window" "bgra8unorm" 64 64 16 64 64)
  IO.println (NativeRenderPlan.request "offscreen" "bgra8unorm" 65 7 16 64 65)
  IO.println (NativeRenderPlan.request "window" "rgba8unorm" 64 64 15 65536 4096)
  IO.println (NativeRenderPlan.request "window" "rgba8unorm" 64 64 16 63 4096)
