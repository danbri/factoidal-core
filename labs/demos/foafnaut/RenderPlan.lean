import Init

/- Closed rendering policy for the experimental lab, not a general GPU API.
   The host supplies actual device limits and preferred surface format. It must
   interpret the returned descriptors/trace, check numeric wire values and the
   actual Float32Array length, and stop on GPU errors. No theorem here verifies
   that interpreter, native handles, host facts, WGSL semantics, or the driver.
   Persistent allocation, resize/visibility/dirty decisions, and failure-path
   resource cleanup remain host policy in this first increment. -/
namespace NativeRenderPlan

inductive Mode where | window | offscreen
  deriving Repr, BEq, DecidableEq
inductive Format where | rgba8unorm | bgra8unorm
  deriving Repr, BEq, DecidableEq
inductive Command where
  | beginPass | setPipeline | setBindGroup | draw | endPass
  | copyTextureToBuffer | submit | present | mapRead | readMapped | unmap
  deriving Repr, BEq, DecidableEq

def Mode.wire : Mode → String
  | .window => "window" | .offscreen => "offscreen"
def Format.wire : Format → String
  | .rgba8unorm => "rgba8unorm" | .bgra8unorm => "bgra8unorm"
def Command.wire : Command → String
  | .beginPass => "beginPass" | .setPipeline => "setPipeline"
  | .setBindGroup => "setBindGroup" | .draw => "draw" | .endPass => "endPass"
  | .copyTextureToBuffer => "copyTextureToBuffer" | .submit => "submit"
  | .present => "present" | .mapRead => "mapRead" | .readMapped => "readMapped"
  | .unmap => "unmap"

def commands (mode : Mode) : List Command :=
  [.beginPass,.setPipeline,.setBindGroup,.draw,.endPass] ++
  match mode with
  | .window => [.submit,.present]
  | .offscreen => [.copyTextureToBuffer,.submit,.mapRead,.readMapped,.unmap]

structure DrawCall where
  vertexCount : Nat
  instanceCount : Nat
  firstVertex : Nat
  firstInstance : Nat
  deriving Repr, BEq

def drawCall : DrawCall := ⟨3,1,0,0⟩

inductive EntryPoint where | vertex | fragment
  deriving Repr, BEq, DecidableEq
inductive Layout where | automatic
  deriving Repr, BEq, DecidableEq
inductive Topology where | triangleList
  deriving Repr, BEq, DecidableEq
inductive BufferUse where | uniform | copyDst | mapRead
  deriving Repr, BEq, DecidableEq
inductive TextureUse where | renderAttachment | copySrc
  deriving Repr, BEq, DecidableEq
inductive LoadOp where | clear
  deriving Repr, BEq, DecidableEq
inductive StoreOp where | store
  deriving Repr, BEq, DecidableEq

def EntryPoint.wire : EntryPoint → String
  | .vertex => "vertex" | .fragment => "fragment"
def Layout.wire : Layout → String | .automatic => "auto"
def Topology.wire : Topology → String | .triangleList => "triangle-list"
def BufferUse.wire : BufferUse → String
  | .uniform => "uniform" | .copyDst => "copy-dst" | .mapRead => "map-read"
def TextureUse.wire : TextureUse → String
  | .renderAttachment => "render-attachment" | .copySrc => "copy-src"
def LoadOp.wire : LoadOp → String | .clear => "clear"
def StoreOp.wire : StoreOp → String | .store => "store"

structure PipelineDescriptor where
  layout : Layout
  vertexEntry : EntryPoint
  fragmentEntry : EntryPoint
  topology : Topology
structure BindingDescriptor where
  index : Nat
  layoutIndex : Nat
  binding : Nat
structure PassDescriptor where
  clearR : Nat
  clearG : Nat
  clearB : Nat
  clearA : Nat
  load : LoadOp
  store : StoreOp

def pipeline : PipelineDescriptor := ⟨.automatic,.vertex,.fragment,.triangleList⟩
def bindGroup : BindingDescriptor := ⟨0,0,0⟩
def renderPass : PassDescriptor := ⟨0,0,0,1,.clear,.store⟩
def uniformUsage : List BufferUse := [.uniform,.copyDst]
def readbackUsage : List BufferUse := [.copyDst,.mapRead]
def targetUsage : Mode → List TextureUse
  | .window => [.renderAttachment] | .offscreen => [.renderAttachment,.copySrc]

def rowBlocks (width : Nat) : Nat :=
  width / 64 + if width % 64 == 0 then 0 else 1
def bytesPerRow (width : Nat) : Nat := 256 * rowBlocks width
def readbackBytes (width height : Nat) : Nat := bytesPerRow width * height

-- Canonical RGBA8 copy rows cover every pixel and obey WebGPU's 256-byte
-- copyTextureToBuffer row alignment, including already aligned widths.
theorem bytesPerRow_aligned (width : Nat) : bytesPerRow width % 256 = 0 := by
  exact Nat.mul_mod_right _ _

theorem bytesPerRow_covers (width : Nat) : 4 * width ≤ bytesPerRow width := by
  by_cases h : width % 64 = 0
  · have whole : 64 * (width / 64) = width := by
      simpa [h] using Nat.div_add_mod width 64
    have exactRow : 4 * width = 256 * (width / 64) := by
      calc
        4 * width = 4 * (64 * (width / 64)) := congrArg (4 * ·) whole.symm
        _ = 256 * (width / 64) := (Nat.mul_assoc 4 64 (width / 64)).symm
    simp [bytesPerRow, rowBlocks, h, exactRow]
  · have remainder : width % 64 ≤ 64 := Nat.le_of_lt (Nat.mod_lt width (by decide))
    have bound : width ≤ 64 * (width / 64) + 64 := by
      calc
        width = 64 * (width / 64) + width % 64 := (Nat.div_add_mod width 64).symm
        _ ≤ 64 * (width / 64) + 64 := Nat.add_le_add_left remainder _
    have cover : 4 * width ≤ 256 * (width / 64 + 1) := by
      calc
        4 * width ≤ 4 * (64 * (width / 64) + 64) := Nat.mul_le_mul_left 4 bound
        _ = 256 * (width / 64 + 1) := by simp [Nat.mul_add, ← Nat.mul_assoc]
    simpa [bytesPerRow, rowBlocks, h] using cover

theorem readbackBytes_covers (width height : Nat) :
    (4 * width) * height ≤ readbackBytes width height := by
  exact Nat.mul_le_mul_right height (bytesPerRow_covers width)

-- Input-indexed plans retain the connection between each accepted request and
-- the values that were actually validated. Proof fields erase at extraction.
structure Plan (width height floatCount maxUniformBytes maxDimension : Nat) where
  mode : Mode
  format : Format
  widthPositive : 0 < width
  heightPositive : 0 < height
  widthBound : width ≤ maxDimension
  heightBound : height ≤ maxDimension
  floatsPositive : 0 < floatCount
  vec4Aligned : 4 * (floatCount / 4) = floatCount
  uniformBound : 4 * floatCount ≤ maxUniformBytes
  offscreenFormat : mode = .offscreen → format = .rgba8unorm

def plan (mode format : String)
    (width height floatCount maxUniformBytes maxDimension : Nat) :
    Except String (Plan width height floatCount maxUniformBytes maxDimension) := do
  let selectedMode ← match mode with
    | "window" => pure Mode.window | "offscreen" => pure Mode.offscreen
    | _ => throw "mode must be window or offscreen"
  let selectedFormat ← match format with
    | "rgba8unorm" => pure Format.rgba8unorm | "bgra8unorm" => pure Format.bgra8unorm
    | _ => throw "format must be rgba8unorm or bgra8unorm"
  if hw : 0 < width then
    if hh : 0 < height then
      if hwb : width ≤ maxDimension then
        if hhb : height ≤ maxDimension then
          if hp : 0 < floatCount then
            if ha : 4 * (floatCount / 4) = floatCount then
              if hb : 4 * floatCount ≤ maxUniformBytes then
                let actualFormat := match selectedMode with
                  | .window => selectedFormat | .offscreen => Format.rgba8unorm
                return {
                  mode := selectedMode, format := actualFormat,
                  widthPositive := hw, heightPositive := hh,
                  widthBound := hwb, heightBound := hhb,
                  floatsPositive := hp, vec4Aligned := ha, uniformBound := hb,
                  offscreenFormat := by cases selectedMode <;> simp_all [actualFormat] }
              else throw "uniform bytes exceed device limit"
            else throw "floatCount must contain complete vec4 rows"
          else throw "floatCount must be positive"
        else throw "height exceeds device limit"
      else throw "width exceeds device limit"
    else throw "height must be positive"
  else throw "width must be positive"

theorem accepted_bounds {width height floatCount maxUniformBytes maxDimension : Nat}
    (p : Plan width height floatCount maxUniformBytes maxDimension) :
    0 < width ∧ 0 < height ∧ width ≤ maxDimension ∧ height ≤ maxDimension ∧
    0 < floatCount ∧ 4 * floatCount ≤ maxUniformBytes :=
  ⟨p.widthPositive,p.heightPositive,p.widthBound,p.heightBound,p.floatsPositive,p.uniformBound⟩

theorem accepted_uniform_rows {width height floatCount maxUniformBytes maxDimension : Nat}
    (p : Plan width height floatCount maxUniformBytes maxDimension) :
    4 * floatCount = 16 * (floatCount / 4) := by
  calc
    4 * floatCount = 4 * (4 * (floatCount / 4)) := congrArg (4 * ·) p.vec4Aligned.symm
    _ = 16 * (floatCount / 4) := (Nat.mul_assoc 4 4 (floatCount / 4)).symm

theorem draw_triangle : drawCall.vertexCount = 3 ∧ drawCall.instanceCount = 1 ∧
    drawCall.firstVertex = 0 ∧ drawCall.firstInstance = 0 := ⟨rfl,rfl,rfl,rfl⟩

theorem pipeline_contract : pipeline.layout = .automatic ∧ pipeline.vertexEntry = .vertex ∧
    pipeline.fragmentEntry = .fragment ∧ pipeline.topology = .triangleList := ⟨rfl,rfl,rfl,rfl⟩
theorem binding_contract : bindGroup.index = 0 ∧ bindGroup.layoutIndex = 0 ∧ bindGroup.binding = 0 :=
  ⟨rfl,rfl,rfl⟩
theorem pass_contract : renderPass.clearR = 0 ∧ renderPass.clearG = 0 ∧
    renderPass.clearB = 0 ∧ renderPass.clearA = 1 ∧ renderPass.load = .clear ∧ renderPass.store = .store :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem window_submit_before_present :
    commands .window = [.beginPass,.setPipeline,.setBindGroup,.draw,.endPass,.submit,.present] := rfl
theorem offscreen_copy_submit_map_read :
    commands .offscreen = [.beginPass,.setPipeline,.setBindGroup,.draw,.endPass,
      .copyTextureToBuffer,.submit,.mapRead,.readMapped,.unmap] := rfl
theorem offscreen_no_present : Command.present ∉ commands .offscreen := by
  simp [commands]

private def quote (s : String) : String :=
  "\"" ++ (s.replace "\\" "\\\\" |>.replace "\"" "\\\"" |>.replace "\n" "\\n") ++ "\""
private def number (n : Nat) : String := toString n
private def strings (xs : List String) : String := "[" ++ String.intercalate "," (xs.map quote) ++ "]"

def Plan.json {width height floatCount maxUniformBytes maxDimension : Nat}
    (p : Plan width height floatCount maxUniformBytes maxDimension) : String :=
  let target := match p.mode with
    | .window => "\"surface\":{\"alphaMode\":\"opaque\",\"usage\":" ++
        strings ((targetUsage p.mode).map TextureUse.wire) ++ "}"
    | .offscreen => "\"texture\":{\"usage\":" ++ strings ((targetUsage p.mode).map TextureUse.wire) ++ ",\"depth\":1}," ++
        "\"readback\":{\"offset\":0,\"bytesPerRow\":" ++ number (bytesPerRow width) ++
        ",\"rowsPerImage\":" ++ number height ++ ",\"bytes\":" ++ number (readbackBytes width height) ++
        ",\"usage\":" ++ strings (readbackUsage.map BufferUse.wire) ++ ",\"mapMode\":\"read\",\"copyExtent\":[" ++
        number width ++ "," ++ number height ++ ",1]}"
  "{\"abi\":\"lean-render-plan-v1\",\"mode\":" ++ quote p.mode.wire ++
  ",\"width\":" ++ number width ++ ",\"height\":" ++ number height ++
  ",\"format\":" ++ quote p.format.wire ++
  ",\"uniform\":{\"floatCount\":" ++ number floatCount ++ ",\"rowCount\":" ++ number (floatCount/4) ++
  ",\"bytes\":" ++ number (4*floatCount) ++ ",\"offset\":0,\"usage\":" ++ strings (uniformUsage.map BufferUse.wire) ++ "}," ++
  "\"pipeline\":{\"layout\":" ++ quote pipeline.layout.wire ++ ",\"vertexEntry\":" ++ quote pipeline.vertexEntry.wire ++
  ",\"fragmentEntry\":" ++ quote pipeline.fragmentEntry.wire ++ ",\"topology\":" ++ quote pipeline.topology.wire ++ "}," ++
  "\"bindGroup\":{\"index\":" ++ number bindGroup.index ++ ",\"layoutIndex\":" ++ number bindGroup.layoutIndex ++
  ",\"binding\":" ++ number bindGroup.binding ++ "}," ++
  "\"pass\":{\"clear\":[" ++ String.intercalate "," ([renderPass.clearR,renderPass.clearG,renderPass.clearB,renderPass.clearA].map number) ++
  "],\"load\":" ++ quote renderPass.load.wire ++ ",\"store\":" ++ quote renderPass.store.wire ++ "}," ++
  "\"draw\":{\"vertexCount\":" ++ number drawCall.vertexCount ++
  ",\"instanceCount\":" ++ number drawCall.instanceCount ++
  ",\"firstVertex\":" ++ number drawCall.firstVertex ++
  ",\"firstInstance\":" ++ number drawCall.firstInstance ++ "}," ++ target ++
  ",\"commands\":[" ++ String.intercalate "," ((commands p.mode).map (quote ∘ Command.wire)) ++ "]}"

def request (mode format : String)
    (width height floatCount maxUniformBytes maxDimension : Nat) : String :=
  match plan mode format width height floatCount maxUniformBytes maxDimension with
  | .ok p => p.json
  | .error message => "{\"error\":" ++ quote message ++ "}"

@[export render_plan_request]
def requestABI (mode format : String)
    (width height floatCount maxUniformBytes maxDimension : UInt32) : String :=
  request mode format width.toNat height.toNat floatCount.toNat maxUniformBytes.toNat maxDimension.toNat

end NativeRenderPlan
