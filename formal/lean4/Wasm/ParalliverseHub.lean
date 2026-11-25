import L4Factoidal.Paralliverse.PackWire
import L4Factoidal.Paralliverse.WGSL.ShaderText
import L4Factoidal.Paralliverse.Studio

namespace L4Factoidal.Paralliverse.Hub

/-- The byte limit is also available to the host before it copies a request. -/
@[export paralliverse_hub_input_limit]
def inputLimit (op : UInt32) : UInt32 :=
  if op == 0 then UInt32.ofNat PackWire.maxEditorBytes
  else if op == 1 then UInt32.ofNat PackWire.maxPacketBytes
  else if op == 2 then 1
  else if op == 3 then UInt32.ofNat Studio.maxRequestBytes
  else if op == 4 then 1
  else 0

/-- Operation 0 prepares a packet, operation 1 runs stable pack, operation 2
selects a fixed shader, operation 3 evaluates a Studio request, and operation 4
reports the byte and command limits. -/
def call (op : UInt32) (src : ByteArray) : Except PackWire.Error ByteArray := do
  if op == 0 then PackWire.prepare src
  else if op == 1 then
    let rows ← PackWire.decode src
    return PackWire.outputWords (StaticPack.packSpec rows)
  else if op == 2 then
    if src.size != 1 then throw (.invalid "Shader selection requires exactly one byte.")
    match (src.data[0]? : Option UInt8) with
    | some 0 => return WGSL.countText.toUTF8
    | some 1 => return WGSL.scanText.toUTF8
    | some 2 => return WGSL.scatterText.toUTF8
    | some 3 => return WordMapGPU.KernelTag.add.shader.toUTF8
    | some 4 => return WordMapGPU.KernelTag.multiply.shader.toUTF8
    | _ => throw (.invalid "The shader selector is unsupported.")
  else if op == 3 then Studio.call src
  else if op == 4 then
    if src.size = 0 then .ok Studio.capabilityBytes
    else .error (.invalid "Studio capabilities require an empty request.")
  else throw (.invalid "The operation is unsupported.")

/-- Response byte 0 is the status (0 success, 1 malformed, 2 limit). The
remaining bytes are the result on success or a UTF-8 diagnostic on failure. -/
@[export paralliverse_hub_call]
def callExport (op : UInt32) (src : ByteArray) : ByteArray :=
  let (status, body) : UInt8 × ByteArray :=
    match call op src with
    | .ok bytes => (0, bytes)
    | .error (.invalid message) => (1, message.toUTF8)
    | .error (.limit message) => (2, message.toUTF8)
  (ByteArray.empty.push status) ++ body

set_option maxRecDepth 8192 in
/-- Kind: exported byte equality.
Says: all three valid one-byte selectors return the exact shader source under the
existing success envelope, and the advertised input limit is one byte.
Does not say: that a linked Wasm shim or GPU implementation transmits these bytes faithfully. -/
theorem shader_source_exports :
    inputLimit 2 = 1 ∧
      callExport 2 ⟨#[0]⟩ = (ByteArray.empty.push 0) ++ WGSL.countText.toUTF8 ∧
      callExport 2 ⟨#[1]⟩ = (ByteArray.empty.push 0) ++ WGSL.scanText.toUTF8 ∧
      callExport 2 ⟨#[2]⟩ = (ByteArray.empty.push 0) ++ WGSL.scatterText.toUTF8 :=
  ⟨rfl, rfl, rfl, rfl⟩

#print axioms shader_source_exports

set_option maxRecDepth 8192 in
/-- Kind: exported operation correspondence.
Says: both word-map shader selectors return the fixed source bytes and every
Studio request enters the Lean Studio evaluator under its advertised byte cap.
Does not say: the linked Wasm shim or a device transmits these bytes faithfully. -/
theorem studio_exports :
    inputLimit 3 = UInt32.ofNat Studio.maxRequestBytes ∧
    (∀ src, call 3 src = Studio.call src) ∧
    callExport 2 ⟨#[WordMapGPU.KernelTag.add.shaderSelector]⟩ =
      (ByteArray.empty.push 0) ++ WordMapGPU.KernelTag.add.shader.toUTF8 ∧
    callExport 2 ⟨#[WordMapGPU.KernelTag.multiply.shaderSelector]⟩ =
      (ByteArray.empty.push 0) ++ WordMapGPU.KernelTag.multiply.shader.toUTF8 :=
  ⟨rfl, fun _ => rfl, rfl, rfl⟩

#print axioms studio_exports

/-- Kind: capability discovery.
Says: the empty request exports the Lean capability record and all nonempty
capability requests receive a refusal in the Lean dispatcher.
Does not say: that an external runtime exposes this operation. -/
theorem capability_exports :
    inputLimit 4 = 1 ∧ callExport 4 ByteArray.empty = (ByteArray.empty.push 0) ++ Studio.capabilityBytes ∧
    ∀ src : ByteArray, src.size ≠ 0 → call 4 src = .error (.invalid "Studio capabilities require an empty request.") :=
  ⟨rfl, rfl, fun _ h => if_neg h⟩

#print axioms capability_exports

end L4Factoidal.Paralliverse.Hub
