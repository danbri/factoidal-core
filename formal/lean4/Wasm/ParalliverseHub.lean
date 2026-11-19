import L4Factoidal.Paralliverse.PackWire
import L4Factoidal.Paralliverse.WGSL.ShaderText

namespace L4Factoidal.Paralliverse.Hub

/-- The byte limit is also available to the host before it copies a request. -/
@[export paralliverse_hub_input_limit]
def inputLimit (op : UInt32) : UInt32 :=
  if op == 0 then UInt32.ofNat PackWire.maxEditorBytes
  else if op == 1 then UInt32.ofNat PackWire.maxPacketBytes
  else if op == 2 then 1
  else 0

/-- Operation 0 prepares a packet and operation 1 runs the ordinary stable pack.
Operation 2 returns the UTF-8 shader selected by one byte, in Count/Scan/Scatter order. -/
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
    | _ => throw (.invalid "The shader selector is unsupported.")
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

end L4Factoidal.Paralliverse.Hub
