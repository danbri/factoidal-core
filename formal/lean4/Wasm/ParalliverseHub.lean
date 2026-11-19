import L4Factoidal.Paralliverse.PackWire

namespace L4Factoidal.Paralliverse.Hub

/-- The byte limit is also available to the host before it copies a request. -/
@[export paralliverse_hub_input_limit]
def inputLimit (op : UInt32) : UInt32 :=
  if op == 0 then UInt32.ofNat PackWire.maxEditorBytes
  else if op == 1 then UInt32.ofNat PackWire.maxPacketBytes
  else 0

/-- Operation 0 prepares the editor bytes as an input packet. Operation 1
decodes that same packet and calls the ordinary stable-pack function. -/
def call (op : UInt32) (src : ByteArray) : Except PackWire.Error ByteArray := do
  if op == 0 then PackWire.prepare src
  else if op == 1 then
    let rows ← PackWire.decode src
    return PackWire.outputWords (StaticPack.packSpec rows)
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

end L4Factoidal.Paralliverse.Hub
