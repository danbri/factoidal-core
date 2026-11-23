import EVMCleanroom.HeaderChain
import EVMCleanroom.Keccak

/-! Bounded canonical RLP encoding of mainnet legacy and London-family
headers through Prague (before Osaka). The header fields are untrusted byte strings,
not an authenticated block. The same checked fields supply the link,
gas and fee data. No external hashing implementation is used. -/
namespace EVMCleanroom.HeaderRLP

abbrev Fields := Array (Array UInt8)
def shanghaiTime : Nat := 1681338455
def cancunTime : Nat := 1710338135
def pragueTime : Nat := 1746612311
def osakaTime : Nat := 1764798551

inductive Error where
  | unsupportedLayout
  | invalidShape
  | laterFork
  | wrongForkShape
  | chain (e : HeaderChain.Error)
  deriving Repr

def field (h : Fields) (i : Nat) : Array UInt8 := (h[i]?).getD #[]

def readNat (h : Fields) (i : Nat) : Nat :=
  (field h i).foldl (fun acc b => acc * 256 + b.toNat) 0

def minimal (b : Array UInt8) (maxBytes : Nat) : Bool :=
  b.size <= maxBytes && (b.isEmpty || (b[0]?).getD 0 != 0)

def layout (h : Fields) : Bool :=
  h.size == 15 || h.size == 16 || h.size == 17 ||
  h.size == 20 || h.size == 21

/-- The execution header field count follows mainnet activation, not the
caller-supplied count. Osaka and later are refused separately. -/
def expectedFieldCount (number timestamp : Nat) : Nat :=
  if timestamp >= pragueTime then 21
  else if timestamp >= cancunTime then 20
  else if timestamp >= shanghaiTime then 17
  else if number >= HeaderChain.londonHeight then 16
  else 15

def forkShape (h : Fields) : Bool :=
  h.size == expectedFieldCount (readNat h 8) (readNat h 11) &&
    (readNat h 11 < shanghaiTime || readNat h 8 >= HeaderChain.londonHeight)

def validShape (h : Fields) : Bool :=
  (field h 0).size == 32 && (field h 1).size == 32 &&
  (field h 2).size == 20 && (field h 3).size == 32 &&
  (field h 4).size == 32 && (field h 5).size == 32 &&
  (field h 6).size == 256 && minimal (field h 7) 32 &&
  minimal (field h 8) 8 && minimal (field h 9) 8 &&
  minimal (field h 10) 8 && minimal (field h 11) 8 &&
  (field h 12).size <= 32 && (field h 13).size == 32 &&
  (field h 14).size == 8 &&
  (h.size < 16 || minimal (field h 15) 32) &&
  (h.size < 17 || (field h 16).size == 32) &&
  (h.size < 20 || (minimal (field h 17) 8 &&
    minimal (field h 18) 8 && (field h 19).size == 32)) &&
  (h.size < 21 || (field h 20).size == 32)

/-- Only used after the fixed header layout and widths are checked:
every string and the complete payload fit in two length bytes. -/
private def lengthPrefix (shortBase longBase n : Nat) : Array UInt8 :=
  if n <= 55 then #[UInt8.ofNat (shortBase + n)]
  else if n < 256 then #[UInt8.ofNat (longBase + 1), UInt8.ofNat n]
  else #[UInt8.ofNat (longBase + 2), UInt8.ofNat (n / 256), UInt8.ofNat (n % 256)]

private def encodeString (b : Array UInt8) : Array UInt8 :=
  if b.size == 1 && (b[0]?).getD 0 < 128 then b
  else lengthPrefix 128 183 b.size ++ b

private def encodeFlat (h : Fields) : Array UInt8 :=
  let payload := h.foldl (fun acc b => acc ++ encodeString b) #[]
  lengthPrefix 192 247 payload.size ++ payload

def wire (h : Fields) : Except Error (Array UInt8) :=
  if !layout h then .error .unsupportedLayout
  else if !validShape h then .error .invalidShape
  else if readNat h 11 >= osakaTime then .error .laterFork
  else if !forkShape h then
    .error .wrongForkShape
  else .ok (encodeFlat h)

private def hashWire (acceptance : Keccak.Acceptance) (bytes : Array UInt8) : Nat :=
  Keccak.experimentalDigestWord acceptance (ByteView.ofArray bytes)

def hash (acceptance : Keccak.Acceptance) (h : Fields) :
    Except Error (Array UInt8 × Nat) :=
  match wire h with
  | .error e => .error e
  | .ok bytes => .ok (bytes, hashWire acceptance bytes)

def pairInput (parent child : Fields) (digest : Nat) : HeaderChain.Pair :=
  { parentNumber := readNat parent 8
    parentTimestamp := readNat parent 11
    parentHash := digest
    parentGasLimit := readNat parent 9
    parentGasUsed := readNat parent 10
    parentBaseFee := if parent.size >= 16 then some (readNat parent 15) else none
    childNumber := readNat child 8
    childTimestamp := readNat child 11
    childParentHash := readNat child 0
    childGasLimit := readNat child 9
    childGasUsed := readNat child 10
    childBaseFee := readNat child 15 }

def pairResult (p : HeaderChain.Pair) : Except Error Nat :=
  match HeaderChain.check p with
  | .error e => .error (.chain e)
  | .ok fee => .ok fee

def checkPair (acceptance : Keccak.Acceptance) (parent child : Fields) :
    Except Error Nat :=
  match wire parent with
  | .error e => .error e
  | .ok bytes =>
    match wire child with
    | .error e => .error e
    | .ok _ => pairResult (pairInput parent child (hashWire acceptance bytes))

/-- Kind: admission. Says: unsupported field count cannot produce wire bytes.
Does not say: all later fork headers are invalid. -/
theorem layout_refused (h : Fields) (hl : layout h = false) :
    wire h = .error .unsupportedLayout := by
  simp [wire, hl]

/-- Kind: admission. Says: malformed widths or integers refuse encoding.
Does not say: the supplied fields are authenticated. -/
theorem shape_refused (h : Fields) (hl : layout h = true)
    (hs : validShape h = false) : wire h = .error .invalidShape := by
  simp [wire, hl, hs]

/-- Kind: executable connection. Says: accepted bytes are the actual
ordered flat encoding. Does not say: independent RLP refinement is proved. -/
theorem wire_exact {h : Fields} {bytes : Array UInt8}
    (hw : wire h = .ok bytes) : bytes = encodeFlat h := by
  unfold wire at hw
  split at hw
  · simp at hw
  · split at hw
    · simp at hw
    · split at hw
      · simp at hw
      · split at hw
        · simp at hw
        · exact (Except.ok.inj hw).symm

/-- Kind: executable connection. Says: the hash uses the actual encoded
wire. Does not say: cryptographic refinement or collision resistance. -/
theorem hash_exact (a : Keccak.Acceptance) (h : Fields) (bytes : Array UInt8)
    (hw : wire h = .ok bytes) :
    hash a h = .ok (bytes, hashWire a bytes) := by
  simp [hash, hw]

/-- Kind: admission. Says: parent encoding failure propagates.
Does not say: all valid historical headers are supported. -/
theorem parent_refused (a : Keccak.Acceptance) (parent child : Fields) (e : Error)
    (hp : wire parent = .error e) :
    checkPair a parent child = .error e := by
  simp [checkPair, hp]

/-- Kind: admission. Says: child encoding failure propagates.
Does not say: successful encoding implies consensus validity. -/
theorem child_refused (a : Keccak.Acceptance) (parent child : Fields)
    (pb : Array UInt8) (e : Error) (hp : wire parent = .ok pb)
    (hc : wire child = .error e) :
    checkPair a parent child = .error e := by
  simp [checkPair, hp, hc]

/-- Kind: executable composition. Says: admitted headers use the same
fields and computed parent digest in the existing chain checker.
Does not say: the pair belongs to the canonical chain. -/
theorem pair_connected (a : Keccak.Acceptance) (parent child : Fields)
    (pb cb : Array UInt8) (hp : wire parent = .ok pb) (hc : wire child = .ok cb) :
    checkPair a parent child =
      pairResult (pairInput parent child (hashWire a pb)) := by
  simp [checkPair, hp, hc]

/-- Kind: admission. Says: a supported-width pre-Osaka header with
the wrong fork field count cannot produce wire bytes.
Does not say: its timestamp belongs to an authenticated chain. -/
theorem fork_shape_refused (h : Fields) (hl : layout h = true)
    (hs : validShape h = true) (ht : readNat h 11 < osakaTime)
    (hf : forkShape h = false) :
    wire h = .error .wrongForkShape := by
  simp [wire, hl, hs, Nat.not_le.mpr ht, hf]

/-- Kind: executable connection. Says: every London-family layout
passes the original fee field to the actual pair checker.
Does not say: the supplied base fee satisfies the recurrence. -/
theorem parent_fee_present (parent child : Fields) (digest : Nat)
    (h : 16 <= parent.size) :
    (pairInput parent child digest).parentBaseFee = some (readNat parent 15) := by
  simp [pairInput, h]

#guard expectedFieldCount 12965000 1681338454 == 16
#guard expectedFieldCount 17034870 1681338455 == 17
#guard expectedFieldCount 19426587 1710338134 == 17
#guard expectedFieldCount 19426589 1710338135 == 20
#guard expectedFieldCount 22431083 1746612310 == 20
#guard expectedFieldCount 22431084 1746612311 == 21

#print axioms fork_shape_refused
#print axioms parent_fee_present
#print axioms layout_refused
#print axioms shape_refused
#print axioms wire_exact
#print axioms hash_exact
#print axioms parent_refused
#print axioms child_refused
#print axioms pair_connected

end EVMCleanroom.HeaderRLP
