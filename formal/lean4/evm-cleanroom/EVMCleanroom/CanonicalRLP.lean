import Std

/-!
# Canonical RLP views for authenticated Ethereum witnesses

Independent implementation of the byte/list encoding described in the Yellow
Paper, Appendix B, and ethereum.org's RLP specification. Issue #1043.

`decode` accepts exactly one recursively canonical RLP item. It retains the
original encoded bytes: callers hashing an inline trie node must hash those
bytes, not a reconstructed encoding. Descendants are validated with an explicit
stack of byte ranges, not a recursive syntax tree. No advertised payload length
is allocated before it has been checked against the actual input.

The local limits (4,096 encoded bytes and 64 nested lists) are resource policy,
not Ethereum invalidity. `resourceLimit` remains separate from `malformed`.
Integer minimality belongs to `scalar`, not to byte-string decoding: the byte
0x00 is canonical RLP data but is not a canonical encoding of integer zero.

These are operational admission/bounds theorems. A complete refinement proof
against an independently formalised RLP grammar remains open.
-/
namespace EVMCleanroom.CanonicalRLP

inductive Error where
  | malformed (reason : String)
  | resourceLimit
  deriving Repr, BEq

structure Item where
  isList : Bool
  payload : Array UInt8
  encoded : Array UInt8
  deriving Repr, BEq

def maxInputBytes : Nat := 4096
def maxListDepth : Nat := 64

/-- Byte positions only. Constructing this header does not allocate a payload. -/
structure Header where
  isList : Bool
  payloadStart : Nat
  stop : Nat
  deriving Repr, BEq

/-- One nonempty range of adjacent items still to validate. -/
structure Segment where
  start : Nat
  stop : Nat
  listDepth : Nat
  deriving Repr

private def byte (input : Array UInt8) (i : Nat) : UInt8 :=
  (input[i]?).getD 0

/-- The caller checks the at-most-eight length bytes before entering this loop. -/
private def lengthLoop (input : Array UInt8) : Nat → Nat → Nat → Nat
  | 0, _, value => value
  | remaining + 1, pos, value =>
    lengthLoop input remaining (pos + 1) (value * 256 + (byte input pos).toNat)

/-- Every successful header advances the cursor and stays inside its containing
range. This is checked before `view` extracts either returned byte array. -/
def admitHeader (inputSize start limit : Nat) (h : Header) : Except Error Header :=
  if start < h.stop ∧ start ≤ h.payloadStart ∧ h.payloadStart ≤ h.stop ∧
      h.stop ≤ limit ∧ limit ≤ inputSize then
    .ok h
  else .error (.malformed "truncated item")

private def longHeader (input : Array UInt8) (start limit width : Nat)
    (isList : Bool) : Except Error Header :=
  let lengthStart := start + 1
  let payloadStart := lengthStart + width
  if payloadStart > limit then .error (.malformed "truncated length")
  else if byte input lengthStart == 0 then
    .error (.malformed "nonminimal length")
  else
    let size := lengthLoop input width lengthStart 0
    if size < 56 then .error (.malformed "nonminimal long form")
    else .ok ⟨isList, payloadStart, payloadStart + size⟩

private def headerShape (input : Array UInt8) (start limit : Nat) :
    Except Error Header :=
  if start ≥ limit ∨ limit > input.size then
    .error (.malformed "missing prefix")
  else
    let tag := (byte input start).toNat
    if tag < 128 then .ok ⟨false, start, start + 1⟩
    else if tag < 184 then
      let size := tag - 128
      let payloadStart := start + 1
      if size == 1 && (byte input payloadStart).toNat < 128 then
        .error (.malformed "nonminimal single byte")
      else .ok ⟨false, payloadStart, payloadStart + size⟩
    else if tag < 192 then longHeader input start limit (tag - 183) false
    else if tag < 248 then .ok ⟨true, start + 1, start + 1 + (tag - 192)⟩
    else longHeader input start limit (tag - 247) true

def readHeader (input : Array UInt8) (start limit : Nat) : Except Error Header :=
  match headerShape input start limit with
  | .error e => .error e
  | .ok h => admitHeader input.size start limit h

private def view (input : Array UInt8) (start : Nat) (h : Header) : Item :=
  { isList := h.isList
    payload := input.extract h.payloadStart h.stop
    encoded := input.extract start h.stop }

/-- The stack carries siblings and nested payloads. Each recursive call consumes
one unit of explicit fuel; all calls are in tail position. On a valid encoding
each visited item owns a distinct prefix byte, so input.size + 1 suffices.
The latter completeness fact is tested here, not claimed as a theorem. -/
def validateSegments (input : Array UInt8) : Nat → List Segment → Except Error Unit
  | _, [] => .ok ()
  | 0, _ :: _ => .error .resourceLimit
  | fuel + 1, segment :: rest =>
    match readHeader input segment.start segment.stop with
    | .error e => .error e
    | .ok h =>
      let next := if h.stop < segment.stop then
          { segment with start := h.stop } :: rest
        else rest
      if h.isList then
        if segment.listDepth ≥ maxListDepth then .error .resourceLimit
        else if h.payloadStart < h.stop then
          validateSegments input fuel
            (⟨h.payloadStart, h.stop, segment.listDepth + 1⟩ :: next)
        else validateSegments input fuel next
      else validateSegments input fuel next

private def decodeBounded (input : Array UInt8) : Except Error Item :=
  match readHeader input 0 input.size with
  | .error e => .error e
  | .ok h =>
    if h.stop != input.size then .error (.malformed "trailing bytes")
    else
      match validateSegments input (input.size + 1) [⟨0, input.size, 0⟩] with
      | .error e => .error e
      | .ok () =>
        .ok { isList := h.isList
              payload := input.extract h.payloadStart h.stop
              encoded := input }

/-- Decode one whole RLP item, including validation of nested list encodings. -/
def decode (input : Array UInt8) : Except Error Item :=
  if input.size > maxInputBytes then .error .resourceLimit
  else decodeBounded input

private def childrenLoop (input : Array UInt8) :
    Nat → Nat → Array Item → Except Error (Array Item)
  | 0, pos, result =>
    if pos == input.size then .ok result else .error .resourceLimit
  | fuel + 1, pos, result =>
    if pos == input.size then .ok result
    else
      match readHeader input pos input.size with
      | .error e => .error e
      | .ok h => childrenLoop input fuel h.stop (result.push (view input pos h))

/-- Return immediate list members, each retaining its exact original encoding.
The payload is independently validated, so constructing an `Item` record outside
`decode` does not bypass canonicality checks on the returned children. -/
def children (item : Item) : Except Error (Array Item) :=
  if item.payload.size > maxInputBytes then .error .resourceLimit
  else if !item.isList then .error (.malformed "expected list")
  else if item.payload.isEmpty then .ok #[]
  else
    match validateSegments item.payload (item.payload.size + 1)
        [⟨0, item.payload.size, 1⟩] with
    | .error e => .error e
    | .ok () => childrenLoop item.payload (item.payload.size + 1) 0 #[]

/-- Interpret a byte-string payload as a minimal big-endian unsigned integer.
The empty byte string is zero; every nonempty integer starts with a nonzero byte.
The enclosing RLP encoding is checked separately by `decode`. -/
def scalar (item : Item) (maxBytes : Nat) : Except Error Nat :=
  if item.payload.size > maxInputBytes then .error .resourceLimit
  else if item.isList then .error (.malformed "expected integer bytes")
  else if item.payload.size > maxBytes then .error (.malformed "integer width")
  else if item.payload.size ≠ 0 ∧ byte item.payload 0 = 0 then
    .error (.malformed "nonminimal integer")
  else .ok (item.payload.foldl (fun value b => value * 256 + b.toNat) 0)

/-- Kind: resource admission.
Says: an input over the byte limit refuses before decoding or extracting arrays.
Does not say: the input is invalid Ethereum data or bound process memory. -/
theorem decode_over_limit (input : Array UInt8) (h : input.size > maxInputBytes) :
    decode input = .error .resourceLimit := by
  simp only [decode, if_pos h]

/-- Kind: bounds.
Says: an admitted header advances and both byte slices lie inside its range.
Does not say: the range is an Ethereum trie node or prove grammar refinement. -/
theorem admitHeader_bounds (inputSize start limit : Nat) (candidate h : Header)
    (ok : admitHeader inputSize start limit candidate = .ok h) :
    start < h.stop ∧ start ≤ h.payloadStart ∧ h.payloadStart ≤ h.stop ∧
      h.stop ≤ limit ∧ limit ≤ inputSize := by
  unfold admitHeader at ok
  split at ok
  next bounds => cases ok; exact bounds
  next _ => cases ok

/-- Kind: decoder bounds.
Says: the actual header parser returns only nonempty, in-range byte extents.
Does not say: all canonical encodings are admitted under the resource policy. -/
theorem readHeader_bounds (input : Array UInt8) (start limit : Nat) (h : Header)
    (ok : readHeader input start limit = .ok h) :
    start < h.stop ∧ start ≤ h.payloadStart ∧ h.payloadStart ≤ h.stop ∧
      h.stop ≤ limit ∧ limit ≤ input.size := by
  unfold readHeader at ok
  cases parsed : headerShape input start limit with
  | error e => simp only [parsed] at ok; cases ok
  | ok candidate =>
    simp only [parsed] at ok
    exact admitHeader_bounds input.size start limit candidate h ok

/-- Kind: resource boundary.
Says: exhausted validation fuel with pending input returns a resource refusal.
Does not say: an arbitrary supplied fuel is sufficient or prove a physical stack bound. -/
theorem validateSegments_zero (input : Array UInt8) (head : Segment) (rest : List Segment) :
    validateSegments input 0 (head :: rest) = .error .resourceLimit := by
  rfl

/-- Kind: resource admission.
Says: every successful public decode had at most the configured input bytes.
Does not say: the limit is a protocol maximum or a measured allocation bound. -/
theorem decode_input_bound (input : Array UInt8) (item : Item)
    (ok : decode input = .ok item) : input.size ≤ maxInputBytes := by
  by_cases over : input.size > maxInputBytes
  · rw [decode_over_limit input over] at ok
    cases ok
  · omega

/-- Kind: whole-input consumption and source linkage.
Says: a successful decode used a header ending at the actual input end, returned
that header's exact source view, and completed recursive segment validation.
Does not say: the validation algorithm refines an independent RLP grammar or
that these bytes authenticate any root. -/
theorem decode_source (input : Array UInt8) (item : Item)
    (ok : decode input = .ok item) :
    ∃ h : Header, readHeader input 0 input.size = .ok h ∧
      h.stop = input.size ∧ item.isList = h.isList ∧
      item.payload = input.extract h.payloadStart h.stop ∧
      item.encoded = input ∧
      validateSegments input (input.size + 1) [⟨0, input.size, 0⟩] = .ok () := by
  unfold decode at ok
  split at ok
  next _ => cases ok
  next _ =>
    unfold decodeBounded at ok
    cases parsed : readHeader input 0 input.size with
    | error e => simp only [parsed] at ok; cases ok
    | ok h =>
      simp only [parsed] at ok
      split at ok
      next _ => cases ok
      next consumed =>
        cases validated : validateSegments input (input.size + 1) [⟨0, input.size, 0⟩] with
        | error e => simp only [validated] at ok; cases ok
        | ok value =>
          cases value
          simp only [validated] at ok
          cases ok
          exact ⟨h, rfl, by simpa using consumed, rfl, rfl, rfl, rfl⟩

/-- Kind: source linkage.
Says: successful whole-input decoding retains the exact bytes supplied for hashing.
Does not say: those bytes authenticate any root or represent a complete trie. -/
theorem decode_keeps_encoded (input : Array UInt8) (item : Item)
    (ok : decode input = .ok item) : item.encoded = input := by
  unfold decode at ok
  split at ok
  next _ => cases ok
  next _ =>
    unfold decodeBounded at ok
    cases parsed : readHeader input 0 input.size with
    | error e => simp only [parsed] at ok; cases ok
    | ok h =>
      simp only [parsed] at ok
      split at ok
      next _ => cases ok
      next _ =>
        cases validated : validateSegments input (input.size + 1) [⟨0, input.size, 0⟩] with
        | error e => simp only [validated] at ok; cases ok
        | ok value =>
          cases value
          simp only [validated] at ok
          cases ok
          rfl

/-- Kind: integer admission.
Says: a successful integer result is a width-bounded byte string with no leading
zero, and equals the actual big-endian fold of that payload.
Does not say: its RLP envelope was validated or the integer is an account balance. -/
theorem scalar_success (item : Item) (maxBytes value : Nat)
    (ok : scalar item maxBytes = .ok value) :
    item.isList = false ∧ item.payload.size ≤ maxInputBytes ∧
      item.payload.size ≤ maxBytes ∧
      (item.payload.size = 0 ∨ byte item.payload 0 ≠ 0) ∧
      value = item.payload.foldl (fun n b => n * 256 + b.toNat) 0 := by
  unfold scalar at ok
  split at ok
  next _ => cases ok
  next bounded =>
    cases list : item.isList with
    | true => simp only [list, ↓reduceIte] at ok; cases ok
    | false =>
      simp only [list, Bool.false_eq_true, ↓reduceIte] at ok
      split at ok
      next _ => cases ok
      next width =>
        split at ok
        next _ => cases ok
        next minimal =>
          cases ok
          refine ⟨rfl, by omega, by omega, ?_, rfl⟩
          by_cases empty : item.payload.size = 0
          · exact Or.inl empty
          · exact Or.inr (fun zero => minimal ⟨empty, zero⟩)

#print axioms decode_over_limit
#print axioms admitHeader_bounds
#print axioms readHeader_bounds
#print axioms validateSegments_zero
#print axioms decode_input_bound
#print axioms decode_source
#print axioms decode_keeps_encoded
#print axioms scalar_success

end EVMCleanroom.CanonicalRLP
