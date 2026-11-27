import EthereumWallet.Abi.Signature

/-!
# Event topics and log data

`topic0` of a non-anonymous event is the Keccak-256 hash of its canonical
signature. An indexed parameter of an elementary type (`uint<M>`, `int<M>`,
`address`, `bool`, `bytes<M>`) is its ABI word in a topic. An indexed parameter
of any other type (`bytes`, `string`, arrays, tuples) is only a hash in the
topic and cannot be decoded: it is returned as `EventArg.hashed`. Parameters
that are not indexed are the strictly decoded argument list of the log data.

A log has at most four topics; a declaration that needs more is refused.
-/

namespace EthereumWallet.Abi

structure EventParam where
  name : String
  type : AbiType
  indexed : Bool

structure EventSig where
  name : String
  params : List EventParam
  anonymous : Bool := false

def EventSig.canonical (e : EventSig) : String :=
  e.name ++ "(" ++ canonicalL (e.params.map (·.type)) ++ ")"

def EventSig.topic0 (e : EventSig) : List UInt8 := keccak256 (utf8 e.canonical)

/-- Kind: definition check. Says: `topic0` is the Keccak-256 hash of the canonical signature.
    Does not say: that `keccak256` is Keccak-256 (tested against published topics). -/
theorem topic0_eq (e : EventSig) :
    e.topic0
      = keccak256 (utf8 (e.name ++ "(" ++ canonicalL (e.params.map (·.type)) ++ ")")) := rfl

inductive EventArg where
  | value (v : AbiValue)
  /-- An indexed value of a non-elementary type: only its hash is in the log. -/
  | hashed (h : List UInt8)

def isElementary : AbiType → Bool
  | .uint _ => true
  | .int _ => true
  | .address => true
  | .bool => true
  | .fixedBytes _ => true
  | _ => false

/-- Walk the parameters in order, taking indexed ones from the topics and the rest from the
    decoded data. Both lists must be used up exactly. -/
def mergeEvent : List EventParam → List (List UInt8) → List AbiValue →
    List (String × EventArg) → Except Err (List (String × EventArg))
  | [], [], [], acc => .ok acc.reverse
  | [], _, _, _ => .error .badTopics
  | p :: ps, topics, vals, acc =>
    if p.indexed then
      match topics with
      | [] => .error .badTopics
      | t :: topics' =>
        if t.length != 32 then .error .badTopics
        else if isElementary p.type then
          match decodeArgsAt [p.type] (toBytes t) 0 with
          | .ok [v] => mergeEvent ps topics' vals ((p.name, .value v) :: acc)
          | .ok _ => .error .badTopics
          | .error e => .error e
        else mergeEvent ps topics' vals ((p.name, .hashed t) :: acc)
    else
      match vals with
      | [] => .error .badTopics
      | v :: vals' => mergeEvent ps topics vals' ((p.name, .value v) :: acc)

/-- Strict decoding of one log against a known event declaration. -/
def decodeEvent (e : EventSig) (topics : List (List UInt8)) (data : ByteArray) :
    Except Err (List (String × EventArg)) :=
  if topics.length > 4 then .error .badTopics
  else
    let indexedTopics : Except Err (List (List UInt8)) :=
      if e.anonymous then .ok topics
      else
        match topics with
        | t0 :: rest => if t0 == e.topic0 then .ok rest else .error .unknownSelector
        | [] => .error .badTopics
    match indexedTopics with
    | .error err => .error err
    | .ok its =>
      match decodeArgsAt ((e.params.filter (!·.indexed)).map (·.type)) data 0 with
      | .error err => .error err
      | .ok vals => mergeEvent e.params its vals []

/-- Kind: refusal at the bound. Says: a log with more than four topics is refused.
    Does not say: anything about logs with four or fewer. -/
theorem decodeEvent_too_many_topics (e : EventSig) (topics : List (List UInt8)) (data : ByteArray)
    (h : 4 < topics.length) : decodeEvent e topics data = .error .badTopics := by
  simp [decodeEvent, h]

end EthereumWallet.Abi
