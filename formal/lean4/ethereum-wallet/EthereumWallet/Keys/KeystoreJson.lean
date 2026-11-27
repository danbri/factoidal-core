import EthereumWallet.Keys.Json
import EthereumWallet.Keys.Keystore

/-
Keystore version 3 as JSON text: reading with the package's own JSON reader
(`Json.lean`) and writing. Member names are matched without regard to ASCII
case, as geth does ("crypto" or "Crypto"). Hex strings have no `0x` prefix.
The reader checks shape only; `decrypt` refuses unsupported versions, ciphers,
KDFs and parameters. Tested in `KeystoreTests`; nothing here is proved.
-/

namespace EthereumWallet.Keys

private def jsonNeed {α : Type} (what : String) : Option α → Except KeystoreError α
  | some a => .ok a
  | none => .error (.json what)

private def jsonMember (j : Json) (name : String) : Except KeystoreError Json :=
  jsonNeed ("missing " ++ name) (j.field? name)

private def jsonStrField (j : Json) (name : String) : Except KeystoreError String := do
  let v ← jsonMember j name
  jsonNeed (name ++ " is not a string") v.str?

private def jsonNatField (j : Json) (name : String) : Except KeystoreError Nat := do
  let v ← jsonMember j name
  jsonNeed (name ++ " is not a non-negative integer") v.nat?

private def jsonHexField (j : Json) (name : String) : Except KeystoreError ByteArray := do
  let s ← jsonStrField j name
  jsonNeed (name ++ " is not hex") (ofHex? s)

/-- Largest number of members accepted in one object of a keystore. -/
def keystoreMaxMembers : Nat := 64

/-- An object of at most `keystoreMaxMembers` members whose names differ even when case is
    ignored; with `exactLower`, every name must also be lower case. Readers disagree on
    which of two members with one name wins (first here, last in Go's decoder), so a
    keystore with a repeated name is refused, not interpreted. -/
def jsonMembersOk (j : Json) (exactLower : Bool) : Bool :=
  match j with
  | .obj members =>
    members.length ≤ keystoreMaxMembers &&
      (members.map (·.1.toLower)).eraseDups.length == members.length &&
      (!exactLower || members.all fun kv => kv.1 == kv.1.toLower)
  | _ => false

/-- An object member that passes `jsonMembersOk`. -/
def jsonCheckedMember (j : Json) (name : String) (exactLower : Bool) :
    Except KeystoreError Json := do
  let m ← jsonMember j name
  if jsonMembersOk m exactLower then pure m
  else .error (.json (name ++ ": repeated, too many or wrongly cased member names"))

/-- A keystore from a parsed JSON value. Top-level and `crypto` names are matched
    without regard to case (geth reads them into a struct); `kdfparams` names must be
    lower case exactly (geth reads them into a map). Repeated names are refused. -/
def Keystore.ofJson (j : Json) : Except KeystoreError Keystore := do
  if !jsonMembersOk j false then
    throw (.json "keystore: not an object, or repeated or too many member names")
  let version ← jsonNatField j "version"
  let crypto ← jsonCheckedMember j "crypto" false
  let cipher ← jsonStrField crypto "cipher"
  let ciphertext ← jsonHexField crypto "ciphertext"
  let cipherparams ← jsonCheckedMember crypto "cipherparams" false
  let iv ← jsonHexField cipherparams "iv"
  let mac ← jsonHexField crypto "mac"
  let kdfName ← jsonStrField crypto "kdf"
  let kdf ←
    if kdfName == "scrypt" then do
      let kp ← jsonCheckedMember crypto "kdfparams" true
      let n ← jsonNatField kp "n"
      let r ← jsonNatField kp "r"
      let p ← jsonNatField kp "p"
      let dkLen ← jsonNatField kp "dklen"
      let salt ← jsonHexField kp "salt"
      pure (Kdf.scrypt n r p dkLen salt)
    else if kdfName == "pbkdf2" then do
      let kp ← jsonCheckedMember crypto "kdfparams" true
      let c ← jsonNatField kp "c"
      let dkLen ← jsonNatField kp "dklen"
      let prf ← jsonStrField kp "prf"
      let salt ← jsonHexField kp "salt"
      pure (Kdf.pbkdf2 c dkLen prf salt)
    else pure (Kdf.other kdfName)
  pure { version := version, cipher := cipher, iv := iv, ciphertext := ciphertext, kdf := kdf,
         mac := mac, address := (j.field? "address").bind Json.str?,
         id := (j.field? "id").bind Json.str? }

/-- A keystore from JSON text. Reader errors come back as `.json`. -/
def Keystore.ofJson? (text : String) : Except KeystoreError Keystore :=
  match Json.parse text with
  | .error e => .error (.json ("not JSON we read: " ++ reprStr e))
  | .ok j => Keystore.ofJson j

private def kdfJson : Kdf → String
  | .scrypt n r p dkLen salt =>
    "\"kdf\":\"scrypt\",\"kdfparams\":{\"dklen\":" ++ toString dkLen ++ ",\"n\":" ++ toString n ++
      ",\"p\":" ++ toString p ++ ",\"r\":" ++ toString r ++ ",\"salt\":\"" ++ toHex salt ++ "\"}"
  | .pbkdf2 c dkLen prf salt =>
    "\"kdf\":\"pbkdf2\",\"kdfparams\":{\"c\":" ++ toString c ++ ",\"dklen\":" ++ toString dkLen ++
      ",\"prf\":" ++ jsonQuote prf ++ ",\"salt\":\"" ++ toHex salt ++ "\"}"
  | .other name => "\"kdf\":" ++ jsonQuote name ++ ",\"kdfparams\":{}"

/-- JSON text for a keystore, in geth's member order. Holds no secret: the
    ciphertext, MAC, salt and IV are what a keystore file stores. -/
def Keystore.toJson (ks : Keystore) : String :=
  let address := match ks.address with
    | some a => "\"address\":" ++ jsonQuote a ++ ","
    | none => ""
  let id := match ks.id with
    | some i => "\"id\":" ++ jsonQuote i ++ ","
    | none => ""
  "{" ++ address ++ "\"crypto\":{\"cipher\":" ++ jsonQuote ks.cipher ++ ",\"ciphertext\":\"" ++
    toHex ks.ciphertext ++ "\",\"cipherparams\":{\"iv\":\"" ++ toHex ks.iv ++ "\"}," ++
    kdfJson ks.kdf ++ ",\"mac\":\"" ++ toHex ks.mac ++ "\"}," ++ id ++ "\"version\":" ++
    toString ks.version ++ "}"

end EthereumWallet.Keys
