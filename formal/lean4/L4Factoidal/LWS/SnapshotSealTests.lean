/-
L4Factoidal.LWS.SnapshotSealTests — build-time checks of the sealed snapshot
envelope (`L4Factoidal.LWS.SnapshotSeal`,
https://github.com/danbri/factoidal/issues/921), positive and negative.

A `#guard` runs in the Lean interpreter, which cannot call the HACL* extern,
so these checks seal and open through `checkingModel`, the model of the AEAD
interface that hides nothing and refuses any changed or removed byte. They
check the envelope: the key text, the key id, the header checks, the
canonical base64 rule, the configuration cases and the round trip. The same
cases with the real ChaCha20-Poly1305 run at run time:
`lake exe l4crypto-probe` (section `lws-snapshot-seal`) and
`node tests/lws/encryption.mjs`.

The key and nonce are those of RFC 8439 §2.8.2. The expected key ids were
computed outside Lean with Python's `hashlib.sha256`, so they also check the
pure Lean SHA-256 that `keyIdOf` uses.
-/
import L4Factoidal.LWS.SnapshotSeal

namespace L4Factoidal.LWS.SealTests

open L4Factoidal.JSON
open L4Factoidal.LWS.Seal

/-- RFC 8439 §2.8.2 key, as the 64 hex digits a user would write. -/
def hexKey : String := "808182838485868788898a8b8c8d8e8f909192939495969798999a9b9c9d9e9f"

/-- The same 32 bytes in base64url (RFC 4648 §5), unpadded. -/
def b64Key : String := "gIGCg4SFhoeIiYqLjI2Oj5CRkpOUlZaXmJmam5ydnp8"

def keyBytesExpected : List UInt8 := (List.range 32).map (fun i => UInt8.ofNat (0x80 + i))

def keyOf (s : String) : ByteArray := match parseStorageKey s with
  | .ok b => b
  | .error _ => ByteArray.empty

def key : ByteArray := keyOf hexKey

/-- Another key: 32 zero bytes. -/
def otherKey : ByteArray := ⟨Array.replicate 32 0⟩

/-- RFC 8439 §2.8.2 nonce. -/
def nonce : ByteArray := ⟨#[0x07, 0, 0, 0, 0x40, 0x41, 0x42, 0x43, 0x44, 0x45, 0x46, 0x47]⟩

def otherNonce : ByteArray := ⟨Array.replicate 12 1⟩

/-- A clear-text snapshot document of format 2, as `snapshotJson` writes. -/
def clearDoc : Json :=
  .object [ ("format", .string "lws-snapshot-2"), ("clock", .number "3")
          , ("entries", .array [.object [ ("path", .string "/"), ("kind", .string "storageRoot")
                                        , ("contentType", .string "text/turtle")
                                        , ("bodyBase64", .string ""), ("mtime", .number "1") ]]) ]

def plain : ByteArray := (Json.toString clearDoc).toUTF8

def sealed : Json := (sealDoc checkingModel key nonce plain).getD .null

def isErr {α} (e : Except String α) : Bool := match e with
  | .error _ => true
  | .ok _ => false

def errHas {α} (e : Except String α) (needle : String) : Bool := match e with
  | .error m => (m.splitOn needle).length > 1
  | .ok _ => false

/-- Replace one member of an object. -/
def setMember (j : Json) (k : String) (v : Json) : Json := match j with
  | .object fs => .object (fs.map (fun (n, x) => if n == k then (n, v) else (n, x)))
  | other => other

def str (j : Json) (k : String) : String := (j.getString? k).getD ""

/-- The text with the character at `i` replaced by another base64 symbol. -/
def changeAt (t : String) (i : Nat) : String :=
  String.ofList (t.toList.mapIdx (fun j c => if j == i then (if c == 'A' then 'B' else 'A') else c))

/-! ## The storage key -/

#guard key.data.toList == keyBytesExpected
#guard (keyOf b64Key).data.toList == keyBytesExpected
#guard (keyOf (b64Key ++ "=")).data.toList == keyBytesExpected
#guard (keyOf hexKey.toUpper).data.toList == keyBytesExpected
#guard (keyOf ("  " ++ hexKey ++ "\n")).data.toList == keyBytesExpected
-- Refused: other lengths, non-hex at 64 characters, the standard alphabet,
-- an empty value. The message never repeats the value.
#guard isErr (parseStorageKey (hexKey.drop 2).toString)
#guard isErr (parseStorageKey (hexKey ++ "00"))
#guard isErr (parseStorageKey ((hexKey.drop 1).toString ++ "g"))
#guard isErr (parseStorageKey "gIGCg4SFhoeIiYqLjI2Oj5CRkpOUlZaXmJmam5ydng")   -- 31 bytes
#guard isErr (parseStorageKey "gIGCg4SFhoeIiYqLjI2Oj5CRkpOUlZaXmJmam5ydnp-g") -- 33 bytes
#guard isErr (parseStorageKey "gIGCg4SFhoeIiYqLjI2Oj5CRkpOUlZaXmJmam5ydnp+")
#guard isErr (parseStorageKey "")
#guard errHas (parseStorageKey (hexKey ++ "00")) "32 bytes"
#guard !(errHas (parseStorageKey (hexKey ++ "00")) hexKey)

/-! ## Key id: first 8 bytes of SHA-256, cross-checked with Python hashlib -/

#guard keyIdOf key == "82d86408530b765e"
#guard keyIdOf otherKey == "66687aadf862bd77"

/-! ## Seal: header members and lengths -/

#guard str sealed "format" == "lws-snapshot-sealed-1"
#guard str sealed "cipher" == "chacha20-poly1305"
#guard str sealed "keyId" == "82d86408530b765e"
#guard str sealed "nonce" == "BwAAAEBBQkNERUZH"
#guard isSealed sealed
#guard !(isSealed clearDoc)
#guard (sealDoc checkingModel (key.extract 0 31) nonce plain).isNone
#guard (sealDoc checkingModel key (nonce.extract 0 8) plain).isNone
#guard isErr (sealSnapshot checkingModel (some key) none clearDoc)
#guard isErr (sealSnapshot checkingModel (some key) (some (nonce.extract 0 11)) clearDoc)
-- No key: the document is written as it is.
#guard (sealSnapshot checkingModel none none clearDoc).toOption.map Json.toString
        == some (Json.toString clearDoc)

/-! ## Open: the round trip -/

#guard (unsealDoc checkingModel key sealed).toOption.map (·.data.toList) == some plain.data.toList
#guard ((sealSnapshot checkingModel (some key) (some nonce) clearDoc).toOption.bind
         (fun d => (openSnapshot checkingModel (some key) (some d)).toOption)).map
         (·.map Json.toString) == some (some (Json.toString clearDoc))

/-! ## Open: refusals -/

-- Wrong key, by key id.
#guard errHas (unsealDoc checkingModel otherKey sealed) "wrong key"
-- Each header member changed.
#guard isErr (unsealDoc checkingModel key (setMember sealed "format" (.string "lws-snapshot-2")))
#guard errHas (unsealDoc checkingModel key (setMember sealed "cipher" (.string "aes-256-gcm"))) "cipher"
#guard errHas (unsealDoc checkingModel key (setMember sealed "keyId" (.string "0000000000000000"))) "wrong key"
#guard errHas (unsealDoc checkingModel key
         (setMember sealed "nonce" (.string (Base64.encode otherNonce)))) "authentication failed"
-- A member missing or of the wrong type.
#guard isErr (unsealDoc checkingModel key (setMember sealed "nonce" (.number "1")))
#guard isErr (unsealDoc checkingModel key (setMember sealed "ciphertext" .null))
-- Base64 that is not canonical: "BwAAAEBBQkNERUZH" with a changed pad-free
-- final symbol is another 12 bytes, so it reaches the AEAD; a text with a
-- symbol outside the alphabet does not decode.
#guard errHas (unsealDoc checkingModel key (setMember sealed "nonce" (.string "BwAAAEBBQkNERUZ*"))) "canonical"
#guard errHas (unsealDoc checkingModel key
         (setMember sealed "ciphertext" (.string (str sealed "ciphertext" ++ "====")))) "canonical"
-- The ciphertext truncated by one base64 group (still valid base64).
#guard errHas (unsealDoc checkingModel key
         (setMember sealed "ciphertext"
           (.string (String.ofList ((str sealed "ciphertext").toList.take
              ((str sealed "ciphertext").length - 4)))))) "authentication failed"
-- Every one-character change of the ciphertext text is refused.
#guard let t := str sealed "ciphertext"
       (List.range t.length).all (fun i =>
         isErr (unsealDoc checkingModel key (setMember sealed "ciphertext" (.string (changeAt t i)))))
-- Every one-character change of the nonce text is refused.
#guard let t := str sealed "nonce"
       (List.range t.length).all (fun i =>
         isErr (unsealDoc checkingModel key (setMember sealed "nonce" (.string (changeAt t i)))))

/-! ## Open: the configuration cases -/

-- No key, clear text: unchanged.
#guard (openSnapshot checkingModel none (some clearDoc)).toOption.map (·.map Json.toString)
        == some (some (Json.toString clearDoc))
-- No snapshot: a new storage, with or without a key.
#guard (openSnapshot checkingModel none none).toOption.map Option.isNone == some true
#guard (openSnapshot checkingModel (some key) none).toOption.map Option.isNone == some true
-- A key and a clear-text file: refused.
#guard errHas (openSnapshot checkingModel (some key) (some clearDoc)) "clear text"
-- A sealed file and no key: refused, naming the key id.
#guard errHas (openSnapshot checkingModel none (some sealed)) "82d86408530b765e"
-- A sealed file whose plaintext is not JSON.
#guard errHas (openSnapshot checkingModel (some key)
         (some ((sealDoc checkingModel key nonce "not json".toUTF8).getD .null))) "not JSON"

end L4Factoidal.LWS.SealTests
