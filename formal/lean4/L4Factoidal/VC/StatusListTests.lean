/-
L4Factoidal.VC.StatusListTests — build-time `#guard`s for
`VC/StatusList.lean` over the examples of Bitstring Status List v1.0 (W3C
Recommendation 2025-05-15; text of w3c/vc-bitstring-status-list at commit
7b93711e, 2026-10-21): the status list credential of §2.2 (its `encodedList`
is GZIP with dynamic Huffman blocks, so this also checks `Codec.gunzip` on a
file this tree did not write) and the entries of §2.1.
-/
import L4Factoidal.VC.StatusList
import L4Factoidal.JSON.Parser

namespace L4Factoidal.VC.StatusListTests

open L4Factoidal.JSON
open L4Factoidal.VC.StatusList

def j (s : String) : Json := (parseJson? s).getD .null

def setField (name : String) (v : Json) : Json → Json
  | .object fs => .object (fs.filter (·.1 != name) ++ [(name, v)])
  | _ => .object [(name, v)]

/-- §2.2, the example status list credential. -/
def specList : Json := j "{
  \"@context\": [\"https://www.w3.org/ns/credentials/v2\"],
  \"id\": \"https://example.com/credentials/status/3\",
  \"type\": [\"VerifiableCredential\", \"BitstringStatusListCredential\"],
  \"issuer\": \"did:example:12345\",
  \"validFrom\": \"2021-04-05T14:27:40Z\",
  \"credentialSubject\": {
    \"id\": \"https://example.com/status/3#list\",
    \"type\": \"BitstringStatusList\",
    \"statusPurpose\": \"revocation\",
    \"encodedList\": \"uH4sIAAAAAAAAA-3BMQEAAADCoPVPbQwfoAAAAAAAAAAAAAAAAAAAAIC3AYbSVKsAQAAA\"
  }}"

/-- §2.1, the first entry of the example credential. -/
def specEntry : Json := j "{
    \"id\": \"https://example.com/credentials/status/3#94567\",
    \"type\": \"BitstringStatusListEntry\",
    \"statusPurpose\": \"revocation\",
    \"statusListIndex\": \"94567\",
    \"statusListCredential\": \"https://example.com/credentials/status/3\"}"

-- the published list expands to 16KB of zeros
#guard (expand "uH4sIAAAAAAAAA-3BMQEAAADCoPVPbQwfoAAAAAAAAAAAAAAAAAAAAIC3AYbSVKsAQAAA").toOption.map
  (fun b => (b.size, b.data.all (· == 0))) == some (16384, true)

#guard (checkEntry specEntry).toOption.map (·.statusListIndex) == some 94567

-- §3.2 on the spec's list: status 0, valid
#guard ((checkEntry specEntry).toOption.map fun e => validate e specList) ==
  some (.ok { status := 0, purpose := "revocation", valid := true })

-- the purpose must match a purpose of the list
#guard ((checkEntry (setField "statusPurpose" (.string "suspension") specEntry)).toOption.map fun e =>
  match validate e specList with | .error (.verification _) => true | _ => false) == some true

-- RANGE_ERROR past the end of 131,072 entries
#guard ((checkEntry (setField "statusListIndex" (.string "131072") specEntry)).toOption.map fun e =>
  match validate e specList with | .error (.range _ _) => true | _ => false) == some true

-- STATUS_LIST_LENGTH_ERROR for a list shorter than 131,072 entries
def shortList : Json :=
  setField "credentialSubject"
    (setField "encodedList" (.string (compress (zeros 1024)))
      ((specList.field? "credentialSubject").getD .null)) specList
#guard ((checkEntry specEntry).toOption.map fun e =>
  match validate e shortList with | .error (.listLength _ _) => true | _ => false) == some true

-- a revoked entry: generate a list with index 94567 set, then validate it
def revokedList : Json :=
  setField "credentialSubject"
    (setField "encodedList" (.string (generate 1 0 [(94567, 1)]))
      ((specList.field? "credentialSubject").getD .null)) specList
#guard ((checkEntry specEntry).toOption.map fun e => validate e revokedList) ==
  some (.ok { status := 1, purpose := "revocation", valid := false })
-- its neighbour is still valid
#guard ((checkEntry (setField "statusListIndex" (.string "94566") specEntry)).toOption.map fun e =>
  (validate e revokedList).toOption.map (·.valid)) == some (some true)

-- MALFORMED_VALUE_ERROR (the shape the W3C suite's Algorithm test posts)
#guard (match checkEntry (j "{\"type\": \"BitstringStatusListEntry\", \"statusPurpose\": \"revocation\",
    \"statusListIndex\": true, \"statusListCredential\": \"https://example.com\"}") with
  | .error (.malformed _) => true | _ => false)
#guard (match checkEntry (setField "type" (.string "StatusList2021Entry") specEntry) with
  | .error (.malformed _) => true | _ => false)
#guard (match checkEntry (setField "id" (.string "https://example.com/credentials/status/3") specEntry) with
  | .error (.malformed _) => true | _ => false)
-- statusSize 2 needs 4 messages
#guard (match checkEntry (setField "statusSize" (.number "2") specEntry) with
  | .error (.malformed _) => true | _ => false)

/-- §2.1, a message entry with statusSize 2 (the spec's example lists three of
its four messages and an ellipsis; the fourth is added here). -/
def msgEntry : Json := j "{
    \"type\": \"BitstringStatusListEntry\", \"statusPurpose\": \"message\",
    \"statusListIndex\": \"3\", \"statusSize\": 2,
    \"statusListCredential\": \"https://example.com/credentials/status/8\",
    \"statusMessage\": [{\"status\":\"0x0\", \"message\":\"pending_review\"},
      {\"status\":\"0x1\", \"message\":\"accepted\"}, {\"status\":\"0x2\", \"message\":\"rejected\"},
      {\"status\":\"0x3\", \"message\":\"undefined\"}]}"

def msgList : Json :=
  setField "credentialSubject"
    (setField "statusPurpose" (.string "message")
      (setField "encodedList" (.string (generate 2 0 [(3, 2)]))
        ((specList.field? "credentialSubject").getD .null))) specList

#guard ((checkEntry msgEntry).toOption.map fun e => validate e msgList) ==
  some (.ok { status := 2, purpose := "message", valid := false, message := some "rejected" })

end L4Factoidal.VC.StatusListTests
