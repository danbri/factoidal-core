/-
L4Factoidal.XMPP.HttpOverXmppTests — end-to-end `#guard`s for HTTP over XMPP
(XEP-0332) against `webdav-serve`'s handler.
https://github.com/danbri/factoidal/issues/1107

Each request is an XEP-0332 `iq` stanza text. `HttpOverXmpp.step` reads it,
decides access, runs `WebDAV.handle` as a program over storage operations, and
the program runs against the reference LWS server over a model storage
(`LWS.step MemStore`, the `lwsRun` loopback of `WebDAV.Tests`). The answer
stanzas are read back with the client-side codec.

No network: stage 2 adds the outgoing XMPP client stream and the local proxy.
-/
import L4Factoidal.XMPP.HttpOverXmpp
import L4Factoidal.WebDAV.Tests

namespace L4Factoidal.XMPP.HttpOverXmppTests

open L4Factoidal.XMPP.HttpOverXmpp
open L4Factoidal.WebDAV (DavState Ctx)
open L4Factoidal.WebDAV.Tests (lwsRun emptyStorage mounts)
open L4Factoidal.LWS (MemState)

def cfg : Config := { allow := ["alice@example.org"], inlineLimit := 4096, chunkSize := 256 }

/-- 5,000 bytes: above the inline limit of `cfg`. -/
def big : ByteArray := ByteArray.mk ((List.range 5000).map (fun i => UInt8.ofNat (i * 7 % 256))).toArray
def cx : Ctx := { mounts, now := 2000000000, random := ByteArray.mk (Array.replicate 16 7) }

structure W where
  dav : DavState := {}
  st : State := {}
  store : MemState := emptyStorage
  out : List String := []
  handled : Bool := true

def feed (w : W) (stanza : String) : W :=
  match (step cfg cx w.dav w.st stanza).runPure lwsRun 100000 w.store with
  | some (o, store) => { dav := o.dav, st := o.st, store, out := o.out, handled := o.handled }
  | none => { w with out := [], handled := false }

def run (stanzas : List String) : W := stanzas.foldl feed {}

def iq (from_ id method resource : String) (headers : List (String × String) := []) (body : Body := .empty)
    (mcs : Option Nat := none) : String :=
  renderReqIq { from_ := some from_, to := some "dav@example.net/box", id }
    { method, resource, headers := ("Host", "localhost:8090") :: headers, body, maxChunkSize := mcs }

def alice : String := "alice@example.org/laptop"

def resp? (w : W) : Option Resp := w.out.head?.bind (fun s => (parseRespIq s).map (·.2))
def status (w : W) : Nat := ((resp? w).map (·.statusCode)).getD 0
def has (s sub : String) : Bool := (s.splitOn sub).length > 1

-- A PROPFIND carried as XEP-0332 gives a 207 `resp` with the multistatus as `xml`.
#guard
  let w := run [iq alice "p1" "PROPFIND" "/m/" [("Depth", "1")]]
  match resp? w with
  | some r => r.statusCode == 207 && r.statusMessage == some "Multi-Status" &&
      (match r.body with | .xml f => has f "multistatus" && has f "<D:href>/m/</D:href>" | _ => false)
  | none => false

-- The answer goes back to the requester, from the address it was sent to.
#guard
  let w := run [iq alice "p1" "PROPFIND" "/m/" [("Depth", "0")]]
  match w.out.head?.bind parseRespIq with
  | some (e, _) => e.to == some alice && e.from_ == some "dav@example.net/box" && e.id == "p1"
  | none => false

-- PUT as text, then GET: 201, then 200 with the text body.
#guard
  let w0 := run [iq alice "a" "PUT" "/m/a.txt" [("Content-Type", "text/plain")] (.text "hello")]
  let w1 := feed w0 (iq alice "b" "GET" "/m/a.txt")
  status w0 == 201 && status w1 == 200 && ((resp? w1).map (·.body)) == some (.text "hello")

-- PUT as base64 (binary), GET answers base64 with the same bytes.
#guard
  let w0 := run [iq alice "a" "PUT" "/m/b.bin" [("Content-Type", "application/octet-stream")] (.base64 binBytes)]
  let w1 := feed w0 (iq alice "b" "GET" "/m/b.bin")
  status w0 == 201 && ((resp? w1).map (·.body)) == some (.base64 binBytes)

-- A body above the inline limit goes back as chunkedBase64, in chunks of at
-- most maxChunkSize bytes, which reassemble to the stored bytes.
#guard
  let w0 := run [iq alice "a" "PUT" "/m/big.bin" [("Content-Type", "application/octet-stream")] (.base64 big)]
  let w1 := feed w0 (iq alice "b" "GET" "/m/big.bin" (mcs := some 300))
  let chunks := (w1.out.drop 1).filterMap parseChunk |>.map (·.2)
  status w1 == 200 && chunks.length == 20 && chunks.all (·.data.size ≤ 256) &&
  (match (resp? w1).map (·.body) with | some (Body.chunked sid) => chunks.all (·.streamId == sid) | _ => false) &&
  (assembleChunks chunks).map (·.toList) == some big.toList

-- A chunked request body: nothing is served until the last chunk; chunks may
-- arrive out of order.
#guard
  let cs := splitChunks "up1" big 256
  let msgs := renderChunkMessages (some alice) (some "dav@example.net/box") cs
  let w0 := run [iq alice "u" "PUT" "/m/up.bin" [("Content-Type", "application/octet-stream")] (.chunked "up1")]
  let w1 := feed w0 (msgs.getLastD "")
  let w2 := (msgs.dropLast.reverse).foldl feed w1
  let w3 := feed w2 (iq alice "g" "GET" "/m/up.bin" (mcs := some 256))
  cs.length == 20 && w0.out.isEmpty && w1.out.isEmpty && status w2 == 201 &&
  (assembleChunks ((w3.out.drop 1).filterMap parseChunk |>.map (·.2))).map (·.toList) == some big.toList

-- A `close` from the requester drops a waiting request.
#guard
  let w0 := run [iq alice "u" "PUT" "/m/up.bin" [] (.chunked "up2")]
  let w1 := feed w0 (renderClose (some alice) (some "dav@example.net/box") "up2")
  w0.st.pending.length == 1 && w1.st.pending.isEmpty

-- A JID not in the allow list is refused with `forbidden`, and nothing runs.
#guard
  let w := run [iq "mallory@example.org/x" "m1" "PUT" "/m/a.txt" [] (.text "x")]
  w.out.length == 1 && has (w.out.getD 0 "") "type=\"error\"" && has (w.out.getD 0 "") "<forbidden" &&
  w.store.entries.length == emptyStorage.entries.length

-- CONNECT is refused with `not-allowed`.
#guard
  let w := run [iq alice "c1" "CONNECT" "example.org:443"]
  has (w.out.getD 0 "") "type=\"error\"" && has (w.out.getD 0 "") "<not-allowed"

-- Other stanzas are not handled here; the host passes them on.
#guard !(run ["<message from='alice@example.org/l'><body>hi</body></message>"]).handled
#guard !(run ["<iq type='get' id='v'><query xmlns='jabber:iq:version'/></iq>"]).handled

end L4Factoidal.XMPP.HttpOverXmppTests
