/- Native IO regression for the shared session adapter; this is not a Wasm or
TCP test. Run from formal/lean4: lake env lean ../../tests/xmpp/session-buffer.lean
The incomplete suffix contains a multibyte character and follows a complete
unit that sends a reply: output presence cannot identify the residual buffer. -/
import Wasm.Ops.XmppSession

open L4Wasm.Ops L4Factoidal.JSON

private def document (text : String) : IO Json := do
  let some doc := parseJson? text | throw (IO.userError s!"invalid JSON: {text}")
  unless doc.field? "ok" == some (.bool true) do
    throw (IO.userError s!"operation failed: {text}")
  return doc

private def handle (doc : Json) : IO String := do
  let some h := doc.getString? "handle" | throw (IO.userError "missing handle")
  return h

private def checkBytes (doc : Json) (expected : Nat) : IO Unit := do
  unless doc.field? "bufferedBytes" == some (.number (toString expected)) do
    throw (IO.userError s!"wrong residual byte count; expected {expected}")

private def run : IO Unit := do
  let server ← handle (← document (← xmppOpen "{}"))
  try
    let session ← handle (← document (← xmppSessionOpen server
      "{\"streamId\":\"buffer-test\",\"nonce\":\"nonce-test\"}"))
    let suffix := "<auth a='é"
    let header := "<stream:stream to='localhost' xmlns='jabber:client' xmlns:stream='http://etherx.jabber.org/streams' version='1.0'>"
    let first ← document (← xmppSessionFeed session (header ++ suffix))
    let some send := first.getArray? "send" | throw (IO.userError "missing send")
    unless !send.isEmpty do throw (IO.userError "complete header did not produce a reply")
    checkBytes first suffix.utf8ByteSize
    checkBytes (← document (← xmppSessionFeed session "")) suffix.utf8ByteSize
    checkBytes (← document (← xmppSessionFeed session "'/>")) 0
    let _ ← document (← xmppSessionClose session)
    let sessions ← xmppSessions.get
    unless !sessions.contains session do throw (IO.userError "closed session retained")
    IO.println "XMPP_SESSION_BUFFER_REPORT={\"cases\":3,\"passed\":3,\"released\":true}"
  finally
    let _ ← xmppClose server
    pure ()

#eval run
