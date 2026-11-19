import L4Factoidal.Net.EventSource
import L4Factoidal.Net.Xhr

namespace L4Factoidal.Net.EventSource

open L4Factoidal.WHATWG

/-- Kind: EventSource parser and reconnect header counterexample
(factoidal-core issue 636).
Says: an admitted UTF-8 event stream can emit the last event ID `Ā` and
retain it for reconnect. The actual XHR header setter refuses that ID on
an opened GET but accepts an ASCII ID on the same opened request.
Does not say: that a running browser attempted the reconnect, sent a
request, or observed any particular timing or network response. -/
theorem unicode_last_event_id_header_refused :
    let stream : ByteArray := "id: Ā\ndata: x\n\n".toUTF8
    let parsed : Parser × List Event := parse {} (Encoding.utf8DecodeWithoutBOM stream)
    let initial : Xhr.State := { enabled := true, xhrs := #[{}] }
    let opened := Xhr.openX initial 1 "GET" "https://example.test/events" "" true
    isStream 200 "text/event-stream; charset=utf-8" = true ∧
      parsed.1.lastEventId = "Ā" ∧
      parsed.2.map Event.lastEventId = ["Ā"] ∧
      opened.2 = .ok "" ∧
      (Xhr.setHeaderX opened.1 1 "Last-Event-ID" parsed.1.lastEventId).2 = .error Xhr.errType ∧
      (Xhr.setHeaderX opened.1 1 "Last-Event-ID" "A").2 = .ok "" := by
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

#print axioms unicode_last_event_id_header_refused

end L4Factoidal.Net.EventSource
