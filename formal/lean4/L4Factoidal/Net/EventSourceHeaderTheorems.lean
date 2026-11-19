import L4Factoidal.Net.EventSource
import L4Factoidal.Net.Xhr

namespace L4Factoidal.Net.EventSource

open L4Factoidal.WHATWG

private theorem sample_mime : isStream 200 "text/event-stream; charset=utf-8" = true := by
  cbv

private theorem sample_utf8 :
    Encoding.utf8DecodeWithoutBOM "id: Ā\ndata: x\n\n".toUTF8 = "id: Ā\ndata: x\n\n" := by
  cbv

private theorem sample_parse :
    parse {} "id: Ā\ndata: x\n\n" =
      ({ idBuffer := "Ā", lastEventId := "Ā" },
       [{ type := "message", data := "x", lastEventId := "Ā" }]) := by
  cbv

private theorem sample_url : (URL.parseUrl "https://example.test/events" none).isSome = true := by
  cbv

private theorem sample_open (u : URL.Url)
    (parsed : URL.parseUrl "https://example.test/events" none = some u) :
    let initial : Xhr.State := { enabled := true, xhrs := #[{}] }
    let opened := Xhr.openX initial 1 "GET" "https://example.test/events" "" true
    opened.2 = .ok "" ∧ ∃ x, opened.1.get? 1 = some x ∧ x.state = 1 ∧ x.sendFlag = false := by
  have atHandle : ({ enabled := true, xhrs := #[{}] } : Xhr.State).get? 1 = some {} := rfl
  have token : Xhr.isToken "GET" = true := by cbv
  have allowed : PageFetch.forbiddenMethod "GET" = false := by cbv
  have noBase : (if "".isEmpty then none else some "") = none := rfl
  dsimp only
  simp only [Xhr.openX, atHandle, token, allowed, noBase, parsed, Bool.not_true,
    Bool.false_eq_true, if_false]
  exact ⟨rfl, _, rfl, rfl, rfl⟩

private theorem sample_headers (s : Xhr.State) (x : Xhr.Xhr)
    (present : s.get? 1 = some x) (ready : x.state = 1) (idle : x.sendFlag = false) :
    (Xhr.setHeaderX s 1 "Last-Event-ID" "Ā").2 = .error Xhr.errType ∧
      (Xhr.setHeaderX s 1 "Last-Event-ID" "A").2 = .ok "" := by
  have wide : "Ā".any (fun (c : Char) => c.toNat > 255) = true := by cbv
  have narrow : "A".any (fun (c : Char) => c.toNat > 255) = false := by cbv
  have name : Xhr.isToken "Last-Event-ID" = true := by cbv
  have trim : PageFetch.trimWs "A" = "A" := by cbv
  have clean : "A".any (fun (c : Char) => c == '\x00' || c == '\n' || c == '\r') = false := by cbv
  constructor
  · simp [Xhr.setHeaderX, present, ready, idle, wide]
  · simp [Xhr.setHeaderX, present, ready, idle, narrow, name, trim, clean] <;> split <;> rfl

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
  obtain ⟨u, hu⟩ := Option.isSome_iff_exists.mp sample_url
  obtain ⟨opened, x, present, ready, idle⟩ := sample_open u hu
  obtain ⟨refused, accepted⟩ := sample_headers _ x present ready idle
  dsimp only
  rw [sample_utf8, sample_parse]
  exact ⟨sample_mime, rfl, rfl, opened, refused, accepted⟩

#print axioms unicode_last_event_id_header_refused

end L4Factoidal.Net.EventSource
