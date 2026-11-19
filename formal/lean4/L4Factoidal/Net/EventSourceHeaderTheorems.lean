import L4Factoidal.Net.EventSource
import L4Factoidal.Net.Xhr
import Init.Data.String.Lemmas.Modify
import Init.Data.String.Lemmas.Pattern.Find.Pred
import Init.Data.String.Lemmas.Pattern.TakeDrop.Pred

namespace L4Factoidal.Net.EventSource

open L4Factoidal.WHATWG

-- Certify just the byte positions the shipped legacy splitter visits.
private theorem split_skip_positions {s sep : String} {base : String.Pos.Raw} {acc answer : List String}
    {pos : Nat} (rest : List Nat)
    (walk : (List.zipWith (fun i j : Nat =>
      let p : String.Pos.Raw := ⟨i⟩
      decide (p.atEnd s = false ∧ (p.get s == (0 : String.Pos.Raw).get sep) = false ∧
        (p.unoffsetBy 0).next s = ⟨j⟩)) (pos :: rest) rest).all id = true)
    (suffix : String.splitOnAux s sep base ⟨rest.getLastD pos⟩ 0 acc = answer) :
    String.splitOnAux s sep base ⟨pos⟩ 0 acc = answer := by
  induction rest generalizing pos with
  | nil => exact suffix
  | cons j js ih =>
    obtain ⟨first, tail⟩ := Bool.and_eq_true_iff.mp walk
    obtain ⟨inside, differs, advance⟩ := of_decide_eq_true first
    rw [List.getLastD_cons] at suffix
    have nextPos : (String.Pos.Raw.mk pos).next s = ⟨j⟩ := by
      simpa only [String.Pos.Raw.unoffsetBy_zero] using advance
    have next := ih (pos := j) tail suffix
    rw [String.splitOnAux]
    simpa [inside, differs, nextPos] using next

private theorem split_at_separator {s sep : String} {base mark : String.Pos.Raw} {acc answer : List String}
    (after : String.Pos.Raw) (piece : String)
    (shape : mark.atEnd s = false ∧ (mark.get s == (0 : String.Pos.Raw).get sep) = true ∧
      ((0 : String.Pos.Raw).next sep).atEnd sep = true ∧ mark.next s = after ∧
      base.extract s (after.unoffsetBy ((0 : String.Pos.Raw).next sep)) = piece)
    (suffix : String.splitOnAux s sep after after 0 (piece :: acc) = answer) :
    String.splitOnAux s sep base mark 0 acc = answer := by
  obtain ⟨inside, hit, complete, advance, emit⟩ := shape
  rw [String.splitOnAux]
  simpa [inside, hit, complete, advance, emit] using suffix

private theorem split_at_end {s sep head tail : String} {base pos : String.Pos.Raw}
    (shape : pos.atEnd s = true ∧ base.extract s pos = tail) :
    String.splitOnAux s sep base pos 0 [head] = [head, tail] := by
  rw [String.splitOnAux, if_pos shape.1, shape.2] <;> rfl

private theorem sample_mime_parts :
    "text/event-stream; charset=utf-8".splitOn ";" = ["text/event-stream", " charset=utf-8"] := by
  rw [String.splitOn, if_neg (by decide)]
  apply split_skip_positions [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17]
  · cbv
  apply split_at_separator ⟨18⟩ "text/event-stream"
  · cbv
  apply split_skip_positions [19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32]
  · cbv
  apply split_at_end
  cbv

private theorem sample_mime_trim : "text/event-stream".trimAscii.toString = "text/event-stream" := by
  have first : "text/event-stream".toSlice.startsWith Char.isWhitespace = false := by
    rw [String.Slice.startsWith_bool_eq_head?, String.copy_toSlice] <;> cbv
  have last : "text/event-stream".toSlice.endsWith Char.isWhitespace = false := by
    rw [String.Slice.endsWith_bool_eq_getLast?, String.copy_toSlice] <;> cbv
  change (("text/event-stream".toSlice.dropWhile Char.isWhitespace).dropEndWhile Char.isWhitespace).copy = _
  rw [String.Slice.dropWhile_eq_self first, String.Slice.dropEndWhile_eq_self last, String.copy_toSlice]

private theorem sample_mime_lower : "text/event-stream".toLower = "text/event-stream" := by
  apply String.toList_injective
  simp only [String.toLower, String.toList_map] <;> cbv

private theorem sample_mime : isStream 200 "text/event-stream; charset=utf-8" = true := by
  simp only [isStream, sample_mime_parts, List.headD_cons, sample_mime_trim, sample_mime_lower] <;> rfl

private theorem sample_utf8 :
    Encoding.utf8DecodeWithoutBOM "id: Ā\ndata: x\n\n".toUTF8 = "id: Ā\ndata: x\n\n" := by
  cbv

private theorem sample_lines :
    lines "id: Ā\ndata: x\n\n" = (["id: Ā", "data: x", ""], "") := by cbv

private theorem sample_no_bom : "id: Ā\ndata: x\n\n".startsWith "﻿" = false := by cbv

private theorem sample_id_parts : "id: Ā".splitOn ":" = ["id", " Ā"] := by
  rw [String.splitOn, if_neg (by decide)]
  apply split_skip_positions [1, 2]
  · cbv
  apply split_at_separator ⟨3⟩ "id"
  · cbv
  apply split_skip_positions [4, 6]
  · cbv
  apply split_at_end
  cbv

private theorem sample_data_parts : "data: x".splitOn ":" = ["data", " x"] := by
  rw [String.splitOn, if_neg (by decide)]
  apply split_skip_positions [1, 2, 3, 4]
  · cbv
  apply split_at_separator ⟨5⟩ "data"
  · cbv
  apply split_skip_positions [6, 7]
  · cbv
  apply split_at_end
  cbv

attribute [local cbv_eval] sample_id_parts sample_data_parts

private theorem sample_parse :
    parse {} "id: Ā\ndata: x\n\n" =
      ({ idBuffer := "Ā", lastEventId := "Ā" },
       [{ type := "message", data := "x", lastEventId := "Ā" }]) := by
  simp only [parse, sample_no_bom, Bool.false_eq_true, if_false, sample_lines]
  cbv

private theorem sample_host_parts : "example.test".splitOn "." = ["example", "test"] := by
  rw [String.splitOn, if_neg (by decide)]
  apply split_skip_positions [1, 2, 3, 4, 5, 6, 7]
  · cbv
  apply split_at_separator ⟨8⟩ "example"
  · cbv
  apply split_skip_positions [9, 10, 11, 12]
  · cbv
  apply split_at_end
  cbv

private theorem sample_host_decode :
    Encoding.utf8DecodeWithoutBOM (URL.percentDecode "example.test".toUTF8) = "example.test" := by cbv

private theorem sample_domain : URL.domainParser "example.test" false = some "example.test" := by
  have ascii : "example.test".toList.all (fun c => c.toNat < 0x80) = true := by cbv
  have lower : URL.asciiLowerStr "example.test" = "example.test" := by
    apply String.toList_injective
    simp only [URL.asciiLowerStr, String.toList_map] <;> cbv
  have safe : "example.test".toList.any URL.isForbiddenDomain = false := by cbv
  have nonempty : "example.test".isEmpty = false := rfl
  simp [URL.domainParser, ascii, lower, safe, nonempty]

private theorem sample_host : URL.parseHost "example.test" false = some (.domain "example.test") := by
  have bare : "example.test".startsWith "[" = false := by cbv
  have domainName : URL.endsInANumber "example.test" = false := by
    simp only [URL.endsInANumber, sample_host_parts] <;> cbv
  simp [URL.parseHost, bare, sample_host_decode, sample_domain, domainName]

attribute [local cbv_eval] sample_host

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
  have wide : "Ā".any (fun (c : Char) => c.toNat > 255) = true := by
    simp only [String.any, String.contains_prop_eq] <;> cbv
  have narrow : "A".any (fun (c : Char) => c.toNat > 255) = false := by
    simp only [String.any, String.contains_prop_eq] <;> cbv
  have name : Xhr.isToken "Last-Event-ID" = true := by cbv
  have trim : PageFetch.trimWs "A" = "A" := by cbv
  have clean : "A".any (fun (c : Char) => c == '\x00' || c == '\n' || c == '\r') = false := by
    simp only [String.any, String.contains_bool_eq] <;> cbv
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
