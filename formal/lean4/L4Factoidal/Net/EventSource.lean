/-
L4Factoidal.Net.EventSource — the event stream of server-sent events (HTML §9.2.6
"Interpreting an event stream", §9.2.5 "Processing model"): what a response's text means as
events, and whether a response may be read as a stream at all.

The request is a page request like any other (`Net.Xhr`, `Net.PageFetch`: CORS, the address
rules, credentials); this file reads its answer.

## Decisions

* The stream is UTF-8; one leading BOM is removed; lines end at CRLF, LF or CR.
* A line that starts with `:` is a comment. Otherwise the field name runs to the first `:` and
  the value after it, less one leading space; a line with no `:` is a field with an empty value.
* `event` sets the event type; `data` appends the value and a LF; `id` sets the last event ID
  unless the value has U+0000; `retry` sets the reconnection time when the value is ASCII
  digits only; other fields are ignored.
* An empty line dispatches: with no data nothing is dispatched (the type is reset); the data's
  last LF is removed; the type is "message" when none was given. Data not ended by an empty
  line when the stream ends is discarded.
* A response is a stream only with status 200 and the MIME type `text/event-stream`
  (parameters allowed); any other fails the connection for good (no reconnection).

## What is proved

`parse_id_nul`: a value with U+0000 never becomes the last event ID. `parse_retry_digits`: a
reconnection time comes only from ASCII digits. `dispatch_no_trailing_lf`: dispatched data
never ends with the LF the last `data` line added.
-/
namespace L4Factoidal.Net.EventSource

/-- One event to dispatch. -/
structure Event where
  type : String
  data : String
  lastEventId : String
  deriving DecidableEq, Repr, Inhabited

/-- The parser's buffers (§9.2.6) and the stream's state. -/
structure Parser where
  data : String := ""
  eventType : String := ""
  /-- The last event ID buffer, and the last event ID string of the source. -/
  idBuffer : String := ""
  lastEventId : String := ""
  /-- The reconnection time in ms, when a `retry` field set it. -/
  retry : Option Nat := none
  deriving DecidableEq, Repr, Inhabited

/-- ASCII digits, at least one. -/
def allDigits (s : String) : Bool := !s.isEmpty && s.all Char.isDigit

/-- A field with its value (§9.2.6 "process the field"). -/
def field (p : Parser) (name value : String) : Parser :=
  if name == "event" then { p with eventType := value }
  else if name == "data" then { p with data := p.data ++ value ++ "\n" }
  else if name == "id" then (if value.contains '\u0000' then p else { p with idBuffer := value })
  else if name == "retry" then (if allDigits value then { p with retry := value.toNat? } else p)
  else p

/-- Remove one trailing LF. -/
def dropLf (s : String) : String := if s.endsWith "\n" then (s.dropEnd 1).toString else s

/-- An empty line: dispatch the event (§9.2.6 "dispatch the event"). -/
def dispatch (p : Parser) : Parser × Option Event :=
  let p := { p with lastEventId := p.idBuffer }
  if p.data.isEmpty then ({ p with eventType := "" }, none)
  else
    let ev : Event := { type := if p.eventType.isEmpty then "message" else p.eventType, data := dropLf p.data,
                        lastEventId := p.lastEventId }
    ({ p with data := "", eventType := "" }, some ev)

/-- One line of the stream. -/
def line (p : Parser) (l : String) : Parser × Option Event :=
  if l.isEmpty then dispatch p
  else if l.startsWith ":" then (p, none)
  else
    match l.splitOn ":" with
    | [] | [_] => (field p l "", none)
    | name :: rest =>
      let v := ":".intercalate rest
      (field p name (if v.startsWith " " then (v.drop 1).toString else v), none)

/-- Split a stream's text into its lines: CRLF, LF and CR end a line; the text after the last
end is not a line yet. -/
def lines (text : String) : List String × String := Id.run do
  let mut out : Array String := #[]
  let mut cur : List Char := []
  let mut cr := false
  for c in text.toList do
    if cr && c == '\n' then cr := false; continue
    cr := false
    if c == '\n' || c == '\r' then
      out := out.push (String.ofList cur.reverse); cur := []
      if c == '\r' then cr := true
    else cur := c :: cur
  return (out.toList, String.ofList cur.reverse)

/-- The events of a whole response's text (the stream ended after it), from the source's
parser state: its last event ID and reconnection time carry over to the next connection. -/
def parse (p : Parser) (text : String) : Parser × List Event := Id.run do
  let text := if text.startsWith "﻿" then (text.drop 1).toString else text
  let (ls, _) := lines text
  let mut p := { p with data := "", eventType := "" }
  let mut evs : Array Event := #[]
  for l in ls do
    let (p', e) := line p l
    p := p'
    if let some e := e then evs := evs.push e
  -- data not ended by an empty line is discarded at the end of the stream
  return ({ p with data := "", eventType := "" }, evs.toList)

/-- A response that is an event stream: status 200, MIME type `text/event-stream`. -/
def isStream (status : Nat) (contentType : String) : Bool :=
  let essence := ((contentType.splitOn ";").headD "").trimAscii.toString.toLower
  status == 200 && essence == "text/event-stream"

/-! ## Examples (WPT eventsource/format-*.any.js) -/

#guard (parse {} "data: data\n\n").2 == [{ type := "message", data := "data", lastEventId := "" }]
#guard (parse {} "data:1\r\ndata:2\rdata:3\n\n").2 == [{ type := "message", data := "1\n2\n3", lastEventId := "" }]
#guard (parse {} ":comment\nevent: test\ndata: x\nid: 7\n\n").2 == [{ type := "test", data := "x", lastEventId := "7" }]
#guard (parse {} "id: a\u0000b\ndata: x\n\n").2 == [{ type := "message", data := "x", lastEventId := "" }]
#guard (parse {} "retry: 1000\ndata: x\n\n").1.retry == some 1000
#guard (parse {} "retry: 10x\ndata: x\n\n").1.retry == none
#guard (parse {} "data: x").2 == []
#guard (parse {} "﻿data: x\n\n").2.length == 1
#guard (parse {} "data\n\n").2 == [{ type := "message", data := "", lastEventId := "" }]
#guard (parse {} "event: x\n\ndata: y\n\n").2 == [{ type := "message", data := "y", lastEventId := "" }]
#guard (parse {} "data:  two spaces\n\n").2.map (·.data) == [" two spaces"]
#guard isStream 200 "text/event-stream; charset=utf-8" && !isStream 200 "text/plain" && !isStream 204 "text/event-stream"

/-! ## Theorems -/

/-- Kind: correctness theorem (§9.2.6, `id`). Says: an `id` value with U+0000 never becomes the
last event ID buffer. -/
theorem parse_id_nul (p : Parser) (v : String) (h : v.contains '\u0000' = true) : field p "id" v = p := by
  simp [field, h]

/-- Kind: correctness theorem (§9.2.6, `retry`). Says: a field sets the reconnection time only
when its name is `retry` and its value is ASCII digits. -/
theorem parse_retry_digits (p : Parser) (name v : String) (h : (field p name v).retry ≠ p.retry) :
    name = "retry" ∧ allDigits v = true := by
  unfold field at h
  by_cases h1 : name = "event"
  · subst h1; simp at h
  · by_cases h2 : name = "data"
    · subst h2; simp at h
    · by_cases h3 : name = "id"
      · subst h3
        exfalso; apply h
        simp only [beq_self_eq_true, if_true, show ("id" == "event") = false from rfl, show ("id" == "data") = false from rfl,
          Bool.false_eq_true, if_false]
        split <;> rfl
      · by_cases h4 : name = "retry"
        · subst h4
          refine ⟨rfl, ?_⟩
          simp only [beq_iff_eq] at h
          simp only [h1, h2, h3, if_false, if_true] at h
          by_cases hd : allDigits v = true
          · exact hd
          · simp [hd] at h
        · simp [h1, h2, h3, h4] at h

/-- Kind: correctness theorem (§9.2.6, dispatch). Says: an event is dispatched only with data,
and its data is the buffer less the one trailing LF. -/
theorem dispatch_no_trailing_lf (p p' : Parser) (e : Event) (h : dispatch p = (p', some e)) :
    p.data ≠ "" ∧ e.data = dropLf p.data := by
  unfold dispatch at h
  by_cases hd : p.data.isEmpty = true
  · simp [hd] at h
  · simp only [hd, if_false, Bool.false_eq_true, Prod.mk.injEq, Option.some.injEq] at h
    refine ⟨fun h0 => hd (by simp [h0]), ?_⟩
    rw [← h.2]

end L4Factoidal.Net.EventSource
