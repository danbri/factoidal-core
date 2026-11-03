/-
L4Factoidal.WHATWG.URL.Theorems — the WHATWG URL Standard's path state and
RFC 3986 reference resolution give the same path for the paths that both read
alike.

Versions: URL Standard, WHATWG Living Standard, Last Updated 19 October 2026
(commit snapshot whatwg/url `845bafca`), section 4.4 "path state", step 1;
RFC 3986 (January 2005), section 5.2.4 "Remove Dot Segments", as implemented
by `L4Factoidal.Syntax.removeDotSegments` (`Syntax/IriResolve.lean`, the
RFC 3986 resolver of the Lean tree).

What is proved:

- `pathSegment_segments`: `Url.pathSegment`, the function the parser's path
  state calls for each segment, acts on the segment list of a URL whose scheme
  is not "file" as the list function `segRule` (shorten on `..`, nothing on
  `.`, append otherwise; a final dot segment appends the empty segment).
- `rfc3986_removeDotSegments_eq_whatwg`: for an absolute path made of segments
  without `/`, in which a segment is a WHATWG single-dot (double-dot) segment
  exactly when it is `.` (`..`), the RFC 3986 algorithm gives the URL path
  serialization of the segment list that `segRule` builds from the empty path.
  The hypothesis excludes `%2e`, `%2E` and their combinations, which the URL
  Standard reads as dots and RFC 3986 does not (RFC 3986 section 2.3 lets a
  normalizer decode them first; `removeDotSegments` does not).
- `whatwg2026_path_eq_rfc3986`: the two above composed: folding
  `Url.pathSegment` over the segments, from a non-file URL with an empty path,
  gives a URL whose path serialization is `removeDotSegments` of the path.

What is not proved: that the whole basic URL parser, run on a reference and a
base, gives the RFC 3986 resolution of the reference where both accept the
input. That statement is measured instead (`l4whatwg-url rfc3986`, run by
tests/whatwg-url/run.sh) and tracked in
https://github.com/danbri/factoidal/issues/1188.

https://github.com/danbri/factoidal/issues/1167, milestone 3. No `sorry`.
-/
import L4Factoidal.WHATWG.URL.Parser
import L4Factoidal.Syntax.IriResolve

namespace L4Factoidal.WHATWG.URL.Theorems

open L4Factoidal.WHATWG.URL
open L4Factoidal.Syntax

/-! ## The segment rule as a list function -/

/-- The path state's rule for one segment, on a list of segments, for a URL
whose scheme is not "file", with `seg` read as `.` or `..` only when it is
that string. -/
def segRule (ws : List String) (seg : String) (slash : Bool) : List String :=
  if seg == ".." then (if slash then ws.dropLast else ws.dropLast ++ [""])
  else if seg == "." then (if slash then ws else ws ++ [""])
  else ws ++ [seg]

/-- The segments of an absolute path, read in order: every segment but the
last is followed by `/`. -/
def wpFold (ws : List String) : List String → List String
  | [] => ws
  | [s] => segRule ws s false
  | s :: t :: rest => wpFold (segRule ws s true) (t :: rest)

/-- A segment that the URL Standard and RFC 3986 read alike: no `/`, and a
WHATWG dot segment exactly when it is `.` or `..`. -/
def ReadAlike (s : String) : Prop :=
  '/' ∉ s.toList ∧ isSingleDot s = (s == ".") ∧ isDoubleDot s = (s == "..")

theorem pathSegment_segments (u : Url) (xs : Array String) (b : String) (sl : Bool)
    (hfile : u.scheme ≠ "file") (hp : u.path = .segments xs) (hb : ReadAlike b) :
    ∃ ys, (u.pathSegment b sl).path = .segments ys ∧ ys.toList = segRule xs.toList b sl := by
  obtain ⟨_, h1, h2⟩ := hb
  have hf : (u.scheme == "file") = false := by simpa using hfile
  unfold Url.pathSegment segRule
  rw [h1, h2]
  by_cases hd : (b == "..") = true
  · simp only [hd, if_true]
    have hs : (u.shortenPath).path = .segments xs.pop := by
      simp [Url.shortenPath, hp, hf]
    cases sl
    · refine ⟨xs.pop.push "", ?_, ?_⟩
      · simp [Url.appendSegment, hs]
      · simp [Array.toList_pop]
    · exact ⟨xs.pop, by simp [hs], by simp [Array.toList_pop]⟩
  · simp only [Bool.not_eq_true] at hd
    simp only [hd]
    by_cases hdot : (b == ".") = true
    · simp only [hdot, if_true]
      cases sl
      · exact ⟨xs.push "", by simp [Url.appendSegment, hp], by simp⟩
      · exact ⟨xs, by simp [hp], by simp⟩
    · simp only [Bool.not_eq_true] at hdot
      simp only [hdot]
      refine ⟨xs.push b, ?_, by simp⟩
      simp [Url.appendSegment, hp, hf]

/-! ## The RFC 3986 side -/

/-- The output list of `removeDotSegmentsStep` that stands for the WHATWG
segment list `ws`: the root `/` last, each segment with its `/`, newest
first. -/
def rfcOut (ws : List String) : List String := (ws.map (· ++ "/")).reverse ++ ["/"]

/-- The URL path serialization of a segment list. -/
def serializeSegs (ws : List String) : String := String.join (ws.map ("/" ++ ·))

theorem join_slash_shift (ws : List String) :
    "/" ++ String.join (ws.map (· ++ "/")) = serializeSegs ws ++ "/" := by
  induction ws with
  | nil => simp [serializeSegs]
  | cons w t ih =>
    simp only [List.map_cons, String.join_cons, serializeSegs] at ih ⊢
    simp only [String.append_assoc]
    rw [ih]

theorem join_rfcOut (ws : List String) :
    String.join (rfcOut ws).reverse = serializeSegs ws ++ "/" := by
  simp only [rfcOut, List.reverse_append, List.reverse_reverse, List.reverse_cons,
    List.reverse_nil, List.nil_append, List.cons_append, String.join_cons]
  exact join_slash_shift ws

theorem popKeepRoot_cons_snoc (x y : String) (a : List String) :
    popKeepRoot (x :: (a ++ [y])) = a ++ [y] := by
  cases a <;> rfl

theorem popKeepRoot_rfcOut (ws : List String) : popKeepRoot (rfcOut ws) = rfcOut ws.dropLast := by
  rcases List.eq_nil_or_concat ws with h | ⟨l, b, h⟩
  · subst h; simp [rfcOut, popKeepRoot]
  · subst h
    simp only [List.concat_eq_append, rfcOut, List.map_append, List.map_cons, List.map_nil,
      List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.cons_append, List.dropLast_concat]
    exact popKeepRoot_cons_snoc _ _ _

theorem rfcOut_ne_nil (ws : List String) : rfcOut ws ≠ [] := by simp [rfcOut]

theorem loop_slash (s r acc : List Char) (h : '/' ∉ s) :
    List.span.loop (fun c => !(c == '/')) (s ++ '/' :: r) acc = (acc.reverse ++ s, '/' :: r) := by
  induction s generalizing acc with
  | nil => simp [List.span.loop]
  | cons c cs ih =>
    have hc : c ≠ '/' := fun e => h (e ▸ List.mem_cons_self)
    have hcs : '/' ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    have hc' : (c == '/') = false := by simpa using hc
    simp [List.span.loop, hc', ih _ hcs]

theorem loop_noslash (s acc : List Char) (h : '/' ∉ s) :
    List.span.loop (fun c => !(c == '/')) s acc = (acc.reverse ++ s, []) := by
  induction s generalizing acc with
  | nil => simp [List.span.loop]
  | cons c cs ih =>
    have hc : c ≠ '/' := fun e => h (e ▸ List.mem_cons_self)
    have hcs : '/' ∉ cs := fun m => h (List.mem_cons_of_mem _ m)
    have hc' : (c == '/') = false := by simpa using hc
    simp [List.span.loop, hc', ih _ hcs]

/-- The characters of the segments joined by `/`. -/
def joinSlash : List String → List Char
  | [] => []
  | [s] => s.toList
  | s :: t :: rest => s.toList ++ '/' :: joinSlash (t :: rest)

/-- `dotSegmentStep` with a `/` after the segment acts on `rfcOut` as
`segRule` with slash. -/
theorem dotSegmentStep_slash (ws : List String) (s : String) :
    dotSegmentStep s true (rfcOut ws) = rfcOut (segRule ws s true) := by
  unfold dotSegmentStep segRule
  by_cases h1 : (s == ".") = true
  · have h2 : (s == "..") = false := by
      simp only [beq_iff_eq] at h1; subst h1; decide
    simp [h1, h2]
  · by_cases h2 : (s == "..") = true
    · have h1' : (s == ".") = false := by simpa using h1
      simp [h1', h2, popKeepRoot_rfcOut]
    · have h1' : (s == ".") = false := by simpa using h1
      have h2' : (s == "..") = false := by simpa using h2
      simp [h1', h2', segmentText, rfcOut]

/-- The last segment, with no `/` after it. -/
theorem dotSegmentStep_last (ws : List String) (s : String) :
    String.join (dotSegmentStep s false (rfcOut ws)).reverse
      = serializeSegs (segRule ws s false) := by
  unfold dotSegmentStep segRule
  by_cases h1 : (s == ".") = true
  · have h2 : (s == "..") = false := by
      simp only [beq_iff_eq] at h1; subst h1; decide
    simp only [h1, h2, if_true, Bool.false_eq_true, if_false]
    rw [join_rfcOut]; simp [serializeSegs]
  · by_cases h2 : (s == "..") = true
    · have h1' : (s == ".") = false := by simpa using h1
      simp only [h1', h2, if_true, Bool.false_eq_true, if_false, popKeepRoot_rfcOut]
      have hne := rfcOut_ne_nil ws.dropLast
      rcases hh : rfcOut ws.dropLast with _ | ⟨a, l⟩
      · exact absurd hh hne
      · show String.join (a :: l).reverse = _
        rw [← hh, join_rfcOut]; simp [serializeSegs]
    · have h1' : (s == ".") = false := by simpa using h1
      have h2' : (s == "..") = false := by simpa using h2
      simp only [h1', h2', Bool.false_eq_true, if_false, segmentText]
      rw [List.reverse_cons, String.join_append, join_rfcOut]
      simp [serializeSegs, String.append_assoc]

theorem step_cons (f : Nat) (x : Char) (xs : List Char) (out : List String) :
    removeDotSegmentsStep (f + 1) (x :: xs) out =
      removeDotSegmentsStep f
        (match ((x :: xs).span (fun c => !(c == '/'))).2 with | _ :: tl => tl | [] => [])
        (dotSegmentStep (String.ofList ((x :: xs).span (fun c => !(c == '/'))).1)
          (match ((x :: xs).span (fun c => !(c == '/'))).2 with | '/' :: _ => true | _ => false)
          out) := rfl

/-- The main simulation: from `rfcOut ws`, the RFC 3986 loop over the
remaining segments ends with the serialization of what `wpFold` builds. -/
theorem removeDotSegmentsStep_wpFold (segs : List String) (ws : List String) (fuel : Nat)
    (hne : segs ≠ []) (hfuel : segs.length ≤ fuel) (hs : ∀ s ∈ segs, '/' ∉ s.toList) :
    String.join (removeDotSegmentsStep fuel (joinSlash segs) (rfcOut ws))
      = serializeSegs (wpFold ws segs) := by
  induction segs generalizing ws fuel with
  | nil => exact absurd rfl hne
  | cons s rest ih =>
    obtain ⟨f, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by simp at hfuel; omega⟩
    have hs0 : '/' ∉ s.toList := hs s List.mem_cons_self
    cases rest with
    | nil =>
      simp only [joinSlash, wpFold]
      by_cases he : s.toList = []
      · have hse : s = "" := by simpa using he
        subst hse
        simp only [he, removeDotSegmentsStep]
        rw [join_rfcOut]; simp [segRule, serializeSegs]
      · obtain ⟨c, cs, hcs⟩ : ∃ c cs, s.toList = c :: cs := by
          cases h : s.toList with
          | nil => exact absurd h he
          | cons c cs => exact ⟨c, cs, rfl⟩
        rw [hcs]
        simp only [removeDotSegmentsStep]
        have hsp : List.span (fun c => !(c == '/')) (c :: cs) = (c :: cs, []) := by
          have := loop_noslash (c :: cs) [] (hcs ▸ hs0)
          simpa [List.span] using this
        simp only [hsp]
        have hof : String.ofList (c :: cs) = s := by rw [← hcs]; simp
        rw [hof]
        cases f <;> simp only [removeDotSegmentsStep] <;> exact dotSegmentStep_last ws s
    | cons t rest' =>
      simp only [joinSlash, wpFold]
      have hsp : List.span (fun c => !(c == '/')) (s.toList ++ '/' :: joinSlash (t :: rest'))
          = (s.toList, '/' :: joinSlash (t :: rest')) := by
        have := loop_slash s.toList (joinSlash (t :: rest')) [] hs0
        simpa [List.span] using this
      have hstep : removeDotSegmentsStep (f + 1) (s.toList ++ '/' :: joinSlash (t :: rest')) (rfcOut ws)
          = removeDotSegmentsStep f (joinSlash (t :: rest')) (dotSegmentStep s true (rfcOut ws)) := by
        obtain ⟨x, xs, hx⟩ : ∃ x xs, s.toList ++ '/' :: joinSlash (t :: rest') = x :: xs := by
          cases s.toList with
          | nil => exact ⟨'/', _, rfl⟩
          | cons c cs => exact ⟨c, _, rfl⟩
        rw [hx, step_cons, ← hx, hsp]
        simp
      rw [hstep, dotSegmentStep_slash]
      exact ih (segRule ws s true) f (by simp) (by simp at hfuel ⊢; omega)
        (fun x hx => hs x (List.mem_cons_of_mem _ hx))

theorem length_joinSlash (segs : List String) : segs.length ≤ (joinSlash segs).length + 1 := by
  induction segs with
  | nil => simp [joinSlash]
  | cons s rest ih =>
    cases rest with
    | nil => simp [joinSlash]
    | cons t rest' =>
      simp only [joinSlash, List.length_append, List.length_cons] at ih ⊢
      omega

theorem toList_intercalate_slash (segs : List String) :
    ("/".intercalate segs).toList = joinSlash segs := by
  induction segs with
  | nil => simp [joinSlash, String.intercalate]
  | cons s rest ih =>
    cases rest with
    | nil => simp [joinSlash, String.intercalate_singleton]
    | cons t rest' =>
      rw [String.intercalate_cons_cons]
      simp [joinSlash, ih]

/-- **RFC 3986 section 5.2.4 equals the WHATWG path state (2026-10-19) on
paths whose segments both read alike.** For an absolute path `/s1/.../sk`
(k ≥ 1, no `/` inside a segment), `removeDotSegments` gives the URL path
serialization of the segment list that the WHATWG rule builds from the empty
path, provided `.` and `..` are the only dot segments (`segRule` reads only
those). -/
theorem rfc3986_removeDotSegments_eq_whatwg (segs : List String) (hne : segs ≠ [])
    (hs : ∀ s ∈ segs, '/' ∉ s.toList) :
    removeDotSegments ("/" ++ "/".intercalate segs) = serializeSegs (wpFold [] segs) := by
  unfold removeDotSegments
  have htl : ("/" ++ "/".intercalate segs).toList = '/' :: joinSlash segs := by
    rw [String.toList_append, toList_intercalate_slash]; rfl
  have hlen : ("/" ++ "/".intercalate segs).length = (joinSlash segs).length + 1 := by
    rw [← String.length_toList, htl]; simp
  rw [htl, hlen]
  rw [show (joinSlash segs).length + 1 + 2 = ((joinSlash segs).length + 2) + 1 by omega, step_cons]
  have hsp : ('/' :: joinSlash segs).span (fun c => !(c == '/')) = ([], '/' :: joinSlash segs) := by
    simpa [List.span] using loop_slash [] (joinSlash segs) [] (by simp)
  rw [hsp]
  have h0 : dotSegmentStep (String.ofList []) true [] = rfcOut [] := by
    simp [dotSegmentStep, segmentText, rfcOut]
  simp only [h0]
  exact removeDotSegmentsStep_wpFold segs [] _ hne (by have := length_joinSlash segs; omega) hs

/-- Folding the parser's segment rule over the segments of a path. -/
def foldSegs (u : Url) : List String → Url
  | [] => u
  | [s] => u.pathSegment s false
  | s :: t :: rest => foldSegs (u.pathSegment s true) (t :: rest)

theorem pathSegment_scheme (u : Url) (b : String) (sl : Bool) :
    (u.pathSegment b sl).scheme = u.scheme := by
  unfold Url.pathSegment Url.shortenPath Url.appendSegment
  repeat (first | split | rfl | simp_all)

theorem foldSegs_segments (segs : List String) (u : Url) (xs : Array String)
    (hfile : u.scheme ≠ "file") (hp : u.path = .segments xs) (hs : ∀ s ∈ segs, ReadAlike s) :
    ∃ ys, (foldSegs u segs).path = .segments ys ∧ ys.toList = wpFold xs.toList segs := by
  induction segs generalizing u xs with
  | nil => exact ⟨xs, by simp [foldSegs, hp], by simp [wpFold]⟩
  | cons s rest ih =>
    cases rest with
    | nil => exact pathSegment_segments u xs s false hfile hp (hs s List.mem_cons_self)
    | cons t rest' =>
      obtain ⟨ys, hy, hyl⟩ := pathSegment_segments u xs s true hfile hp (hs s List.mem_cons_self)
      obtain ⟨zs, hz, hzl⟩ := ih (u.pathSegment s true) ys (by rw [pathSegment_scheme]; exact hfile)
        hy (fun x hx => hs x (List.mem_cons_of_mem _ hx))
      exact ⟨zs, hz, by rw [hzl, hyl]; rfl⟩

theorem foldl_slash (l : List String) (init : String) :
    l.foldl (fun acc s => acc ++ "/" ++ s) init = init ++ serializeSegs l := by
  induction l generalizing init with
  | nil => simp [serializeSegs]
  | cons x rest ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp only [serializeSegs, List.map_cons, String.join_cons, String.append_assoc]

/-- **The parser's path rule (URL Standard 2026-10-19) agrees with RFC 3986
section 5.2.4.** Start from a URL whose scheme is not "file" and whose path
is empty, apply `Url.pathSegment` (the function the path state runs at each
`/` and at the end) to the segments of `/s1/.../sk`; the URL path
serialization is `removeDotSegments` of that path, when no segment contains
`/` and `.` and `..` are its only dot segments. -/
theorem whatwg2026_path_eq_rfc3986 (u : Url) (segs : List String) (hne : segs ≠ [])
    (hfile : u.scheme ≠ "file") (hp : u.path = .segments #[]) (hs : ∀ s ∈ segs, ReadAlike s) :
    (foldSegs u segs).serializePath = removeDotSegments ("/" ++ "/".intercalate segs) := by
  obtain ⟨ys, hy, hyl⟩ := foldSegs_segments segs u #[] hfile hp hs
  rw [rfc3986_removeDotSegments_eq_whatwg segs hne (fun s h => (hs s h).1)]
  simp only [Url.serializePath, hy]
  rw [← Array.foldl_toList, hyl, foldl_slash]
  simp

/-- A segment without `%` and `/` reads alike in both standards. Checked on
the segments the RFC 3986 section 5.4 examples use. -/
def readAlikeB (s : String) : Bool :=
  !s.toList.contains '/' && isSingleDot s == (s == ".") && isDoubleDot s == (s == "..")

#guard ["g", ".", "..", "", "g;x", "b", "c", "d;p", "g.", ".g", "g..", "..g", "%2e", "%2E%2e"].map readAlikeB
  == [true, true, true, true, true, true, true, true, true, true, true, true, false, false]

end L4Factoidal.WHATWG.URL.Theorems
