/-
Copyright (c) 2026 Dan Brickley. Released under the Apache 2.0 license.
Round trips for the executable navigation-cookie wire format. This proof module is
separate from the engine so the standard library's decimal proof adds no runtime import.
-/
import L4Factoidal.Net.Cookies
import Std.Data.String.ToNat

namespace L4Factoidal.Net.Cookies

/-- Kind: framing lemma.
Says: reading one escaped field consumes it and passes the original characters to the continuation.
Does not say: anything about the fields a cookie may contain. -/
private theorem readField (sep : Char) (hsep : sep ≠ '\\') (xs rest chars : List Char)
    (done : List String) :
    Wire.read sep (xs.flatMap (Wire.escapeChar sep) ++ sep :: rest) false chars done =
    Wire.read sep rest false [] (String.ofList (chars.reverse ++ xs) :: done) := by
  induction xs generalizing chars with
  | nil => simp [Wire.read, hsep]
  | cons c xs ih =>
    by_cases esc : c = '\\'
    · subst c
      simp [Wire.escapeChar, Wire.read, List.append_assoc, ih]
    · by_cases eq : c = sep
      · subst c
        simp [Wire.escapeChar, Wire.read, hsep, List.append_assoc, ih]
      · simp [Wire.escapeChar, Wire.read, esc, eq, List.append_assoc, ih]

/-- Kind: codec round trip.
Says: the framing recovers every string in order, including empty strings and literal delimiters.
Does not say: a field decodes as a valid cookie. -/
theorem Wire.read_fields (sep : Char) (hsep : sep ≠ '\\') (ss done : List String) :
    Wire.read sep (Wire.fields sep ss) false [] done = some (done.reverse ++ ss) := by
  induction ss generalizing done with
  | nil => simp [Wire.fields, Wire.read]
  | cons s ss ih =>
    change Wire.read sep (((s.toList.flatMap (Wire.escapeChar sep) ++ [sep]) ++ Wire.fields sep ss))
      false [] done = _
    rw [List.append_assoc, List.singleton_append, readField sep hsep]
    simp [ih, List.append_assoc]

/-- Kind: codec round trip.
Says: writing and reading a cookie accepted by the storage checks preserves all nine fields.
Does not say: a file came from a server or that a host wrote it to disk. -/
theorem Cookie.ofWire_wire (c : Cookie) (hv : c.storageOK = true) : Cookie.ofWire c.wire = some c := by
  have hs : c.sameSite ≤ 3 := by
    simp only [Cookie.storageOK, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.2.2
  unfold Cookie.ofWire Cookie.wire
  rw [String.toList_ofList, Wire.read_fields ';' (by decide)]
  simp only [List.reverse_nil, List.nil_append]
  have expiry (e : Option Nat) : ((e.map Nat.repr).getD "").toNat? = e := by
    cases e with
    | none =>
      apply String.toNat?_eq_none
      simp [Bool.eq_false_iff, String.isNat_iff]
    | some n => exact Nat.toNat?_repr n
  cases c with
  | mk name value host path secure httpOnly expires created sameSite =>
    cases secure <;> cases httpOnly <;>
      simp [Cookie.fromFields, Cookie.wireFields, expiry, Nat.min_eq_right hs, hv, Option.filter_some]

/-- Kind: admission invariant.
Says: every cookie accepted from an HTTP header can be read back after writing it.
Does not say: its site or clock came from a particular host implementation. -/
theorem parseForHeader_wire (site : Site) (now : Nat) (header : String) (c : Cookie)
    (h : parseForHeader site now header = some c) : Cookie.ofWire c.wire = some c := by
  apply Cookie.ofWire_wire
  unfold parseForHeader at h
  split at h
  · cases h
  · exact (Option.filter_eq_some_iff.mp h).2

/-- Kind: admission invariant.
Says: every cookie accepted from a script can be read back after writing it.
Does not say: a script can see an HttpOnly cookie. -/
theorem parseForScript_wire (site : Site) (now : Nat) (text : String) (c : Cookie)
    (h : parseForScript site now text = some c) : Cookie.ofWire c.wire = some c := by
  apply Cookie.ofWire_wire
  unfold parseForScript at h
  split at h
  · cases h
  · split at h
    · cases h
    · exact (Option.filter_eq_some_iff.mp h).2

/-- Kind: framing lemma.
Says: the two framing levels recover every row's fields in order.
Does not say: these rows meet the store's checks. -/
private theorem readRowFields (cs : List Cookie) :
    (cs.map Cookie.wire).filterMap (fun row => Wire.read ';' row.toList false [] []) =
      cs.map Cookie.wireFields := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp [Cookie.wire, Wire.read_fields ';' (by decide), ih]

/-- Kind: codec lemma.
Says: validating the fields of stored cookies recovers the entire list, including its ordering.
Does not say: arbitrary text passes validation. -/
private theorem readStoredRows (cs : List Cookie) (hv : ∀ c ∈ cs, c.storageOK = true) :
    (cs.map Cookie.wireFields).filterMap Cookie.fromFields = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := Cookie.ofWire_wire c (hv c (by simp))
    simp [Cookie.ofWire, Cookie.wire, Wire.read_fields ';' (by decide)] at hc
    simp [hc, ih (fun d hd => hv d (by simp [hd]))]

/-- Kind: persistence round trip.
Says: all stored cookies and their order survive a jar round trip. The reader repairs an
externally supplied next counter by raising it above every recovered creation number.
Does not say: a host completed the file write. -/
theorem Jar.ofWire_wire_normalized (j : Jar) (hv : ∀ c ∈ j.cookies, c.storageOK = true) :
    Jar.ofWire j.wire =
      { cookies := j.cookies, next := j.cookies.foldl (fun n c => max n (c.created + 1)) j.next } := by
  have hrows : Jar.wireRows j.wire = (j.next.repr, j.cookies.map Cookie.wireFields) := by
    simp only [Jar.wire, Jar.wireRows, String.toList_ofList, Wire.read_fields '\n' (by decide),
      List.reverse_nil, List.nil_append]
    rw [readRowFields]
  simp [Jar.ofWire, hrows, readStoredRows j.cookies hv]

/-- Kind: counter invariant.
Says: the reader preserves an existing next counter above every creation number.
Does not say: a larger counter is ever needed for an engine-created jar. -/
private theorem foldCreated (cs : List Cookie) (n : Nat) (h : ∀ c ∈ cs, c.created < n) :
    cs.foldl (fun next c => max next (c.created + 1)) n = n := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc := h c (by simp)
    rw [List.foldl_cons, Nat.max_eq_left (by omega : c.created + 1 ≤ n)]
    exact ih (fun d hd => h d (by simp [hd]))

/-- Kind: persistence round trip.
Says: reading the emitted jar reconstructs it exactly when its cookies meet admission and
the next creation number exceeds all stored creation numbers. The empty jar qualifies.
Does not say: whether a host retained session cookies or wrote a particular file. -/
theorem Jar.ofWire_wire (j : Jar) (hv : ∀ c ∈ j.cookies, c.storageOK = true)
    (hn : ∀ c ∈ j.cookies, c.created < j.next) : Jar.ofWire j.wire = j := by
  rw [Jar.ofWire_wire_normalized j hv, foldCreated j.cookies j.next hn]

#print axioms Wire.read_fields
#print axioms Cookie.ofWire_wire
#print axioms parseForHeader_wire
#print axioms parseForScript_wire
#print axioms Jar.ofWire_wire_normalized
#print axioms Jar.ofWire_wire

end L4Factoidal.Net.Cookies
