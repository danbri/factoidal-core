/-
Class-atom names for the Direct certificate reader. Source IRIs and the
reader's nominal/data-cardinality abstractions occupy distinct constructors.
Concept.atom currently takes a String, so this module supplies a reversible
encoding at that boundary. Every source name is encoded as well: no reserved
IRI prefix or assumption about corpus names is needed.

Field framing preserves arbitrary characters, including delimiters and empty
strings. Decimal cardinalities retain logarithmic-size representations.
The round trip proves injectivity and pairwise constructor disjointness.
This naming theorem does not prove the RDF reader's semantic correctness.
-/
import Std

namespace L4Factoidal.OWL.CertNames

inductive Name where
  | source (iri : String)
  | nominal (members : List String)
  | dataMin (n : Nat) (property : String)
  | dataMax (n : Nat) (property : String)
deriving Repr, DecidableEq

-- Each payload character follows '+'. A bare ';' terminates a field.
-- The payload character itself may be '+' or ';'.
def frame : List Char → List Char
  | [] => [';']
  | c :: cs => '+' :: c :: frame cs

def frameAcc : List Char → List Char → List Char
  | [], acc => acc.reverse ++ [';']
  | c :: cs, acc => frameAcc cs (c :: '+' :: acc)

def frameTR (cs : List Char) : List Char := frameAcc cs []

theorem frameAcc_eq (cs acc : List Char) : frameAcc cs acc = acc.reverse ++ frame cs := by
  induction cs generalizing acc with
  | nil => rfl
  | cons c cs ih => simp [frameAcc, frame, ih, List.reverse_cons, List.append_assoc]

@[csimp] theorem frame_eq_frameTR : frame = frameTR := by
  funext cs
  simp [frameTR, frameAcc_eq]

def fields (ss : List String) : List Char := ss.flatMap (fun s => frame s.toList)

def readFields : List Char → List Char → List String → Option (List String)
  | [], [], acc => some acc.reverse
  | [], _ :: _, _ => none
  | ';' :: rest, chars, acc => readFields rest [] (String.ofList chars.reverse :: acc)
  | '+' :: c :: rest, chars, acc => readFields rest (c :: chars) acc
  | _ :: _, _, _ => none

theorem readFields_frame (cs rest chars : List Char) (acc : List String) :
    readFields (frame cs ++ rest) chars acc =
      readFields rest [] (String.ofList (chars.reverse ++ cs) :: acc) := by
  induction cs generalizing chars with
  | nil => simp [frame, readFields]
  | cons c cs ih => simp [frame, readFields, ih, List.reverse_cons, List.append_assoc]

theorem readFields_fields (ss acc : List String) :
    readFields (fields ss) [] acc = some (acc.reverse ++ ss) := by
  induction ss generalizing acc with
  | nil => simp [fields, readFields]
  | cons s ss ih =>
      simp only [fields, List.flatMap_cons]
      rw [readFields_frame]
      simp only [List.reverse_nil, List.nil_append, String.ofList_toList]
      change readFields (fields ss) [] (s :: acc) = some (acc.reverse ++ s :: ss)
      rw [ih]
      simp [List.reverse_cons, List.append_assoc]

-- Decimal reader and proof pattern from LWS/Snapshot.lean, kept here to avoid
-- coupling the OWL library to the storage host's snapshot implementation.
def decAcc : List Char → Nat → Option Nat
  | [], acc => some acc
  | c :: cs, acc => if c.isDigit then decAcc cs (acc * 10 + (c.toNat - 48)) else none

def decimal? (s : String) : Option Nat :=
  if s.toList.isEmpty then none else decAcc s.toList 0

theorem decAcc_append (l1 l2 : List Char) (acc : Nat) :
    decAcc (l1 ++ l2) acc = (decAcc l1 acc).bind (decAcc l2) := by
  induction l1 generalizing acc with
  | nil => simp [decAcc]
  | cons c cs ih =>
      simp only [List.cons_append, decAcc]
      split <;> simp [ih]

theorem decAcc_repr (n : Nat) :
    ∀ acc, decAcc n.repr.toList acc = some (acc * 10 ^ n.repr.length + n) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro acc
    by_cases h : n < 10
    · rw [Nat.repr_of_lt h]
      have hd : (Nat.digitChar n).isDigit = true := by simp [Nat.isDigit_digitChar, h]
      simp [decAcc, hd, Nat.toNat_digitChar_sub_48_of_lt_ten h]
    · have h10 : 10 ≤ n := by omega
      have hm : n % 10 < 10 := Nat.mod_lt _ (by decide)
      have h1 : (n % 10).repr.length = 1 := by
        rw [Nat.repr_of_lt hm]; simp
      rw [Nat.repr_eq_repr_append_repr h10, String.toList_append, decAcc_append,
        ih (n / 10) (by omega) acc, Option.bind_some, ih (n % 10) (by omega),
        String.length_append, h1]
      congr 1
      have hdm := Nat.div_add_mod n 10
      rw [Nat.pow_one, Nat.pow_succ, Nat.add_mul, Nat.mul_assoc]
      omega

theorem decimal_repr (n : Nat) : decimal? n.repr = some n := by
  have hne : n.repr.toList.isEmpty = false := by
    cases h : n.repr.toList with
    | nil => exact absurd (String.toList_eq_nil_iff.mp h) Nat.repr_ne_empty
    | cons _ _ => rfl
  simp only [decimal?, hne]
  rw [decAcc_repr]; simp

def nameFields : Name → List String
  | .source s => ["source", s]
  | .nominal ms => "nominal" :: ms
  | .dataMin n p => ["dataMin", n.repr, p]
  | .dataMax n p => ["dataMax", n.repr, p]

def fromFields : List String → Option Name
  | ["source", s] => some (.source s)
  | "nominal" :: ms => some (.nominal ms)
  | ["dataMin", n, p] => (decimal? n).map (fun k => .dataMin k p)
  | ["dataMax", n, p] => (decimal? n).map (fun k => .dataMax k p)
  | _ => none

def encode (n : Name) : String := String.ofList (fields (nameFields n))

def decode (s : String) : Option Name :=
  (readFields s.toList [] []).bind fromFields

theorem decode_encode (n : Name) : decode (encode n) = some n := by
  simp only [decode, encode, String.toList_ofList, readFields_fields,
    List.reverse_nil, List.nil_append, Option.bind_some]
  cases n <;> simp [nameFields, fromFields, decimal_repr]

theorem encode_injective {a b : Name} (h : encode a = encode b) : a = b := by
  have hd := congrArg decode h
  simpa only [decode_encode, Option.some.injEq] using hd

theorem encode_eq_iff (a b : Name) : encode a = encode b ↔ a = b :=
  ⟨encode_injective, fun h => congrArg encode h⟩

theorem source_ne_nominal (s : String) (ms : List String) :
    encode (.source s) ≠ encode (.nominal ms) := by
  intro h
  cases encode_injective h

theorem source_ne_dataMin (s p : String) (n : Nat) :
    encode (.source s) ≠ encode (.dataMin n p) := by
  intro h
  cases encode_injective h

theorem source_ne_dataMax (s p : String) (n : Nat) :
    encode (.source s) ≠ encode (.dataMax n p) := by
  intro h
  cases encode_injective h

-- Delimiters, empty list entries and old generated-looking URNs are data.
#guard decode (encode (.nominal ["", "a b", "a", "b", ";+:", "λ"])) ==
  some (.nominal ["", "a b", "a", "b", ";+:", "λ"])
#guard encode (.nominal ["a b"]) != encode (.nominal ["a", "b"])
#guard decode (encode (.dataMin 12345678901234567890 "urn:p:;+:x")) ==
  some (.dataMin 12345678901234567890 "urn:p:;+:x")
#guard decode (encode (.dataMax 0 "")) == some (.dataMax 0 "")
#guard decode (encode (.source (String.ofList (List.replicate 100000 'x')))) ==
  some (.source (String.ofList (List.replicate 100000 'x')))

/-- info: 'L4Factoidal.OWL.CertNames.decode_encode' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in #print axioms decode_encode

end L4Factoidal.OWL.CertNames
