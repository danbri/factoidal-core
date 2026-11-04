import L4Factoidal.Tdb2.Format
import Std.Data.TreeMap.Lemmas

/-! Bit-keyed memoization of the existing exact SVG decimal formatter.
The cache stores only javaDoubleString(bits), so the proof requires no
axiom connecting Float equality with bit equality and changes no rounding. -/
namespace L4Factoidal.Rendering.FloatFormat

def format (x : Float) : String :=
  let integer := x.toInt64.toInt
  if Float.ofInt integer == x then toString integer
  else Tdb2.javaDoubleString x.toBits

abbrev Cache := Std.TreeMap UInt64 String
def Valid (cache : Cache) : Prop :=
  ∀ key value, cache.get? key = some value → value = Tdb2.javaDoubleString key

theorem valid_empty : Valid ({} : Cache) := by
  intro key value h
  simp at h

theorem Valid.insert (cache : Cache) (h : Valid cache) (key : UInt64) :
    Valid (cache.insert key (Tdb2.javaDoubleString key)) := by
  intro k value found
  simp only [Std.TreeMap.get?_eq_getElem?, Std.TreeMap.getElem?_insert] at found
  split at found
  next same =>
    have eqKey : key = k := Std.LawfulEqOrd.eq_of_compare same
    subst k
    exact (Option.some.inj found).symm
  next _ => exact h k value found

def step (cache : Cache) (x : Float) : String × Cache :=
  let integer := x.toInt64.toInt
  if Float.ofInt integer == x then (toString integer,cache)
  else match cache.get? x.toBits with
    | some text => (text,cache)
    | none =>
      let text := Tdb2.javaDoubleString x.toBits
      (text,cache.insert x.toBits text)

theorem step_correct (cache : Cache) (x : Float) (h : Valid cache) :
    (step cache x).1 = format x ∧ Valid (step cache x).2 := by
  by_cases integral : (Float.ofInt x.toInt64.toInt == x) = true
  · simpa [step,format,integral] using (And.intro (rfl : toString x.toInt64.toInt = toString x.toInt64.toInt) h)
  · cases found : cache.get? x.toBits with
    | some text =>
      simp only [Std.TreeMap.get?_eq_getElem?] at found
      simpa [step,format,integral,found] using And.intro (h x.toBits text found) h
    | none =>
      simp only [Std.TreeMap.get?_eq_getElem?] at found
      simpa [step,format,integral,found] using
        And.intro (rfl : Tdb2.javaDoubleString x.toBits = Tdb2.javaDoubleString x.toBits)
          (Valid.insert cache h x.toBits)

def loop : List Float → Cache → List String → List String × Cache
  | [],cache,acc => (acc.reverse,cache)
  | x::rest,cache,acc =>
    let (text,next) := step cache x
    loop rest next (text::acc)

theorem loop_correct (xs : List Float) : ∀ cache acc, Valid cache →
    (loop xs cache acc).1 = acc.reverse ++ xs.map format ∧
    Valid (loop xs cache acc).2 := by
  induction xs with
  | nil => intro cache acc h; exact ⟨by simp [loop],h⟩
  | cons x rest ih =>
    intro cache acc h
    cases pair : step cache x with
    | mk text next =>
      have correct := step_correct cache x h
      rw [pair] at correct
      have textEq : text = format x := correct.1
      subst text
      have tail := ih next (format x::acc) correct.2
      constructor
      · simpa [loop,pair,List.reverse_cons,List.append_assoc] using tail.1
      · simpa [loop,pair] using tail.2

def formatList (xs : List Float) : List String := (loop xs {} []).1

theorem formatList_eq_map (xs : List Float) : formatList xs = xs.map format := by
  simpa [formatList] using (loop_correct xs {} [] valid_empty).1

#guard formatList [0,1,-1,0.1,0.1,0.5,0.1] == [0,1,-1,0.1,0.1,0.5,0.1].map format
#guard formatList [] == []
#print axioms formatList_eq_map
end L4Factoidal.Rendering.FloatFormat
