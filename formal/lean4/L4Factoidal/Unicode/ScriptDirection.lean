import L4Factoidal.Unicode.ScriptData

/-!
# The horizontal direction of a script

HarfBuzz `hb_script_get_horizontal_direction` (15.0.0): the scripts written
right to left, by ISO 15924 code. Old Hungarian, Old Italic, Runic and Tifinagh
are written either way; HarfBuzz gives them no direction, and its guess for
text in them is left to right, as here.

`guessRtl` is HarfBuzz's guess for a run (`hb_buffer_guess_segment_properties`):
the script of the first character whose Script is not Common, Inherited or
Unknown, and that script's direction. Layout uses it to know which way the
shaper will take a word when no direction is given
(https://github.com/danbri/factoidal/issues/1275).
-/
namespace L4Factoidal.Unicode.ScriptDirection

def rtlScripts : List String :=
  ["Arab", "Hebr", "Syrc", "Thaa", "Cprt", "Khar", "Phnx", "Nkoo", "Lydi", "Avst", "Armi",
   "Phli", "Prti", "Sarb", "Orkh", "Samr", "Mand", "Merc", "Mero", "Mani", "Mend", "Nbat",
   "Narb", "Palm", "Phlp", "Hatr", "Adlm", "Rohg", "Sogo", "Sogd", "Elym", "Chrs", "Yezi",
   "Ougr", "Gara", "Sidt"]

/-- The script (ISO 15924) is written right to left. -/
def isRtl (iso : String) : Bool := rtlScripts.contains iso

/-- The script of `text` as HarfBuzz guesses it: the first that is not Common,
Inherited or Unknown. -/
def textScript (text : String) : Option String :=
  (text.toList.map fun c => ScriptData.scriptOf c.toNat).find?
    fun s => s != "Zyyy" && s != "Zinh" && s != "Zzzz"

/-- HarfBuzz's guessed direction of `text` is right to left. -/
def guessRtl (text : String) : Bool := (textScript text).any isRtl

#guard guessRtl "שלום"
#guard guessRtl "١٢٣"
#guard !guessRtl "abc"
#guard !guessRtl "123."

end L4Factoidal.Unicode.ScriptDirection
