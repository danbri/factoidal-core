/-
L4Factoidal.XPath4.NumberWords — the words of numbers, and the names of
months and days, in German, French and Italian, for `fn:format-integer`
(F&O 4.0 §5.4, the `w`, `W` and `Ww` tokens) and `fn:format-date`,
`fn:format-dateTime` (§9.8.4, the `N`, `n` and `Nn` presentations).

The spellings follow the CLDR spell-out rules for these languages
(`%spellout-cardinal` and `%spellout-ordinal`): German writes a number
below one million as one word (`einundzwanzig`, `zweihunderteins`);
French uses the 1990 spelling with hyphens between all parts
(`deux-cent-vingt-et-un`); Italian joins the parts and elides the vowel
before `uno` and `otto` (`ventuno`, `ventotto`).

An ordinal word is a stem and an ending (`erst` + `e`, `quint` + `o`),
so that the variant in the format modifier (`o(-er)`, `o(-a)`) can
replace the ending (F&O 4.0 §5.4.2: the string in parentheses selects a
variant, for example a gender or a grammatical case).

Numbers of one billion (10^9) or more have no words here: the caller
writes them in digits.
-/

namespace L4Factoidal.XPath4.NumberWords

/-! ## German -/

def deOnes : List String := ["null", "eins", "zwei", "drei", "vier", "fünf", "sechs", "sieben", "acht",
  "neun", "zehn", "elf", "zwölf", "dreizehn", "vierzehn", "fünfzehn", "sechzehn", "siebzehn",
  "achtzehn", "neunzehn"]
def deTens : List String := ["", "", "zwanzig", "dreißig", "vierzig", "fünfzig", "sechzig", "siebzig",
  "achtzig", "neunzig"]

/-- A German number below 100 as a part of a compound (`ein`, not `eins`). -/
def de100 (n : Nat) (final : Bool) : String :=
  if n == 1 then (if final then "eins" else "ein")
  else if n < 20 then deOnes.getD n ""
  else
    let o := n % 10
    (if o == 0 then "" else (if o == 1 then "ein" else deOnes.getD o "") ++ "und") ++ deTens.getD (n / 10) ""

/-- A German number below 1000. -/
def de1000 (n : Nat) (final : Bool) : String :=
  if n < 100 then de100 n final
  else
    (if n / 100 == 1 then "ein" else deOnes.getD (n / 100) "") ++ "hundert" ++
      (if n % 100 == 0 then "" else de100 (n % 100) final)

/-- German cardinal words, below 10^9. -/
def deCard (n : Nat) : String :=
  if n == 0 then "null" else
  let m := n / 1000000
  let t := (n / 1000) % 1000
  let r := n % 1000
  let mil := if m == 0 then "" else if m == 1 then "eine Million" else de1000 m false ++ " Millionen"
  let low := (if t == 0 then "" else de1000 t false ++ "tausend") ++ (if r == 0 then "" else de1000 r true)
  if mil == "" then low else if low == "" then mil else mil ++ " " ++ low

/-- The stem of a German ordinal below 20 (the ending is `e`). -/
def deOrdSmall (n : Nat) : String :=
  match n with
  | 1 => "erst" | 3 => "dritt" | 7 => "siebt" | 8 => "acht"
  | _ => deOnes.getD n "" ++ "t"

/-- German ordinal: (stem, default ending). -/
def deOrd (n : Nat) : String × String :=
  let r := n % 100
  if n ≥ 1 && n < 20 then (deOrdSmall n, "e")
  else if n > 100 && r ≥ 1 && r < 20 && n < 1000000 then
    -- `hunderterste`, `tausendzweite`: the last part is the ordinal
    let c := deCard (n - r)
    (c ++ deOrdSmall r, "e")
  else (deCard n ++ "st", "e")

/-! ## French -/

def frOnes : List String := ["zéro", "un", "deux", "trois", "quatre", "cinq", "six", "sept", "huit",
  "neuf", "dix", "onze", "douze", "treize", "quatorze", "quinze", "seize", "dix-sept", "dix-huit",
  "dix-neuf"]
def frTens : List String := ["", "", "vingt", "trente", "quarante", "cinquante", "soixante"]

/-- A French number below 100; `final`: the last part of the number
    (`quatre-vingts` takes an `s` only there). -/
def fr100 (n : Nat) (final : Bool) : String :=
  if n < 20 then frOnes.getD n ""
  else if n < 70 then
    let o := n % 10
    frTens.getD (n / 10) "" ++ (if o == 0 then "" else if o == 1 then "-et-un" else "-" ++ frOnes.getD o "")
  else if n < 80 then
    "soixante" ++ (if n == 71 then "-et-onze" else "-" ++ frOnes.getD (n - 60) "")
  else if n == 80 then (if final then "quatre-vingts" else "quatre-vingt")
  else "quatre-vingt-" ++ frOnes.getD (n - 80) ""

/-- A French number below 1000. -/
def fr1000 (n : Nat) (final : Bool) : String :=
  if n < 100 then fr100 n final
  else
    let h := n / 100
    let r := n % 100
    let cent := if h == 1 then "cent" else frOnes.getD h "" ++ (if r == 0 && final then "-cents" else "-cent")
    cent ++ (if r == 0 then "" else "-" ++ fr100 r final)

/-- French cardinal words, below 10^9. -/
def frCard (n : Nat) : String :=
  if n == 0 then "zéro" else
  let m := n / 1000000
  let t := (n / 1000) % 1000
  let r := n % 1000
  let parts : List String :=
    (if m == 0 then [] else [(if m == 1 then "un" else fr1000 m false) ++ (if m == 1 then "-million" else "-millions")]) ++
    (if t == 0 then [] else [if t == 1 then "mille" else fr1000 t false ++ "-mille"]) ++
    (if r == 0 then [] else [fr1000 r true])
  String.intercalate "-" parts

/-- French ordinal: (stem, default ending). `premier` for 1. -/
def frOrd (n : Nat) : String × String :=
  if n == 1 then ("premi", "er") else
  let c := frCard n
  let c := if c.endsWith "cinq" then c ++ "u"
    else if c.endsWith "neuf" then (c.dropEnd 1).toString ++ "v"
    else if c.endsWith "s" && (c.endsWith "vingts" || c.endsWith "cents") then (c.dropEnd 1).toString
    else if c.endsWith "e" then (c.dropEnd 1).toString
    else c
  (c, "ième")

/-! ## Italian -/

def itOnes : List String := ["zero", "uno", "due", "tre", "quattro", "cinque", "sei", "sette", "otto",
  "nove", "dieci", "undici", "dodici", "tredici", "quattordici", "quindici", "sedici", "diciassette",
  "diciotto", "diciannove"]
def itTens : List String := ["", "", "venti", "trenta", "quaranta", "cinquanta", "sessanta", "settanta",
  "ottanta", "novanta"]

/-- An Italian number below 100. -/
def it100 (n : Nat) (final : Bool) : String :=
  if n < 20 then itOnes.getD n ""
  else
    let t := itTens.getD (n / 10) ""
    let o := n % 10
    if o == 0 then t
    else if o == 1 || o == 8 then (t.dropEnd 1).toString ++ itOnes.getD o ""
    else if o == 3 && final then t ++ "tré"
    else t ++ itOnes.getD o ""

/-- An Italian number below 1000. -/
def it1000 (n : Nat) (final : Bool) : String :=
  if n < 100 then it100 n final
  else
    let h := n / 100
    (if h == 1 then "" else itOnes.getD h "") ++ "cento" ++ (if n % 100 == 0 then "" else it100 (n % 100) final)

/-- Italian cardinal words, below 10^9. -/
def itCard (n : Nat) : String :=
  if n == 0 then "zero" else
  let m := n / 1000000
  let t := (n / 1000) % 1000
  let r := n % 1000
  let mil := if m == 0 then "" else if m == 1 then "un milione" else it1000 m false ++ " milioni"
  let low := (if t == 0 then "" else if t == 1 then "mille" else it1000 t false ++ "mila") ++
    (if r == 0 then "" else it1000 r true)
  if mil == "" then low else if low == "" then mil else mil ++ " " ++ low

/-- Italian ordinal: (stem, default ending `o`; the feminine ending is `a`). -/
def itOrd (n : Nat) : String × String :=
  match n with
  | 1 => ("prim", "o") | 2 => ("second", "o") | 3 => ("terz", "o") | 4 => ("quart", "o")
  | 5 => ("quint", "o") | 6 => ("sest", "o") | 7 => ("settim", "o") | 8 => ("ottav", "o")
  | 9 => ("non", "o") | 10 => ("decim", "o")
  | _ =>
    let c := itCard n
    let c := if c.endsWith "tré" then (c.dropEnd 1).toString ++ "e"
      else if c.endsWith "sei" then c
      else (c.dropEnd 1).toString
    (c ++ "esim", "o")

/-! ## Dispatch -/

/-- The language part of a tag (`de-CH` gives `de`). -/
def langBase (l : String) : String := ((l.toLower.splitOn "-").headD "").trim

/-- The languages that this module has. -/
def hasLang (l : String) : Bool := ["de", "fr", "it"].contains (langBase l)

/-- Cardinal words in a language of this module; `none` for another
    language or a number of 10^9 or more. -/
def card? (lang : String) (n : Nat) : Option String :=
  if n ≥ 1000000000 then none else
  match langBase lang with
  | "de" => some (deCard n)
  | "fr" => some (frCard n)
  | "it" => some (itCard n)
  | _ => none

/-- Ordinal words; `variant` is the text in the parentheses of the
    format modifier. A variant that starts with `-` replaces the default
    ending; another variant is ignored. -/
def ord? (lang : String) (n : Nat) (variant : Option String) : Option String :=
  if n ≥ 1000000000 || n == 0 then none else
  let se : Option (String × String) := match langBase lang with
    | "de" => some (deOrd n)
    | "fr" => some (frOrd n)
    | "it" => some (itOrd n)
    | _ => none
  se.map fun (stem, ending) =>
    match variant with
    | some v => if v.startsWith "-" then stem ++ (v.drop 1).toString else stem ++ ending
    | none => stem ++ ending

def deMonths : List String := ["Januar", "Februar", "März", "April", "Mai", "Juni", "Juli", "August",
  "September", "Oktober", "November", "Dezember"]
def deDays : List String := ["Montag", "Dienstag", "Mittwoch", "Donnerstag", "Freitag", "Samstag", "Sonntag"]
def frMonths : List String := ["janvier", "février", "mars", "avril", "mai", "juin", "juillet", "août",
  "septembre", "octobre", "novembre", "décembre"]
def frDays : List String := ["lundi", "mardi", "mercredi", "jeudi", "vendredi", "samedi", "dimanche"]
def itMonths : List String := ["gennaio", "febbraio", "marzo", "aprile", "maggio", "giugno", "luglio",
  "agosto", "settembre", "ottobre", "novembre", "dicembre"]
def itDays : List String := ["lunedì", "martedì", "mercoledì", "giovedì", "venerdì", "sabato", "domenica"]

/-- Month names (1 to 12) in a language of this module. -/
def months? (lang : String) : Option (List String) :=
  match langBase lang with
  | "de" => some deMonths | "fr" => some frMonths | "it" => some itMonths | _ => none

/-- Day names (Monday first) in a language of this module. -/
def days? (lang : String) : Option (List String) :=
  match langBase lang with
  | "de" => some deDays | "fr" => some frDays | "it" => some itDays | _ => none

#guard card? "de" 21 = some "einundzwanzig"
#guard card? "de" 1 = some "eins"
#guard card? "de" 101 = some "einhunderteins"
#guard card? "de" 2000 = some "zweitausend"
#guard ord? "de" 1 (some "-er") = some "erster"
#guard ord? "de" 20 none = some "zwanzigste"
#guard ord? "de" 3 none = some "dritte"
#guard card? "fr" 80 = some "quatre-vingts"
#guard card? "fr" 81 = some "quatre-vingt-un"
#guard card? "fr" 71 = some "soixante-et-onze"
#guard card? "fr" 200 = some "deux-cents"
#guard card? "fr" 221 = some "deux-cent-vingt-et-un"
#guard ord? "fr" 2 none = some "deuxième"
#guard ord? "fr" 5 none = some "cinquième"
#guard ord? "fr" 9 none = some "neuvième"
#guard ord? "fr" 80 none = some "quatre-vingtième"
#guard ord? "fr" 1 none = some "premier"
#guard card? "it" 21 = some "ventuno"
#guard card? "it" 23 = some "ventitré"
#guard card? "it" 28 = some "ventotto"
#guard card? "it" 2000 = some "duemila"
#guard ord? "it" 5 (some "-a") = some "quinta"
#guard ord? "it" 5 (some "-o") = some "quinto"
#guard ord? "it" 11 none = some "undicesimo"
#guard ord? "it" 23 none = some "ventitreesimo"
#guard ord? "it" 26 none = some "ventiseiesimo"
#guard ord? "it" 20 none = some "ventesimo"

end L4Factoidal.XPath4.NumberWords
