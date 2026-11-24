import L4Factoidal.RDF.LangTag
-- https://gitlab.wikimedia.org/repos/wikidata-platform/wikidata-query-rewriter/-/blob/e13dcdb96d65bb97a28095cac19a6f0c6f9c9f74/java-rewriter/src/main/java/io/github/andreawesterinen/wikidata/rewriter/rules/LabelLanguagePriority.java


/-! Language priority corresponds to Wikimedia's upstream helper:
Factoidal resolves the UI placeholder before deduplicating.
-/
namespace L4Factoidal.Wikidata
open L4Factoidal.RDF

/-- Accept an explicit BCP 47 tag or a locale such as en_GB.UTF-8.
Keep an explicitly supplied region. Empty, C/POSIX and invalid values use en. -/
def autoLanguage (language : String := "") : String :=
  if language.isEmpty then "en" else
  let stem := (((language.trimAscii.toString.splitOn ".").headD "").splitOn "@").headD ""
  let tag := (stem.replace "_" "-").toLower
  if tag == "c" || tag == "posix" || !isWellFormedLangTag tag then "en" else tag

def languagePriority (language : String) (values : List String) : List String :=
  ((values.flatMap (·.splitOn ",")).map (fun token =>
    let trimmed := token.trimAscii.toString
    if trimmed == "[AUTO_LANGUAGE]" then autoLanguage language else trimmed.toLower)
    |>.filter (!·.isEmpty)).eraseDups

def labelLanguages (languages : List String) : List String :=
  if languages.contains "mul" then languages else languages ++ ["mul"]

def descriptionLanguages (languages : List String) : List String :=
  languages.filter (· != "mul")

theorem defaultAutoLanguage : autoLanguage "" = "en" := by rfl

#guard autoLanguage "en_GB.UTF-8" == "en-gb"
#guard autoLanguage "C.UTF-8" == "en"
#guard languagePriority "" ["[AUTO_LANGUAGE],en,MUL"] == ["en", "mul"]
#guard languagePriority "fr-CA" ["[AUTO_LANGUAGE],FR,fr-ca"] == ["fr-ca", "fr"]

end L4Factoidal.Wikidata
