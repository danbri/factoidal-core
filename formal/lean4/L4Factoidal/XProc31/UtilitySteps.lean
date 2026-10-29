import L4Factoidal.XProc31.Atomic
import L4Factoidal.Codec.Crc32
import L4Factoidal.Crypto.MD5
import L4Factoidal.Crypto.SHA1
import L4Factoidal.Crypto.SHA2

namespace L4Factoidal.XProc31
open XML

def supportsUtility (name : String) : Bool := ["hash", "uuid"].contains name

/-- Delegate digest arithmetic to the existing shared implementations. -/
def utilityDigest (algorithm version value : String) : Result String :=
  match algorithm, version with
  | "crc", "" | "crc", "32" =>
    let digest := Codec.crc32 value.toUTF8
    let bytes := [24,16,8,0].map (fun n => UInt8.ofNat ((digest >>> UInt32.ofNat n).toNat % 256))
    pure (Crypto.bytesToHex ⟨bytes.toArray⟩)
  | "md", "" | "md", "5" => pure (Crypto.md5Hex value)
  | "sha", "" | "sha", "1" => pure (Crypto.sha1Hex value)
  | "sha", "256" => pure (Crypto.sha256Hex value)
  | "sha", "384" => pure (Crypto.sha384Hex value)
  | "sha", "512" => pure (Crypto.sha512Hex value)
  | _, _ => error "XC0036" "unsupported hash algorithm or version"

/-- Replace matched nodes with text, except attributes whose name is preserved.
The shared XSLT pattern implementation determines match semantics. -/
def replaceUtilityMatches (step : Node) (env : XPath4.Env) (source : Document)
    (replacement : String) : Result (List Document) := do
  let pattern ← option step "match" env "/"
  let body := [xsl "choose" [] [
    xsl "when" [⟨"test", "self::attribute()"⟩] [
      xsl "attribute" [⟨"name", "{name()}"⟩, ⟨"namespace", "{namespace-uri()}"⟩] [.text replacement]],
    xsl "otherwise" [] [xsl "text" [] [.text replacement]]]]
  let results ← runSheet (editSheet step pattern body) source
  pure (results.map (fun d =>
    if d.contentType == "text/plain" then d else {d with contentType := source.contentType}))

/-- UUID version 4: 122 random bits plus the version and variant fields. -/
def randomUuid4 : IO String := do
  let mut bytes : Array UInt8 := #[]
  for _ in [:16] do
    bytes := bytes.push (UInt8.ofNat (← IO.rand 0 255))
  bytes := bytes.set! 6 ((bytes[6]! &&& 15) ||| 64)
  bytes := bytes.set! 8 ((bytes[8]! &&& 63) ||| 128)
  let hex := Crypto.bytesToHex ⟨bytes⟩
  pure ((hex.take 8).toString ++ "-" ++ (hex.drop 8 |>.take 4).toString ++ "-" ++
    (hex.drop 12 |>.take 4).toString ++ "-" ++ (hex.drop 16 |>.take 4).toString ++ "-" ++ (hex.drop 20).toString)

def utilityStep (step : Node) (ports : List (String × List Document))
    (env : XPath4.Env) : IO (Result (List Document)) := do
  let parsed := do
    let source ← oneSource ((ports.lookup "source").getD [])
    let version ← option step "version" env
    if tag step == "hash" then
      let algorithm ← option step "algorithm" env
      let value ← option step "value" env
      let digest ← utilityDigest algorithm version value
      pure (source, some digest)
    else if tag step == "uuid" then
      if version != "" && version != "4" then error "XC0060" "unsupported UUID version" else pure (source, none)
    else unsupported ("utility step " ++ tag step)
  match parsed with
  | .error e => return .error e
  | .ok (source,value) =>
    let value ← match value with | some value => pure value | none => randomUuid4
    return replaceUtilityMatches step env source value

#guard (utilityDigest "crc" "32" "123456789").toOption == some "cbf43926"
#guard (utilityDigest "md" "5" "abc").toOption == some "900150983cd24fb0d6963f7d28e17f72"
#guard (utilityDigest "sha" "256" "abc").toOption == some "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad"
#guard (replaceUtilityMatches (.element "p:hash" [⟨"match", "doc/@hash | doc/comment()"⟩] []) {}
  {node := .element "doc" [⟨"hash", "old"⟩] [.comment "old"]} "replacement").toOption.map
  (fun docs => docs.map (fun d => (attr d.node "hash",d.node.textContent))) == some [("replacement","replacement")]

/-- Check the generated version and variant fields against RFC UUID syntax. -/
def utilityStepsRegression : IO Bool := do
  let a ← randomUuid4
  let b ← randomUuid4
  let shape := fun value =>
    (evalBool "matches($uuid,'^[0-9a-f]{8}-[0-9a-f]{4}-4[0-9a-f]{3}-[89ab][0-9a-f]{3}-[0-9a-f]{12}$')"
      {vars := [(⟨"","uuid",""⟩, XPath4.sStr value)]}).toOption == some true
  pure (shape a && shape b && a != b)

end L4Factoidal.XProc31
